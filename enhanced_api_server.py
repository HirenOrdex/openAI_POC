import http.server
import json
import xmlrpc.client
import jwt
from datetime import datetime, timedelta
import configparser
import logging
from logging.handlers import RotatingFileHandler
import hashlib
import secrets
import requests
import time
import os
import re
import threading
from functools import lru_cache

# --- Load Configuration ---
config = configparser.ConfigParser()
config_path = os.path.join(os.path.dirname(os.path.dirname(__file__)), 'config', 'config.ini')
config.read(config_path)

ODOO_URL = config.get('odoo', 'url')
ODOO_DB = config.get('odoo', 'db') 
ODOO_USER = config.get('odoo', 'user')
ODOO_PASSWORD = config.get('odoo', 'password')
JWT_SECRET = config.get('api', 'jwt_secret')
SMS_API_KEY = config.get('sms', 'sms_bearer_token')

# --- Performance Optimizations ---
# Connection pooling
odoo_connections = {}
connection_lock = threading.RLock()
last_cleanup = time.time()

# Simple in-memory cache with TTL
cache_data = {}
cache_timestamps = {}
CACHE_TTL = 300  # 5 minutes

# Reduce logging for performance (keep original level but optimize calls)
original_log_level = config.get('logging', 'level', fallback='INFO').upper()

# --- Logging Setup ---
log_file = config.get('logging', 'file', fallback='api_server.log')
if not log_file.startswith('/'):
    log_file = os.path.join(os.path.dirname(os.path.dirname(__file__)), log_file)
log_level = config.get('logging', 'level', fallback='INFO').upper()
max_size_str = config.get('logging', 'max_size', fallback='10')
max_size_mb = int(max_size_str.replace('MB', '').strip()) if 'MB' in max_size_str else int(max_size_str)
backup_count = config.getint('logging', 'backup_count', fallback=5)

logger = logging.getLogger(__name__)
logger.setLevel(log_level)
handler = RotatingFileHandler(log_file, maxBytes=max_size_mb * 1024 * 1024, backupCount=backup_count)
formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
handler.setFormatter(formatter)
logger.addHandler(handler)

# odoo 3rd party api for sms 


# --- Performance Helper Functions ---
def get_cached_data(key):
    """Get cached data if still valid"""
    current_time = time.time()
    if key in cache_data and key in cache_timestamps:
        if current_time - cache_timestamps[key] < CACHE_TTL:
            return cache_data[key]
        else:
            # Remove expired cache
            cache_data.pop(key, None)
            cache_timestamps.pop(key, None)
    return None

def set_cached_data(key, data):
    """Set cached data with timestamp"""
    cache_data[key] = data
    cache_timestamps[key] = time.time()

def cleanup_cache():
    """Clean expired cache entries"""
    global last_cleanup
    current_time = time.time()
    if current_time - last_cleanup > 60:  # Cleanup every minute
        expired_keys = []
        for key, timestamp in cache_timestamps.items():
            if current_time - timestamp > CACHE_TTL:
                expired_keys.append(key)
        for key in expired_keys:
            cache_data.pop(key, None)
            cache_timestamps.pop(key, None)
        last_cleanup = current_time

def get_or_create_odoo_connection():
    """Get pooled Odoo connection or create new one"""
    thread_id = threading.current_thread().ident
    current_time = time.time()
    
    with connection_lock:
        # Check if we have a valid connection for this thread
        if thread_id in odoo_connections:
            conn_info = odoo_connections[thread_id]
            # Reuse connection if it's less than 10 minutes old
            if current_time - conn_info['created_at'] < 600:
                return conn_info['uid'], conn_info['models']
        
        # Create new connection
        try:
            common = xmlrpc.client.ServerProxy(f'{ODOO_URL}/xmlrpc/2/common')
            uid = common.authenticate(ODOO_DB, ODOO_USER, ODOO_PASSWORD, {})
            if not uid:
                raise ConnectionRefusedError("Failed to authenticate with Odoo")
            
            models = xmlrpc.client.ServerProxy(f'{ODOO_URL}/xmlrpc/2/object')
            
            odoo_connections[thread_id] = {
                'uid': uid,
                'models': models,
                'created_at': current_time
            }
            
            return uid, models
        except Exception as e:
            logger.error(f"Failed to connect to Odoo: {str(e)}")
            raise

def execute_odoo_kw_optimized(model, method, args=[], kwargs={}, cache_key=None):
    """Execute Odoo method with caching and connection pooling"""
    # Check cache first for read operations
    if cache_key and method in ['search', 'read', 'search_read']:
        cached_result = get_cached_data(cache_key)
        if cached_result is not None:
            return cached_result
    
    try:
        uid, models = get_or_create_odoo_connection()
        result = models.execute_kw(ODOO_DB, uid, ODOO_PASSWORD, model, method, args, kwargs)
        
        # Cache read operations
        if cache_key and method in ['search', 'read', 'search_read']:
            set_cached_data(cache_key, result)
        
        return result
    except Exception as e:
        # Remove failed connection from pool
        thread_id = threading.current_thread().ident
        with connection_lock:
            odoo_connections.pop(thread_id, None)
        logger.error(f"Odoo operation failed: {str(e)}")
        raise

# --- Session Management ---
active_sessions = {}
blacklisted_tokens = set()

# --- Database-Level OTP Management using res.partner ---
OTP_TTL_SECONDS = 300  # 5 minutes
MAX_OTP_ATTEMPTS = 3  # Maximum OTP validation attempts

def _generate_otp(length: int = 6) -> str:
    """Generate cryptographically secure numeric OTP"""
    return ''.join(str(secrets.randbelow(10)) for _ in range(length))

def _sanitize_phone(phone: str) -> str:
    """Sanitize phone number to digits only"""
    if not phone:
        return ''
    # keep digits only
    sanitized = re.sub(r"\D", "", str(phone))
    return sanitized

def _cleanup_expired_otps():
    """Clean up expired OTPs from all res.partner records"""
    try:
        current_time = datetime.utcnow()
        
        # Find users with expired OTPs
        users_with_expired_otps = execute_odoo_kw (
        'res.partner', 'search',
        [[
            ('x_otp_expires_at', '!=', False),
            ('x_otp_expires_at', '<', current_time.isoformat())
        ]]
        )
        
        if users_with_expired_otps:
            # Clear expired OTP data
            execute_odoo_kw('res.partner', 'write', [
                users_with_expired_otps,
                {
                    'x_otp_code': False,
                    'x_otp_expires_at': False,
                    'x_otp_attempts': 0,
                    'x_otp_created_at': False
                }
            ])
            logger.info(f"Cleaned up expired OTPs for {len(users_with_expired_otps)} users")
            
    except Exception as e:
        logger.error(f"Failed to cleanup expired OTPs: {str(e)}")

def _store_otp_in_partner(user_id: int, otp: str) -> bool:
    """Store OTP data directly in res.partner record"""
    try:
        current_time = datetime.utcnow()
        expires_at = current_time + timedelta(seconds=OTP_TTL_SECONDS)
        
        # Update user record with OTP data using custom fields
        otp_data = {
            'x_otp_code': otp,
            'x_otp_created_at': current_time.isoformat(),
            'x_otp_expires_at': expires_at.isoformat(),
            'x_otp_attempts': 0  # Reset attempts when new OTP is generated
        }
        
        execute_odoo_kw('res.partner', 'write', [[user_id], otp_data])
        logger.info(f"OTP stored in user record {user_id}, expires at {expires_at}")
        
        # Clean up expired OTPs from other users periodically
        _cleanup_expired_otps()
        
        return True
        
    except Exception as e:
        logger.error(f"Failed to store OTP in user record {user_id}: {str(e)}")
        return False

def _validate_otp_from_partner(phone_or_email: str, otp: str) -> tuple[bool, int, str]:
    """Validate OTP from res.partner record with attempt tracking"""
    try:
        # Clean expired OTPs first
        _cleanup_expired_otps()
        
        # Find user by phone or email with active OTP
        current_time = datetime.utcnow()
        domain = [
            '&', '&', '&',
            '|', ('phone', '=', phone_or_email), ('email', '=', phone_or_email),
            ('active', '=', True),
            ('x_otp_code', '!=', False),
            ('x_otp_expires_at', '>', current_time.isoformat())
        ]
        
        user_ids = execute_odoo_kw('res.partner', 'search', [domain])
        
        if not user_ids:
            return False, None, 'OTP not found or expired. Please request a new code.'
        
        user_id = user_ids[0]
        
        # Get current OTP data
        user_data = execute_odoo_kw('res.partner', 'read', [
            user_id, 
            ['x_otp_code', 'x_otp_attempts', 'x_otp_expires_at']
        ])[0]
        
        current_attempts = user_data.get('x_otp_attempts', 0)
        
        # Check if max attempts exceeded
        if current_attempts >= MAX_OTP_ATTEMPTS:
            # Clear OTP data to prevent further attempts
            execute_odoo_kw('res.partner', 'write', [[user_id], {
                'x_otp_code': False,
                'x_otp_expires_at': False,
                'x_otp_attempts': 0,
                'x_otp_created_at': False
            }])
            return False, None, f'OTP has exceeded maximum attempts ({MAX_OTP_ATTEMPTS}). Please request a new code.'
        
        # Increment attempt counter
        new_attempts = current_attempts + 1
        execute_odoo_kw('res.partner', 'write', [[user_id], {'x_otp_attempts': new_attempts}])
        
        # Validate OTP code
        stored_otp = user_data.get('x_otp_code', '')
        if str(stored_otp) != str(otp):
            if new_attempts >= MAX_OTP_ATTEMPTS:
                # Clear OTP data if max attempts reached
                execute_odoo_kw('res.partner', 'write', [[user_id], {
                    'x_otp_code': False,
                    'x_otp_expires_at': False,
                    'x_otp_attempts': 0,
                    'x_otp_created_at': False
                }])
                return False, None, f'Invalid OTP. Maximum attempts ({MAX_OTP_ATTEMPTS}) reached. Please request a new code.'
            else:
                remaining_attempts = MAX_OTP_ATTEMPTS - new_attempts
                return False, None, f'Invalid OTP. {remaining_attempts} attempt(s) remaining.'
        
        # OTP is valid - clear OTP data (single-use)
        execute_odoo_kw('res.partner', 'write', [[user_id], {
            'x_otp_code': False,
            'x_otp_expires_at': False,
            'x_otp_attempts': 0,
            'x_otp_created_at': False
        }])
        
        logger.info(f"OTP validated successfully for user: {user_id}")
        return True, user_id, None
        
    except Exception as e:
        logger.error(f"Failed to validate OTP: {str(e)}")
        return False, None, f'OTP validation failed: {str(e)}'

def _get_otp_stats() -> dict:
    """Get OTP statistics from res.partner records"""
    try:
        current_time = datetime.utcnow()
        
        # Count active OTPs
        active_otps = len(execute_odoo_kw('res.partner', 'search', [[
            ('x_otp_code', '!=', False),
            ('x_otp_expires_at', '>', current_time.isoformat())
        ]]))

        expired_otps = len(execute_odoo_kw('res.partner', 'search', [[
            ('x_otp_code', '!=', False),
            ('x_otp_expires_at', '<', current_time.isoformat())
        ]]))

        
        return {
            'active_otps': active_otps,
            'expired_otps_pending_cleanup': expired_otps,
            'otp_ttl_seconds': OTP_TTL_SECONDS,
            'max_attempts': MAX_OTP_ATTEMPTS
        }
        
    except Exception as e:
        logger.error(f"Failed to get OTP stats: {str(e)}")
        return {'error': str(e)}

def _check_otp_fields_exist() -> bool:
    """Check if custom OTP fields exist in res.partner model"""
    try:
        # Try to read OTP fields from any partner record to test if fields exist
        partner_ids = execute_odoo_kw('res.partner', 'search', [[]], {'limit': 1})
        if partner_ids:
            execute_odoo_kw('res.partner', 'read', [
                partner_ids[0], 
                ['x_otp_code', 'x_otp_created_at', 'x_otp_expires_at', 'x_otp_attempts']
            ])
        
        logger.info("OTP fields exist in res.partner model")
        return True
        
    except Exception as e:
        logger.error(f"OTP fields missing in res.partner: {str(e)}")
        logger.error("Please add these custom fields to res.partner model:")
        logger.error("  - x_otp_code (Char)")
        logger.error("  - x_otp_created_at (Datetime)")
        logger.error("  - x_otp_expires_at (Datetime)")
        logger.error("  - x_otp_attempts (Integer)")
        return False

# Main OTP functions with fallback support
def _put_otp(identifier: str, otp: str, user_id: int):
    """Store OTP - tries res.partner fields first, falls back to local storage"""
    if _check_otp_fields_exist():
        success = _store_otp_in_partner(user_id, otp)
        if success:
            return
        logger.warning("Failed to store OTP in res.partner, falling back to local storage")
    
    # Fallback to local storage for development/testing
    logger.warning("Using local OTP storage - add custom fields to res.partner for production!")
    global otp_store, otp_lock
    if 'otp_store' not in globals():
        otp_store = {}
        otp_lock = threading.RLock()
    
    with otp_lock:
        otp_store[identifier] = {
            'otp': otp,
            'user_id': user_id,
            'expires_at': time.time() + OTP_TTL_SECONDS,
        }

def _get_and_validate_otp(identifier: str, otp: str):
    """Validate OTP - tries res.partner fields first, falls back to local storage"""
    logger.info(f"OTP validation: Checking for identifier={identifier}, otp={otp}")
    
    if _check_otp_fields_exist():
        try:
            success, user_id, error = _validate_otp_from_partner(identifier, otp)
            logger.info(f"Database OTP validation: success={success}, user_id={user_id}, error={error}")
            
            # If found in database and valid, return
            if success:
                logger.info("OTP validated successfully from database")
                return True, user_id, None
            
            # If database said not found, try local storage
            if error and ('not found' in error.lower() or 'expired' in error.lower()):
                logger.warning(f"OTP not in database, trying local storage: {error}")
            else:
                # Other errors (invalid OTP, max attempts), return immediately
                return False, user_id, error
                
        except Exception as e:
            logger.error(f"Partner OTP validation exception: {str(e)}, trying local storage")
    
    # Fallback to local storage for development/testing
    logger.warning("Using local OTP validation - checking local storage")
    global otp_store, otp_lock
    if 'otp_store' not in globals():
        logger.error("OTP local storage not initialized")
        return False, None, 'OTP storage not initialized'
    
    logger.info(f"Local OTP store keys: {list(otp_store.keys()) if 'otp_store' in globals() else 'not initialized'}")
    
    with otp_lock:
        entry = otp_store.get(identifier)
        logger.info(f"Local storage lookup for '{identifier}': {entry}")
        
        if not entry:
            logger.warning(f"OTP not found in local storage for identifier: {identifier}")
            return False, None, 'OTP not found. Please request a new code.'
        if time.time() > entry['expires_at']:
            otp_store.pop(identifier, None)
            logger.warning(f"OTP expired in local storage for identifier: {identifier}")
            return False, None, 'OTP expired. Please request a new code.'
        if str(entry['otp']) != str(otp):
            logger.warning(f"OTP mismatch in local storage: expected={entry['otp']}, got={otp}")
            return False, None, 'Invalid OTP'
        # OTP valid, remove it (single-use)
        otp_store.pop(identifier, None)
        logger.info(f"âœ… OTP validated successfully from local storage for user_id={entry['user_id']}")
        return True, entry['user_id'], None

def _get_sms_config():
    """Get SMS configuration from config file"""
    try:
        return {
            'username': config.get('sms', 'username'),
            'bearer_token': config.get('sms', 'bearer_token'),
            'api_url': config.get('sms', 'api_url'),
            'source': config.get('sms', 'source'),
            'max_tries': config.getint('sms', 'max_tries', fallback=3),
            'valid_time': config.getint('sms', 'valid_time', fallback=5)
        }
    except Exception as e:
        logger.error(f"Failed to load SMS config: {e}")
        return None

def _format_phone_for_019sms(phone: str) -> tuple[str, bool]:
    """Format phone number for 019sms API (format: +972545590094)
    Returns (formatted_phone, is_israeli_number)
    """
    if not phone:
        return None, False
    
    # Remove all non-digits first
    clean_phone = re.sub(r'\D', '', str(phone))
    
    # Handle different formats
    if clean_phone.startswith('972'):
        # Already has country code: 972545590094
        formatted = f"+{clean_phone}"
        if len(clean_phone) == 12 and clean_phone[3] == '5':
            return formatted, True
    elif clean_phone.startswith('0'):
        # Israeli format with leading 0: 0545590094 -> +972545590094
        israeli_phone = clean_phone[1:]
        if len(israeli_phone) == 9 and israeli_phone.startswith('5'):
            return f"+972{israeli_phone}", True
    elif len(clean_phone) == 9 and clean_phone.startswith('5'):
        # Clean Israeli format without 0: 545590094 -> +972545590094
        return f"+972{clean_phone}", True
    elif len(clean_phone) >= 10:
        # International number with country code
        if not clean_phone.startswith('+'):
            return f"+{clean_phone}", False
        return clean_phone, False
    
    return None, False

def _send_otp_via_019sms(to_phone: str, otp_code: str) -> tuple[bool, str]:
    """Send OTP using 019SMS API with Bearer token authentication and proper message format.
    Returns (success, error_message).
    """
    sms_config = _get_sms_config()
    if not sms_config:
        return False, "SMS configuration not available"
    
    # Format phone number for 019sms
    formatted_phone, is_israeli = _format_phone_for_019sms(to_phone)
    if not formatted_phone:
        return False, "Invalid phone number format"
    
    # For non-Israeli numbers, return mock success for testing
    if not is_israeli:
        logger.info(f"Mock OTP sent to international number: {to_phone} with code: {otp_code}")
        return True, "Mock SMS sent for international number"
    
    # Prepare the payload according to 019SMS standard format
    # Professional OTP message format
    message = f"Your verification code is: {otp_code}\nValid for {sms_config['valid_time']} minutes.\nDo not share this code."
    
    payload = {
        "sms": {
            "user": {
                "username": sms_config['username']
            },
            "source": sms_config['source'],
            "destinations": {
                "phone": formatted_phone
            },
            "message": message
        }
    }
    
    headers = {
        'Content-Type': 'application/json',
        'Authorization': f"Bearer {sms_config['bearer_token']}"
    }
    
    try:
        logger.info(f"Sending OTP to phone: {formatted_phone} (original: {to_phone})")
        resp = requests.post(sms_config['api_url'], json=payload, headers=headers, timeout=15)
        
        if resp.status_code != 200:
            logger.error(f"019SMS API HTTP error: {resp.status_code} - {resp.text}")
            return False, f"SMS service error: HTTP {resp.status_code}"
        
        try:
            response_data = resp.json()
            logger.info(f"019SMS API response: {response_data}")
            
            # Check for success - 019SMS returns numeric status codes
            # Status 200 or string 'success' = success
            # Any other status code or error message = failure
            status = response_data.get('status')
            message = response_data.get('message', '')
            
            # Check if it's a success response
            # 019SMS returns status 0 or 200 for success
            if status == 0 or status == 200 or status == 'success' or response_data.get('success') == True:
                logger.info(f"✅ OTP sent successfully to {formatted_phone} (shipment_id: {response_data.get('shipment_id', 'N/A')})")
                return True, ''
            
            # Check for error status codes (but not 0 which is success)
            if isinstance(status, int) and status != 0 and status != 200:
                error_msg = f"{message} (status: {status})" if message else f"SMS service error (status: {status})"
                logger.error(f"❌ 019SMS API error: {error_msg}")
                return False, error_msg
            
            # Check for error in message or explicit error field
            if 'error' in str(response_data).lower() or response_data.get('error'):
                error_msg = response_data.get('message') or response_data.get('error') or 'Unknown SMS service error'
                logger.error(f"❌ 019SMS API error: {error_msg}")
                return False, f"SMS service error: {error_msg}"
            
            # If we get here, uncertain status - treat as error for safety
            logger.warning(f"⚠️  019SMS API returned unclear status: {response_data}")
            return False, f"SMS service returned unclear response: {message}"
                
        except json.JSONDecodeError:
            logger.error(f"019SMS API invalid JSON response: {resp.text}")
            return False, "SMS service returned invalid response"
            
    except requests.exceptions.RequestException as e:
        logger.error(f"019SMS API request failed: {str(e)}")
        return False, f"SMS service request failed: {str(e)}"
    except Exception as e:
        logger.error(f"019SMS API unexpected error: {str(e)}")
        return False, f"SMS service error: {str(e)}"

def generate_session_id(user_id):
    timestamp = str(int(time.time()))
    data = f"{user_id}{timestamp}{JWT_SECRET}"
    return hashlib.sha256(data.encode()).hexdigest()

def create_session(user_id, user_data, token):
    session_id = generate_session_id(user_id)
    session_data = {
        'user_id': user_id,
        'user_data': user_data,
        'token': token,
        'created_at': datetime.utcnow(),
        'last_activity': datetime.utcnow()
    }
    active_sessions[session_id] = session_data
    logger.info(f"Session created with ID: {session_id} for user: {user_id}")
    return session_id

def validate_token_and_session(token):
    if token in blacklisted_tokens:
        raise jwt.InvalidTokenError("Token has been revoked")
    
    try:
        decoded_token = jwt.decode(token, JWT_SECRET, algorithms=['HS256'])
        for session_id, session_data in active_sessions.items():
            if session_data['token'] == token:
                session_data['last_activity'] = datetime.utcnow()
                break
        return decoded_token
    except jwt.ExpiredSignatureError:
        raise jwt.ExpiredSignatureError("Token has expired")
    except jwt.InvalidTokenError:
        raise jwt.InvalidTokenError("Invalid token")

def invalidate_session(token):
    blacklisted_tokens.add(token)
    for session_id, session_data in list(active_sessions.items()):
        if session_data['token'] == token:
            del active_sessions[session_id]
            logger.info(f"Session {session_id} invalidated")
            break

def cleanup_expired_sessions():
    current_time = datetime.utcnow()
    expired_sessions = []
    
    for session_id, session_data in active_sessions.items():
        if (current_time - session_data['last_activity']).total_seconds() > 10800:
            expired_sessions.append(session_id)
            blacklisted_tokens.add(session_data['token'])
    
    for session_id in expired_sessions:
        del active_sessions[session_id]
        logger.info(f"Expired session {session_id} cleaned up")

# --- XML-RPC Connection ---
def get_odoo_uid():
    common = xmlrpc.client.ServerProxy(f'{ODOO_URL}/xmlrpc/2/common')
    uid = common.authenticate(ODOO_DB, ODOO_USER, ODOO_PASSWORD, {})
    if not uid:
        raise ConnectionRefusedError("Failed to authenticate with Odoo")
    return uid

def execute_odoo_kw(model, method, args=[], kwargs={}):
    uid = get_odoo_uid()
    models = xmlrpc.client.ServerProxy(f'{ODOO_URL}/xmlrpc/2/object')
    return models.execute_kw(ODOO_DB, uid, ODOO_PASSWORD, model, method, args, kwargs)

# --- Utility Functions ---
def strip_html_tags(text):
    """Remove HTML tags from text, specifically for birthday field that might contain <p> tags"""
    if not text:
        return ''
    # Remove HTML tags using regex
    clean = re.sub('<.*?>', '', str(text))
    return clean.strip()

class EnhancedApiHandler(http.server.BaseHTTPRequestHandler):
    def handle_send_invoice_sms(self, data):
        print("[SMS SERVICE] ===============================")
        print("[SMS SERVICE] Request received")

        try:
            order_name = data.get("order_name")
            customer_name = data.get("customer_name", "Anonymous")
            phone_number = data.get("phone_number")
            invoice_url = data.get("invoice_url")

            print(f"[SMS SERVICE] Order: {order_name}")
            print(f"[SMS SERVICE] Customer: {customer_name}")
            print(f"[SMS SERVICE] Phone (raw): {phone_number}")
            print(f"[SMS SERVICE] Invoice URL: {invoice_url}")

            if not phone_number:
                return self._send_response(400, {
                    "success": False,
                    "message": "Phone number missing"
                })

            formatted_phone = (
                phone_number
                if phone_number.startswith("+")
                else f"+972{phone_number[1:]}"
            )

            message = (
                f"✅ SUCCESS! Your order has been completed!\n"
                f"Order: {order_name}\n"
                f"Customer: {customer_name}"
            )

            if invoice_url:
                message += f"\n\n📄 View your invoice (PDF):\n{invoice_url}"

            payload = {
                "sms": {
                    "user": {"username": "eyezon"},
                    "source": "Grocery",
                    "destinations": {"phone": formatted_phone},
                    "message": message
                }
            }

            headers = {
                "Content-Type": "application/json",
                "Authorization": f"Bearer {SMS_API_KEY}"
            }

            response = requests.post(
                "https://019sms.co.il/api",
                json=payload,
                headers=headers,
                timeout=10
            )

            if response.status_code in (200, 201):
                return self._send_response(200, {
                    "success": True,
                    "message": "SMS sent successfully",
                    "response": response.text,
                    "invoice_url": invoice_url
                })

            return self._send_response(500, {
                "success": False,
                "message": "019SMS API error",
                "response": response.text
            })

        except Exception as e:
            return self._send_response(500, {
                "success": False,
                "message": str(e)
            })

    def _send_response(self, data, status=200):
        self.send_response(status)
        self.send_header('Content-type', 'application/json')
        self.send_header('Access-Control-Allow-Origin', '*')
        self.send_header('Access-Control-Allow-Methods', 'GET, POST, PUT, DELETE, OPTIONS')
        self.send_header('Access-Control-Allow-Headers', 'Content-Type, Authorization')
        self.end_headers()
        self.wfile.write(json.dumps(data, indent=2).encode('utf-8'))

    def do_OPTIONS(self):
        self.send_response(200)
        self.send_header('Access-Control-Allow-Origin', '*')
        self.send_header('Access-Control-Allow-Methods', 'GET, POST, PUT, DELETE, OPTIONS')
        self.send_header('Access-Control-Allow-Headers', 'Content-Type, Authorization')
        self.end_headers()
        
    def do_GET(self):
        cleanup_cache()  # Periodic cache cleanup
        if self.path == '/api/v1/health':
            otp_stats = _get_otp_stats()
            otp_fields_exist = _check_otp_fields_exist()
            
            self._send_response({
                'status': 'ok', 
                'message': 'OPTIMIZED Enhanced Store API with Database OTP is running!',
                'database': ODOO_DB,
                'port': config.getint('server', 'port', fallback=8001),
                'performance_info': {
                    'cache_entries': len(cache_data),
                    'active_connections': len(odoo_connections),
                    'active_sessions': len(active_sessions)
                },
                'otp_info': {
                    'storage_type': 'res.partner (database)' if otp_fields_exist else 'local memory (fallback)',
                    'fields_configured': otp_fields_exist,
                    'statistics': otp_stats
                },
                'optimizations': [
                    'Connection pooling enabled',
                    'Response caching (5 min TTL)',
                    'Optimized session management',
                    'Database-level OTP storage',
                    '019SMS integration with dynamic codes',
                    'Compact JSON responses'
                ],
                'new_endpoints': [
                    'GET /api/v1/user/details - Get user details',
                    'POST /api/v1/user/update - Update user details', 
                    'PUT /api/v1/user/{user_id} - Update user by ID',
                    'POST /api/v1/user/logout - Logout user',
                    'GET /api/v1/user/sessions - Get active sessions',
                    'DELETE /api/v1/user/{user_id} - Soft delete user'
                ],
                'database_requirements': {
                    'required_custom_fields': [
                        'x_otp_code (Char) - Stores the OTP code',
                        'x_otp_created_at (Datetime) - OTP creation timestamp',
                        'x_otp_expires_at (Datetime) - OTP expiration timestamp', 
                        'x_otp_attempts (Integer) - Failed attempt counter'
                    ],
                    'target_model': 'res.partner',
                    'fields_exist': otp_fields_exist
                }
            })
        elif self.path == '/api/v1/user/details':
            self.handle_get_user_details()
        elif self.path == '/api/v1/user/sessions':
            self.handle_get_active_sessions()
        elif self.path.startswith('/api/v1/user/list'):
            self.handle_get_user_list()
        elif self.path.startswith('/api/v1/user/') and self.path.count('/') == 4 and self.command == 'GET':
            # GET /api/v1/user/{user_id} - Get user by ID (excluding deleted)
            user_id = self.path.split('/')[-1]
            self.handle_get_user_by_id(user_id)
        else:
            logger.warning(f"404 Not Found for path: {self.path}")
            self._send_response({'error': 'Not Found'}, 404)

    def handle_get_user_list(self):
        """GET /api/v1/user/list?active=true|false - Get user list filtered by active status."""
        try:
            # Parse query string for 'active' parameter
            from urllib.parse import urlparse, parse_qs
            query = urlparse(self.path).query
            params = parse_qs(query)
            active_param = params.get('active', ['true'])[0].lower()
            if active_param == 'false':
                active_value = False
            else:
                active_value = True
            # Search for users with the given active status
            domain = [[('active', '=', active_value)]]
            user_ids = execute_odoo_kw_optimized('res.partner', 'search', domain, cache_key=f"user_list_{active_value}")
            if not user_ids:
                self._send_response({'success': True, 'users': []}, 200)
                return
            users = execute_odoo_kw_optimized('res.partner', 'read', [user_ids, ['id', 'name', 'phone', 'email', 'function', 'vat', 'ref']], cache_key=f"user_list_data_{active_value}")
            user_list = []
            for user in users:
                user_list.append({
                    'id': user['id'],
                    'name': user['name'],
                    'phone': user['phone'],
                    'email': user['email'],
                    'last_name': user.get('function', ''),
                    'birthday': user.get('vat', ''),
                    'identification_id': user.get('ref', '')
                })
            self._send_response({'success': True, 'users': user_list}, 200)
        except Exception as e:
            logger.error(f"Get user list failed: {str(e)}")
            self._send_response({'error': f'Get user list failed: {str(e)}'}, 500)

    def do_POST(self):
        try:
            content_length = int(self.headers['Content-Length'])
            post_data = self.rfile.read(content_length)
            data = json.loads(post_data.decode('utf-8'))
            if self.path == '/api/v1/user/register':
                self.handle_user_register(data)
            elif self.path == '/api/v1/user/login':
                self.handle_user_login(data)
            elif self.path == '/api/v1/user/verify':
                self.handle_user_verify(data)
            elif self.path == '/api/v1/user/update':
                self.handle_user_update(data)
            elif self.path == '/api/v1/user/logout':
                self.handle_user_logout(data)
            elif self.path == '/api/v1/store-visit':
                self.handle_store_visit(data)
            elif self.path.startswith('/api/v1/user/') and len(self.path.split('/')) == 5:
                # Handle /api/v1/user/{user_id} for updating user by ID
                user_id = self.path.split('/')[-1]
                self.handle_update_user_by_id(data, user_id)
            elif self.path == "/api/v1/send-sms":
                self.handle_send_invoice_sms(data)
            else:
                self._send_response({'error': 'Not Found'}, 404)
        except Exception as e:
            logger.error(f"Request processing error: {str(e)}")
            self._send_response({'error': f'Request processing error: {str(e)}'}, 400)

    def do_DELETE(self):
        try:
            if self.path.startswith('/api/v1/user/') and len(self.path.split('/')) == 5:
                user_id = self.path.split('/')[-1]
                self.handle_soft_delete_user(user_id)
            else:
                self._send_response({'error': 'Not Found'}, 404)
        except Exception as e:
            logger.error(f"DELETE request processing error: {str(e)}")
            self._send_response({'error': f'Request processing error: {str(e)}'}, 400)

    def handle_soft_delete_user(self, user_id):
        """DELETE /api/v1/user/{user_id} - Soft delete user by setting active=False."""
        try:
            try:
                user_id = int(user_id)
            except ValueError:
                self._send_response({'error': 'Invalid user ID format'}, 400)
                return
            # Check if user exists and is active
            user_exists = execute_odoo_kw_optimized('res.partner', 'search', [[('id', '=', user_id), ('active', '=', True)]], cache_key=f"user_exists_{user_id}")
            if not user_exists:
                self._send_response({'error': 'User not found or already deleted'}, 404)
                return
            # Soft delete: set active=False
            execute_odoo_kw('res.partner', 'write', [[user_id], {'active': False}])
            # Clear cache for this user
            cache_key = f"user_exists_{user_id}"
            cache_data.pop(cache_key, None)
            cache_timestamps.pop(cache_key, None)
            logger.info(f"User {user_id} soft deleted successfully")
            self._send_response({'success': True, 'message': f'User {user_id} deleted (soft) successfully'}, 200)
        except Exception as e:
            logger.error(f"Soft delete user failed: {str(e)}")
            self._send_response({'error': f'Soft delete user failed: {str(e)}'}, 500)

    def handle_get_user_by_id(self, user_id):
        """GET /api/v1/user/{user_id} - Get user by ID (excluding deleted)."""
        try:
            try:
                user_id = int(user_id)
            except ValueError:
                self._send_response({'error': 'Invalid user ID format'}, 400)
                return
            user_exists = execute_odoo_kw_optimized('res.partner', 'search', [[('id', '=', user_id), ('active', '=', True)]], cache_key=f"user_exists_{user_id}")
            if not user_exists:
                self._send_response({'error': 'User not found or deleted'}, 404)
                return
            user_data = execute_odoo_kw('res.partner', 'read', [user_id, ['name', 'phone', 'email', 'function', 'vat', 'ref']])[0]
            api_user_data = {
                'id': user_data['id'],
                'name': user_data['name'],
                'phone': user_data['phone'],
                'email': user_data['email'],
                'last_name': user_data.get('function', ''),
                'birthday': user_data.get('vat', ''),
                'identification_id': user_data.get('ref', '')
            }
            self._send_response({'success': True, 'data': api_user_data}, 200)
        except Exception as e:
            logger.error(f"Get user by ID failed: {str(e)}")
            self._send_response({'error': f'Get user by ID failed: {str(e)}'}, 500)

    def handle_user_register(self, data):
        try:
            phone = data.get('phone')
            email = data.get('email')
            if phone:
                cache_key = f"user_exists_phone_{phone}"
                existing_users = execute_odoo_kw_optimized('res.partner', 'search', [[('phone', '=', phone), ('active', '=', True)]], cache_key=cache_key)
                if existing_users:
                    self._send_response({'error': 'User with this phone already exists'}, 409)
                    return
            if email:
                cache_key = f"user_exists_email_{email}"
                existing_users = execute_odoo_kw_optimized('res.partner', 'search', [[('email', '=', email), ('active', '=', True)]], cache_key=cache_key)
                if existing_users:
                    self._send_response({'error': 'User with this email already exists'}, 409)
                    return

            user_data = {
                'name': data.get('name', 'Unknown User'),
                'phone': phone,
                'email': email or '',
                'function': data.get('last_name', ''),  # Using function field for last_name
                'vat': data.get('birthday', ''),  # Using vat field for birthday (plain text)
                'ref': data.get('identification_id', ''),  # Using ref field for identification_id
            }
            
            user_id = execute_odoo_kw_optimized('res.partner', 'create', [user_data])
            
            # Map response back to API field names
            api_response_data = {
                'name': data.get('name', 'Unknown User'),
                'phone': phone,
                'email': email or '',
                'last_name': data.get('last_name', ''),
                'birthday': data.get('birthday', ''),
                'identification_id': data.get('identification_id', '')
            }
            
            logger.info(f"Successfully registered new user with ID: {user_id}")
            self._send_response({'success': True, 'message': 'User registered successfully', 'user_id': user_id, 'data': api_response_data}, 201)
            
        except Exception as e:
            logger.error(f"Registration failed: {str(e)}")
            self._send_response({'error': f'Registration failed: {str(e)}'}, 500)

    def handle_user_login(self, data):
        try:
            logger.info("="*60)
            logger.info("NEW LOGIN REQUEST - SEND OTP")
            logger.info(f"Request data: {json.dumps(data, indent=2)}")
            logger.info(f"Request headers: {dict(self.headers)}")
            
            phone_or_email = data.get('phone_or_email')
            if not phone_or_email:
                logger.warning("LOGIN FAILED: Missing phone_or_email")
                self._send_response({'error': 'Phone or email is required'}, 400)
                return

            logger.info(f"Login attempt for: {phone_or_email}")

            # Find user by phone or email
            domain = ['&', '|', ('phone', '=', phone_or_email), ('email', '=', phone_or_email), ('active', '=', True)]
            logger.info(f"Searching user with domain: {domain}")
            user_ids = execute_odoo_kw('res.partner', 'search', [domain])
            logger.info(f"User search result: {user_ids}")
            
            if not user_ids:
                logger.warning(f"LOGIN FAILED: User not found for {phone_or_email}")
                self._send_response({'error': 'User not found'}, 404)
                return

            user_id = user_ids[0]
            logger.info(f"User found: ID={user_id}")
            
            # Fetch phone to send OTP
            user = execute_odoo_kw('res.partner', 'read', [user_id, ['phone', 'name', 'email']])[0]
            logger.info(f"User details: name={user.get('name')}, phone={user.get('phone')}, email={user.get('email')}")
            
            phone_value = user.get('phone') or (phone_or_email if '@' not in str(phone_or_email) else None)
            logger.info(f"Phone value for OTP: {phone_value}")
            
            sanitized = _sanitize_phone(phone_value)
            logger.info(f"Sanitized phone: {sanitized}")
            
            if not sanitized:
                logger.error("LOGIN FAILED: Invalid phone number")
                self._send_response({'error': 'User does not have a valid phone number for OTP'}, 400)
                return

            # Generate and store OTP
            otp = _generate_otp(6)
            logger.info(f"Generated OTP: {otp} for user_id={user_id}")
            
            logger.info(f"Storing OTP in database/storage...")
            _put_otp(sanitized, otp, user_id)
            logger.info(f"OTP stored successfully")

            # Send OTP via 019SMS with dynamic code
            logger.info(f"Attempting to send SMS to: {phone_value}")
            ok, err = _send_otp_via_019sms(phone_value, otp)
            logger.info(f"SMS send result: success={ok}, error={err}")
            
            if not ok:
                logger.error(f"LOGIN FAILED: SMS send failed - {err}")
                self._send_response({'error': f'Failed to send OTP: {err}'}, 502)
                return

            logger.info(f"✅ LOGIN SUCCESS: OTP sent to user_id={user_id}")
            logger.info("="*60)
            self._send_response({'success': True, 'message': 'OTP sent successfully', 'user_id': user_id}, 200)
        except Exception as e:
            logger.error(f"❌ LOGIN EXCEPTION: {str(e)}", exc_info=True)
            logger.info("="*60)
            self._send_response({'error': f'Login failed: {str(e)}'}, 500)


    def handle_user_verify(self, data):
        try:
            logger.info("="*60)
            logger.info("NEW VERIFY REQUEST")
            logger.info(f"Request data: {json.dumps(data, indent=2)}")
            logger.info(f"Request headers: {dict(self.headers)}")
            
            phone_or_email = data.get('phone_or_email')
            otp = data.get('otp')
            
            if not phone_or_email or not otp:
                logger.warning("VERIFY FAILED: Missing phone_or_email or OTP")
                self._send_response({'error': 'Phone/email and OTP are required'}, 400)
                return

            logger.info(f"Verify attempt for: {phone_or_email} with OTP: {otp}")

            # Resolve user and target phone used for OTP
            domain = ['&', '|', ('phone', '=', phone_or_email), ('email', '=', phone_or_email), ('active', '=', True)]
            logger.info(f"Searching user with domain: {domain}")
            user_ids = execute_odoo_kw('res.partner', 'search', [domain])
            logger.info(f"User search result: {user_ids}")
            
            if not user_ids:
                logger.warning(f"VERIFY FAILED: User not found for {phone_or_email}")
                self._send_response({'error': 'User not found'}, 404)
                return
                
            user_id = user_ids[0]
            logger.info(f"User found: ID={user_id}")
            
            user = execute_odoo_kw('res.partner', 'read', [user_id, ['name', 'phone', 'email']])[0]
            logger.info(f"User details: name={user.get('name')}, phone={user.get('phone')}, email={user.get('email')}")
            
            phone_value = user.get('phone') or (phone_or_email if '@' not in str(phone_or_email) else None)
            sanitized = _sanitize_phone(phone_value)
            logger.info(f"Phone for OTP lookup: {phone_value} -> sanitized: {sanitized}")
            
            if not sanitized:
                logger.error("VERIFY FAILED: Invalid phone number")
                self._send_response({'error': 'User does not have a valid phone number for OTP'}, 400)
                return

            # Validate OTP from store
            logger.info(f"Validating OTP: {otp} for sanitized phone: {sanitized}")
            ok, matched_user_id, err = _get_and_validate_otp(sanitized, str(otp))
            logger.info(f"OTP validation result: success={ok}, matched_user_id={matched_user_id}, error={err}")
            
            if not ok:
                logger.warning(f"VERIFY FAILED: OTP validation failed - {err}")
                self._send_response({'error': err}, 401)
                return
                
            if matched_user_id != user_id:
                logger.error(f"VERIFY FAILED: User ID mismatch - expected {user_id}, got {matched_user_id}")
                self._send_response({'error': 'OTP does not match user'}, 401)
                return

            # Issue JWT and create session
            current_time = int(time.time())
            payload = {
                'user_id': user_id,
                'phone': user.get('phone'),
                'email': user.get('email'),
                'name': user.get('name'),
                'iat': current_time,
                'exp': current_time + 10800
            }
            logger.info(f"Generating JWT token with payload: {json.dumps(payload, indent=2)}")
            
            token = jwt.encode(payload, JWT_SECRET, algorithm='HS256')
            logger.info(f"JWT token generated (first 20 chars): {token[:20]}...")
            
            session_id = create_session(user_id, user, token)
            logger.info(f"Session created: session_id={session_id}")
            
            response_data = {
                'success': True,
                'token': token,
                'session_id': session_id,
                'user_id': user_id,
                'data': user,
                'expires_in': 10800
            }
            
            logger.info(f"✅ VERIFY SUCCESS: User {user_id} authenticated")
            logger.info("="*60)
            self._send_response(response_data, 200)
        except Exception as e:
            logger.error(f"❌ VERIFY EXCEPTION: {str(e)}", exc_info=True)
            logger.info("="*60)
            self._send_response({'error': f'Verification failed: {str(e)}'}, 500)


    def handle_store_visit(self, data):
        try:
            auth_header = self.headers.get('Authorization')
            if not auth_header or not auth_header.startswith('Bearer '):
                self._send_response({'error': 'Authorization header missing or invalid'}, 401)
                return
            
            token = auth_header.split(' ')[1]
            
            try:
                decoded_token = validate_token_and_session(token)
            except jwt.ExpiredSignatureError:
                logger.warning("Expired JWT token received")
                self._send_response({'error': 'Token has expired'}, 401)
                return
            except jwt.InvalidTokenError:
                logger.warning("Invalid JWT token received")
                self._send_response({'error': 'Invalid token'}, 401)
                return
            
            user_id = decoded_token['user_id']
            user_data = execute_odoo_kw('res.partner', 'read', [user_id, ['name', 'phone', 'email']])[0]
            
            visit_data = {
                'name': data.get('name', user_data.get('name', 'Anonymous Visit')),
                'phone': data.get('phone', user_data.get('phone', '')),
                'email': data.get('email', user_data.get('email', '')),
                'user_id': str(user_id),
                'last_name': data.get('last_name', ''),
                'mobile': data.get('mobile', data.get('phone', user_data.get('phone', ''))),
                'entered': True,
            }
            
            if data.get('warehouse_id'):
                visit_data['warehouse_id'] = data['warehouse_id']
            
            visit_id = execute_odoo_kw('store.visit', 'create', [visit_data])
            created_visit = execute_odoo_kw('store.visit', 'read', [visit_id])[0]
            
            logger.info(f"Store visit created with ID: {visit_id} by user {user_id}")
            self._send_response({
                'success': True, 
                'message': 'Store visit created successfully', 
                'visit_id': visit_id, 
                'data': visit_data
            }, 201)
            
        except Exception as e:
            logger.error(f"Store visit creation failed: {str(e)}")
            self._send_response({'error': f'Store visit creation failed: {str(e)}'}, 500)

    # NEW API 1: GET /api/v1/user/details - Get authenticated user's details
    def handle_get_user_details(self):
        """GET /api/v1/user/details - Get authenticated user's details."""
        try:
            auth_header = self.headers.get('Authorization')
            if not auth_header or not auth_header.startswith('Bearer '):
                self._send_response({'error': 'Authorization header missing or invalid'}, 401)
                return
            
            token = auth_header.split(' ')[1]
            
            try:
                decoded_token = validate_token_and_session(token)
            except jwt.ExpiredSignatureError:
                logger.warning("Expired JWT token received")
                self._send_response({'error': 'Token has expired'}, 401)
                return
            except jwt.InvalidTokenError:
                logger.warning("Invalid JWT token received")
                self._send_response({'error': 'Invalid token'}, 401)
                return
            
            user_id = decoded_token['user_id']
            # Fetch all user fields including the optional ones stored in Odoo fields
            user_data = execute_odoo_kw('res.partner', 'read', [user_id, ['name', 'phone', 'email', 'function', 'vat', 'ref']])[0]
            
            # Map back to API field names and include all optional fields
            api_user_data = {
                'id': user_data['id'],
                'name': user_data['name'],
                'phone': user_data['phone'],
                'email': user_data['email'],
                'last_name': user_data.get('function', ''),  # last_name stored in function field
                'birthday': user_data.get('vat', ''),        # birthday stored in vat field
                'identification_id': user_data.get('ref', '') # identification_id stored in ref field
            }
            
            # Get session information for compatibility
            session_info = {
                'user_id': user_id,
                'token_expires': decoded_token['exp'],
                'issued_at': decoded_token['iat']
            }
            
            logger.info(f"User details retrieved for user ID: {user_id}")
            # Use 'data' as the main property (not 'user_data')
            self._send_response({
                'success': True,
                'data': api_user_data,
                'session_info': session_info  # Additional session info for compatibility
            }, 200)
            
        except Exception as e:
            logger.error(f"Get user details failed: {str(e)}")
            self._send_response({'error': f'Get user details failed: {str(e)}'}, 500)

    # NEW API 2: POST /api/v1/user/update - Update authenticated user's details
    def handle_user_update(self, data):
        """POST /api/v1/user/update - Update authenticated user's details."""
        try:
            auth_header = self.headers.get('Authorization')
            if not auth_header or not auth_header.startswith('Bearer '):
                self._send_response({'error': 'Authorization header missing or invalid'}, 401)
                return
            
            token = auth_header.split(' ')[1]
            
            try:
                decoded_token = validate_token_and_session(token)
            except jwt.ExpiredSignatureError:
                logger.warning("Expired JWT token received")
                self._send_response({'error': 'Token has expired'}, 401)
                return
            except jwt.InvalidTokenError:
                logger.warning("Invalid JWT token received")
                self._send_response({'error': 'Invalid token'}, 401)
                return
            
            user_id = decoded_token['user_id']
            
            update_data = {}
            if 'name' in data:
                update_data['name'] = data['name']
            if 'phone' in data:
                existing_users = execute_odoo_kw('res.partner', 'search', [[('phone', '=', data['phone']), ('id', '!=', user_id)]])
                if existing_users:
                    self._send_response({'error': 'Phone number already in use by another user'}, 409)
                    return
                update_data['phone'] = data['phone']
            if 'email' in data:
                existing_users = execute_odoo_kw('res.partner', 'search', [[('email', '=', data['email']), ('id', '!=', user_id)]])
                if existing_users:
                    self._send_response({'error': 'Email already in use by another user'}, 409)
                    return
                update_data['email'] = data['email']
            if 'last_name' in data:
                update_data['function'] = data['last_name']  # Map last_name to function
            if 'birthday' in data:
                update_data['vat'] = data['birthday']  # Map birthday to vat (plain text)
            if 'identification_id' in data:
                update_data['ref'] = data['identification_id']  # Map identification_id to ref
            
            if not update_data:
                self._send_response({'error': 'No valid fields to update'}, 400)
                return
            
            execute_odoo_kw('res.partner', 'write', [[user_id], update_data])
            updated_user_data = execute_odoo_kw('res.partner', 'read', [user_id, ['name', 'phone', 'email', 'function', 'vat', 'ref']])[0]
            
            # Map back to API field names with HTML stripping for birthday
            api_updated_data = {
                'id': updated_user_data['id'],
                'name': updated_user_data['name'],
                'phone': updated_user_data['phone'],
                'email': updated_user_data['email'],
                'last_name': updated_user_data.get('function', ''),
                'birthday': updated_user_data.get('vat', ''),
                'identification_id': updated_user_data.get('ref', '')
            }
            
            for session_id, session_data in active_sessions.items():
                if session_data['token'] == token:
                    session_data['user_data'] = api_updated_data
                    break
            
            logger.info(f"User details updated for user ID: {user_id}")
            self._send_response({
                'success': True,
                'message': 'User details updated successfully',
                'data': api_updated_data
            }, 200)
            
        except Exception as e:
            logger.error(f"User update failed: {str(e)}")
            self._send_response({'error': f'User update failed: {str(e)}'}, 500)

    # NEW API 3: POST /api/v1/user/logout - Logout user and invalidate session
    def handle_user_logout(self, data):
        """POST /api/v1/user/logout - Logout user and invalidate session."""
        try:
            auth_header = self.headers.get('Authorization')
            if not auth_header or not auth_header.startswith('Bearer '):
                self._send_response({'error': 'Authorization header missing or invalid'}, 401)
                return
            
            token = auth_header.split(' ')[1]
            
            try:
                decoded_token = validate_token_and_session(token)
            except jwt.ExpiredSignatureError:
                logger.warning("Expired JWT token received during logout")
                self._send_response({'error': 'Token has expired'}, 401)
                return
            except jwt.InvalidTokenError:
                logger.warning("Invalid JWT token received during logout")
                self._send_response({'error': 'Invalid token'}, 401)
                return
            
            user_id = decoded_token['user_id']
            invalidate_session(token)
            
            logger.info(f"User logged out successfully: {user_id}")
            self._send_response({
                'success': True,
                'message': 'Logged out successfully'
            }, 200)
            
        except Exception as e:
            logger.error(f"Logout failed: {str(e)}")
            self._send_response({'error': f'Logout failed: {str(e)}'}, 500)

    # NEW API 4: GET /api/v1/user/sessions - Get active sessions
    def handle_get_active_sessions(self):
        """GET /api/v1/user/sessions - Get active sessions."""
        try:
            auth_header = self.headers.get('Authorization')
            if not auth_header or not auth_header.startswith('Bearer '):
                self._send_response({'error': 'Authorization header missing or invalid'}, 401)
                return
            
            token = auth_header.split(' ')[1]
            
            try:
                decoded_token = validate_token_and_session(token)
            except jwt.ExpiredSignatureError:
                logger.warning("Expired JWT token received")
                self._send_response({'error': 'Token has expired'}, 401)
                return
            except jwt.InvalidTokenError:
                logger.warning("Invalid JWT token received")
                self._send_response({'error': 'Invalid token'}, 401)
                return
            
            cleanup_expired_sessions()
            
            sessions_info = []
            for session_id, session_data in active_sessions.items():
                sessions_info.append({
                    'session_id': session_id,
                    'user_id': session_data['user_id'],
                    'user_name': session_data['user_data'].get('name', 'Unknown'),
                    'created_at': session_data['created_at'].isoformat(),
                    'last_activity': session_data['last_activity'].isoformat(),
                    'is_current': session_data['token'] == token
                })
            
            logger.info(f"Active sessions retrieved by user: {decoded_token['user_id']}")
            self._send_response({
                'success': True,
                'active_sessions_count': len(sessions_info),
                'sessions': sessions_info,
                'blacklisted_tokens_count': len(blacklisted_tokens)
            }, 200)
            
        except Exception as e:
            logger.error(f"Get active sessions failed: {str(e)}")
            self._send_response({'error': f'Get active sessions failed: {str(e)}'}, 500)

    # NEW API 5: POST/PUT /api/v1/user/{user_id} - Update user details by ID
    def handle_update_user_by_id(self, data, user_id):
        """POST/PUT /api/v1/user/{user_id} - Update user details by their ID."""
        try:
            # Validate user_id is numeric
            try:
                user_id = int(user_id)
            except ValueError:
                self._send_response({'error': 'Invalid user ID format'}, 400)
                return
            
            # Check if user exists
            user_exists = execute_odoo_kw_optimized('res.partner', 'search', 
                                                   [[('id', '=', user_id), ('active', '=', True)]], 
                                                   cache_key=f"user_exists_{user_id}")
            if not user_exists:
                self._send_response({'error': 'User not found'}, 404)
                return
            
            # Prepare update data with field mapping
            update_data = {}
            
            if 'name' in data:
                update_data['name'] = data['name']
                
            if 'phone' in data:
                # Check if phone is already used by another user
                existing_users = execute_odoo_kw('res.partner', 'search', 
                                                [[('phone', '=', data['phone']), ('id', '!=', user_id)]])
                if existing_users:
                    self._send_response({'error': 'Phone number already in use by another user'}, 409)
                    return
                update_data['phone'] = data['phone']
                
            if 'email' in data:
                # Check if email is already used by another user
                existing_users = execute_odoo_kw('res.partner', 'search', 
                                                [[('email', '=', data['email']), ('id', '!=', user_id)]])
                if existing_users:
                    self._send_response({'error': 'Email already in use by another user'}, 409)
                    return
                update_data['email'] = data['email']
                
            if 'last_name' in data:
                update_data['function'] = data['last_name']  # Map last_name to function field
                
            if 'birthday' in data:
                update_data['vat'] = data['birthday']  # Map birthday to vat field
                
            if 'identification_id' in data:
                update_data['ref'] = data['identification_id']  # Map identification_id to ref field
            
            if not update_data:
                self._send_response({'error': 'No valid fields to update'}, 400)
                return
            
            # Update the user
            execute_odoo_kw('res.partner', 'write', [[user_id], update_data])
            
            # Fetch updated user data
            updated_user_data = execute_odoo_kw('res.partner', 'read', 
                                              [user_id, ['name', 'phone', 'email', 'function', 'vat', 'ref']])[0]
            
            # Map back to API field names
            api_updated_data = {
                'id': updated_user_data['id'],
                'name': updated_user_data['name'],
                'phone': updated_user_data['phone'],
                'email': updated_user_data['email'],
                'last_name': updated_user_data.get('function', ''),
                'birthday': updated_user_data.get('vat', ''),
                'identification_id': updated_user_data.get('ref', '')
            }
            
            # Clear cache for this user
            cache_key = f"user_exists_{user_id}"
            if cache_key in cache_data:
                cache_data.pop(cache_key, None)
                cache_timestamps.pop(cache_key, None)
            
            logger.info(f"User {user_id} details updated successfully")
            self._send_response({
                'success': True,
                'message': f'User {user_id} updated successfully',
                'data': api_updated_data
            }, 200)
            
        except Exception as e:
            logger.error(f"Update user by ID failed: {str(e)}")
            self._send_response({'error': f'Update user by ID failed: {str(e)}'}, 500)

# --- Clean run() override to ensure valid startup logs/prints ---
def run(server_class=http.server.HTTPServer, handler_class=EnhancedApiHandler, port=8001):
    server_address = (
        config.get('server', 'host', fallback='0.0.0.0'),
        config.getint('server', 'port', fallback=8001)
    )
    httpd = server_class(server_address, handler_class)

    logger.info(
        f"Starting OPTIMIZED Enhanced API server on {server_address[0]}:{server_address[1]}..."
    )
    logger.info(f"Connected to Odoo: {ODOO_URL}")
    logger.info(f"Database: {ODOO_DB}")
    logger.info("PERFORMANCE OPTIMIZATIONS ACTIVE:")
    logger.info("   - Connection pooling (10 min TTL)")
    logger.info("   - Response caching (5 min TTL)")
    logger.info("   - Optimized session management")
    logger.info("   - 019SMS OTP integration with dynamic codes")
    logger.info("NEW ENDPOINTS AVAILABLE:")
    logger.info("   1. GET /api/v1/user/details - Get authenticated user's details")
    logger.info("   2. POST /api/v1/user/update - Update authenticated user's details")
    logger.info("   3. POST/PUT /api/v1/user/{user_id} - Update user by ID")
    logger.info("   4. POST /api/v1/user/logout - Logout user and invalidate session")
    logger.info("   5. GET /api/v1/user/sessions - Get active sessions")
    logger.info("   6. DELETE /api/v1/user/{user_id} - Soft delete user")
    logger.info("   7. GET /api/v1/user/list - Get user list")

    print("=" * 70)
    print("OPTIMIZED ENHANCED STORE API SERVER STARTING...")
    print("=" * 70)
    print(f"Odoo Server: {ODOO_URL}")
    print(f"Database: {ODOO_DB}")
    print(f"API Port: {server_address[1]}")
    print("PERFORMANCE OPTIMIZATIONS:")
    print("   - Connection pooling enabled")
    print("   - Response caching (5 min TTL)")
    print("   - Optimized session management")
    print("   - Reduced logging overhead")
    print("   - 019SMS OTP integration with dynamic codes")
    print("7 NEW ENDPOINTS READY!")
    print("=" * 70)

    httpd.serve_forever()

if __name__ == '__main__':
    run()