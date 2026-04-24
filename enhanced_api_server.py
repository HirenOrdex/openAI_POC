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
import socket
socket.setdefaulttimeout(15)  # 15s timeout on all XML-RPC calls

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
# Connection pooling with cleanup
odoo_connections = {}
connection_lock = threading.RLock()
last_cleanup = time.time()
last_connection_cleanup = time.time()

# Simple in-memory cache with TTL
cache_data = {}
cache_timestamps = {}
cache_lock = threading.RLock()  # FIX: Add lock for cache operations
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

# Add console handler for critical errors to see them even if file logging fails
console_handler = logging.StreamHandler()
console_handler.setLevel(logging.ERROR)
console_handler.setFormatter(formatter)
logger.addHandler(console_handler)
_refresh_db_available = None        # ← ADD THIS LINE

# odoo 3rd party api for sms 


# --- Performance Helper Functions ---
def get_cached_data(key):
    """Get cached data if still valid - THREAD SAFE"""
    current_time = time.time()
    with cache_lock:
        if key in cache_data and key in cache_timestamps:
            if current_time - cache_timestamps[key] < CACHE_TTL:
                return cache_data[key]
            else:
                # Remove expired cache
                cache_data.pop(key, None)
                cache_timestamps.pop(key, None)
    return None

def set_cached_data(key, data):
    """Set cached data with timestamp - THREAD SAFE"""
    with cache_lock:
        cache_data[key] = data
        cache_timestamps[key] = time.time()

def cleanup_cache():
    """Clean expired cache entries - THREAD SAFE"""
    global last_cleanup
    current_time = time.time()
    if current_time - last_cleanup > 60:  # Cleanup every minute
        with cache_lock:
            expired_keys = []
            for key, timestamp in list(cache_timestamps.items()):  # FIX: Use list() to avoid dict changed during iteration
                if current_time - timestamp > CACHE_TTL:
                    expired_keys.append(key)
            for key in expired_keys:
                cache_data.pop(key, None)
                cache_timestamps.pop(key, None)
            last_cleanup = current_time

def cleanup_old_connections():
    """Clean up stale connections - THREAD SAFE"""
    global last_connection_cleanup
    current_time = time.time()
    
    # Only cleanup every 5 minutes to reduce overhead
    if current_time - last_connection_cleanup < 300:
        return
    
    with connection_lock:
        stale_threads = []
        for thread_id, conn_info in list(odoo_connections.items()):  # FIX: Use list()
            # Remove connections older than 10 minutes
            if current_time - conn_info['created_at'] > 600:
                stale_threads.append(thread_id)
        
        for thread_id in stale_threads:
            odoo_connections.pop(thread_id, None)
            logger.info(f"Cleaned up stale connection for thread {thread_id}")
        
        last_connection_cleanup = current_time

def get_or_create_odoo_connection():
    """Get pooled Odoo connection or create new one - THREAD SAFE"""
    thread_id = threading.current_thread().ident
    current_time = time.time()
    
    with connection_lock:
        # Check if we have a valid connection for this thread
        if thread_id in odoo_connections:
            conn_info = odoo_connections[thread_id]
            # Reuse connection if it's less than 10 minutes old
            if current_time - conn_info['created_at'] < 600:
                return conn_info['uid'], conn_info['models']
            else:
                # Remove stale connection
                odoo_connections.pop(thread_id, None)
        
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

# FIX: Change default arguments from mutable [] and {} to None
def execute_odoo_kw_optimized(model, method, args=None, kwargs=None, cache_key=None):
    """Execute Odoo method with caching and connection pooling"""
    args = args or []  # FIX: Avoid mutable default argument
    kwargs = kwargs or {}  # FIX: Avoid mutable default argument
    
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
        
        # Periodic connection cleanup
        cleanup_old_connections()
        
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
active_sessions_lock = threading.RLock()  # FIX: Add lock for sessions
blacklisted_tokens = set()
blacklisted_tokens_lock = threading.RLock()  # FIX: Add lock for blacklist


refresh_tokens: dict = {}           # { refresh_token_str: { user_id, exp } }
refresh_tokens_lock = threading.RLock()
 
ACCESS_TOKEN_TTL  = 24 * 60 * 60   # 24 hours  (seconds)
REFRESH_TOKEN_TTL = 365 * 24 * 60 * 60  # 365 days (seconds)

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
        
        # FIX: Use optimized function to prevent connection exhaustion
        users_with_expired_otps = execute_odoo_kw_optimized(
            'res.partner', 'search',
            [[
                ('x_otp_expires_at', '!=', False),
                ('x_otp_expires_at', '<', current_time.strftime("%Y-%m-%d %H:%M:%S"))
            ]]
        )
        
        if users_with_expired_otps:
            # Clear expired OTP data
            execute_odoo_kw_optimized('res.partner', 'write', [
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
        logger.error(f"Failed to cleanup expired OTPs: {str(e)}", exc_info=True)  # FIX: Add exc_info

def _store_otp_in_partner(user_id: int, otp: str) -> bool:
    """Store OTP data directly in res.partner record"""
    try:
        current_time = datetime.utcnow()
        expires_at = current_time + timedelta(seconds=OTP_TTL_SECONDS)
        
        # Update user record with OTP data using custom fields
        otp_data = {
            'x_otp_code': otp,
            'x_otp_created_at': current_time.strftime("%Y-%m-%d %H:%M:%S"),
            'x_otp_expires_at': expires_at.strftime("%Y-%m-%d %H:%M:%S"),
            'x_otp_attempts': 0  # Reset attempts when new OTP is generated
        }
        
        execute_odoo_kw_optimized('res.partner', 'write', [[user_id], otp_data])
        logger.info(f"OTP stored in user record {user_id}, expires at {expires_at}")
        
        # Clean up expired OTPs from other users periodically
        _cleanup_expired_otps()
        
        return True
        
    except Exception as e:
        logger.error(f"Failed to store OTP in user record {user_id}: {str(e)}", exc_info=True)
        return False

def _validate_otp_from_partner(phone_or_email: str, otp: str) -> tuple:
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
            ('x_otp_expires_at', '>', current_time.strftime("%Y-%m-%d %H:%M:%S"))
        ]
        
        user_ids = execute_odoo_kw_optimized('res.partner', 'search', [domain])
        
        if not user_ids:
            return False, None, 'OTP not found or expired. Please request a new code.'
        
        user_id = user_ids[0]
        
        # Get current OTP data
        user_data = execute_odoo_kw_optimized('res.partner', 'read', [
            user_id, 
            ['x_otp_code', 'x_otp_attempts', 'x_otp_expires_at']
        ])[0]
        
        current_attempts = user_data.get('x_otp_attempts', 0)
        
        # Check if max attempts exceeded
        if current_attempts >= MAX_OTP_ATTEMPTS:
            # Clear OTP data to prevent further attempts
            execute_odoo_kw_optimized('res.partner', 'write', [[user_id], {
                'x_otp_code': False,
                'x_otp_expires_at': False,
                'x_otp_attempts': 0,
                'x_otp_created_at': False
            }])
            return False, None, f'OTP has exceeded maximum attempts ({MAX_OTP_ATTEMPTS}). Please request a new code.'
        
        # Increment attempt counter
        new_attempts = current_attempts + 1
        execute_odoo_kw_optimized('res.partner', 'write', [[user_id], {'x_otp_attempts': new_attempts}])
        
        # Validate OTP code
        stored_otp = user_data.get('x_otp_code', '')
        if str(stored_otp) != str(otp):
            if new_attempts >= MAX_OTP_ATTEMPTS:
                # Clear OTP data if max attempts reached
                execute_odoo_kw_optimized('res.partner', 'write', [[user_id], {
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
        execute_odoo_kw_optimized('res.partner', 'write', [[user_id], {
            'x_otp_code': False,
            'x_otp_expires_at': False,
            'x_otp_attempts': 0,
            'x_otp_created_at': False
        }])
        
        logger.info(f"OTP validated successfully for user: {user_id}")
        return True, user_id, None
        
    except Exception as e:
        logger.error(f"Failed to validate OTP: {str(e)}", exc_info=True)
        return False, None, f'OTP validation failed: {str(e)}'

def _get_otp_stats() -> dict:
    """Get OTP statistics from res.partner records"""
    try:
        current_time = datetime.utcnow()
        
        # Count active OTPs
        active_otps = len(execute_odoo_kw_optimized('res.partner', 'search', [[
            ('x_otp_code', '!=', False),
            ('x_otp_expires_at', '>', current_time.strftime("%Y-%m-%d %H:%M:%S"))
        ]]))

        expired_otps = len(execute_odoo_kw_optimized('res.partner', 'search', [[
            ('x_otp_code', '!=', False),
            ('x_otp_expires_at', '<', current_time.strftime("%Y-%m-%d %H:%M:%S"))
        ]]))

        
        return {
            'active_otps': active_otps,
            'expired_otps_pending_cleanup': expired_otps,
            'otp_ttl_seconds': OTP_TTL_SECONDS,
            'max_attempts': MAX_OTP_ATTEMPTS
        }
        
    except Exception as e:
        logger.error(f"Failed to get OTP stats: {str(e)}", exc_info=True)
        return {'error': str(e)}

def _check_otp_fields_exist() -> bool:
    """Check if custom OTP fields exist in res.partner model"""
    try:
        # Try to read OTP fields from any partner record to test if fields exist
        partner_ids = execute_odoo_kw_optimized('res.partner', 'search', [[]], {'limit': 1})
        if partner_ids:
            execute_odoo_kw_optimized('res.partner', 'read', [
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

# =============================================================================
# REFRESH TOKEN — ODOO DB PERSISTENCE
# Requires two custom fields on res.partner (add via Odoo Studio / Technical):
#   x_refresh_jti        (Char)     — JTI of the currently valid refresh token
#   x_refresh_token_exp  (Datetime) — UTC expiry of that refresh token
# =============================================================================

def _store_refresh_token(user_id: int, jti: str, exp_ts: int) -> bool:
    """Write a new refresh-token JTI to res.partner. Overwrites any existing one."""
    try:
        exp_dt = datetime.utcfromtimestamp(exp_ts).strftime("%Y-%m-%d %H:%M:%S")
        execute_odoo_kw_optimized('res.partner', 'write', [
            [user_id],
            {'x_refresh_jti': jti, 'x_refresh_token_exp': exp_dt}
        ])
        logger.info(f"Stored refresh JTI for user_id={user_id}, exp={exp_dt}")
        return True
    except Exception as e:
        logger.error(f"_store_refresh_token failed for user_id={user_id}: {e}", exc_info=True)
        return False


def _validate_refresh_token_db(user_id: int, jti: str) -> tuple:
    """
    Check that (user_id, jti) matches the stored record AND is not expired.
    Returns (ok: bool, error_msg: str | None)
    """
    try:
        current_time = datetime.utcnow()
        rows = execute_odoo_kw_optimized('res.partner', 'read', [
            user_id, ['x_refresh_jti', 'x_refresh_token_exp']
        ])
        if not rows:
            return False, "User not found"
        row = rows[0]
        stored_jti = row.get('x_refresh_jti') or ''
        stored_exp = row.get('x_refresh_token_exp')  # Odoo returns str or False

        if not stored_jti:
            return False, "No active refresh token on record — please log in again"
        if stored_jti != jti:
            return False, "Refresh token has been rotated or revoked — please log in again"
        if stored_exp:
            # Odoo may return "2026-04-20 10:30:00" string
            try:
                exp_dt = datetime.strptime(str(stored_exp), "%Y-%m-%d %H:%M:%S")
                if current_time > exp_dt:
                    return False, "Refresh token expired"
            except ValueError:
                pass  # If we can't parse, fall through and trust JWT exp
        return True, None
    except Exception as e:
        logger.error(f"_validate_refresh_token_db failed: {e}", exc_info=True)
        return False, f"Token validation error: {e}"


def _rotate_refresh_token_db(user_id: int, old_jti: str, new_jti: str, new_exp_ts: int) -> bool:
    """
    Atomically swap old JTI → new JTI in Odoo.
    First verifies old_jti is still stored (prevents replay after server crash).
    """
    ok, err = _validate_refresh_token_db(user_id, old_jti)
    if not ok:
        logger.warning(f"_rotate_refresh_token_db: validation failed — {err}")
        return False
    return _store_refresh_token(user_id, new_jti, new_exp_ts)


def _revoke_refresh_token_db(user_id: int) -> bool:
    """Clear the stored JTI (logout / forced re-login)."""
    try:
        execute_odoo_kw_optimized('res.partner', 'write', [
            [user_id],
            {'x_refresh_jti': False, 'x_refresh_token_exp': False}
        ])
        logger.info(f"Revoked refresh token for user_id={user_id}")
        return True
    except Exception as e:
        logger.error(f"_revoke_refresh_token_db failed: {e}", exc_info=True)
        return False


def _check_refresh_token_fields_exist() -> bool:
    """Verify the two custom fields are present on res.partner."""
    try:
        partner_ids = execute_odoo_kw_optimized('res.partner', 'search', [[]], {'limit': 1})
        if partner_ids:
            execute_odoo_kw_optimized('res.partner', 'read', [
                partner_ids[0], ['x_refresh_jti', 'x_refresh_token_exp']
            ])
        return True
    except Exception as e:
        logger.error(
            "Refresh-token DB fields missing on res.partner — add via Odoo Studio:\n"
            "  x_refresh_jti       (Char)\n"
            "  x_refresh_token_exp (Datetime)\n"
            f"Error: {e}"
        )
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
            logger.error(f"Partner OTP validation exception: {str(e)}, trying local storage", exc_info=True)
    
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
        logger.info(f"✅ OTP validated successfully from local storage for user_id={entry['user_id']}")
        return True, entry['user_id'], None


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
            logger.error(f"Partner OTP validation exception: {str(e)}, trying local storage", exc_info=True)
    
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
        logger.info(f"✅ OTP validated successfully from local storage for user_id={entry['user_id']}")
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
        logger.error(f"Failed to load SMS config: {e}", exc_info=True)
        return None

def _format_phone_for_019sms(phone: str) -> tuple:
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

def _send_otp_via_019sms(to_phone: str, otp_code: str) -> tuple:
    """Send OTP using 019SMS API with Bearer token authentication and proper message format.
    Returns (success, error_message).
    """
    try:  # FIX: Wrap entire function in try-except
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
            
            if resp.status_code not in (200, 201):
                logger.error(f"019SMS API HTTP error: {resp.status_code} - {resp.text}")
                return False, f"SMS service error: HTTP {resp.status_code}"
            
            try:
                response_data = resp.json()
                logger.info(f"019SMS API response: {response_data}")
                
                # Check for success - 019SMS returns numeric status codes
                status = response_data.get('status')
                message = response_data.get('message', '')
                
                # Check if it's a success response
                if status == 0 or status == 200 or status == 'success' or response_data.get('success') == True:
                    logger.info(f"✅ OTP sent successfully to {formatted_phone} (shipment_id: {response_data.get('shipment_id', 'N/A')})")
                    return True, ''
                
                # Check for error status codes
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
                    
            except json.JSONDecodeError as je:
                logger.error(f"019SMS API invalid JSON response: {resp.text}", exc_info=True)
                return False, "SMS service returned invalid response"
                
        except requests.exceptions.Timeout as te:
            logger.error(f"019SMS API timeout: {str(te)}", exc_info=True)
            return False, "SMS service timeout"
        except requests.exceptions.RequestException as re:
            logger.error(f"019SMS API request failed: {str(re)}", exc_info=True)
            return False, f"SMS service request failed: {str(re)}"
    except Exception as e:
        logger.error(f"019SMS API unexpected error: {str(e)}", exc_info=True)
        return False, f"SMS service error: {str(e)}"

def generate_session_id(user_id):
    timestamp = str(int(time.time()))
    data = f"{user_id}{timestamp}{JWT_SECRET}"
    return hashlib.sha256(data.encode()).hexdigest()

def create_session(user_id, user_data, token):
    """Create session - THREAD SAFE"""
    session_id = generate_session_id(user_id)
    session_data = {
        'user_id': user_id,
        'user_data': user_data,
        'token': token,
        'created_at': datetime.utcnow(),
        'last_activity': datetime.utcnow()
    }
    with active_sessions_lock:
        active_sessions[session_id] = session_data
    logger.info(f"Session created with ID: {session_id} for user: {user_id}")
    return session_id

def validate_token_and_session(token):
    """Validate token - THREAD SAFE"""
    with blacklisted_tokens_lock:
        if token in blacklisted_tokens:
            raise jwt.InvalidTokenError("Token has been revoked")
    
    try:
        decoded_token = jwt.decode(token, JWT_SECRET, algorithms=['HS256'])
        with active_sessions_lock:
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
    """Invalidate session - THREAD SAFE"""
    with blacklisted_tokens_lock:
        blacklisted_tokens.add(token)
    
    with active_sessions_lock:
        for session_id, session_data in list(active_sessions.items()):
            if session_data['token'] == token:
                del active_sessions[session_id]
                logger.info(f"Session {session_id} invalidated")
                break

def cleanup_expired_sessions():
    """Cleanup expired sessions - THREAD SAFE"""
    current_time = datetime.utcnow()
    expired_sessions = []
    
    with active_sessions_lock:
        for session_id, session_data in list(active_sessions.items()):  # FIX: Use list()
            if (current_time - session_data['last_activity']).total_seconds() > 10800:
                expired_sessions.append((session_id, session_data['token']))
        
        for session_id, token in expired_sessions:
            del active_sessions[session_id]
            with blacklisted_tokens_lock:
                blacklisted_tokens.add(token)
            logger.info(f"Expired session {session_id} cleaned up")
def _is_refresh_db_available() -> bool:
    """Return True if x_refresh_jti / x_refresh_token_exp exist on res.partner."""
    global _refresh_db_available
    if _refresh_db_available is None:
        _refresh_db_available = _check_refresh_token_fields_exist()
        if _refresh_db_available:
            logger.info("Refresh-token DB fields confirmed — DB-backed token validation ACTIVE")
        else:
            logger.warning("Refresh-token DB fields NOT found — falling back to JWT-only validation")
    return _refresh_db_available

# --- XML-RPC Connection ---
# FIX: Remove the old execute_odoo_kw function to prevent confusion
# Only use execute_odoo_kw_optimized everywhere

# --- Utility Functions ---
def strip_html_tags(text):
    """Remove HTML tags from text, specifically for birthday field that might contain <p> tags"""
    if not text:
        return ''
    # Remove HTML tags using regex
    clean = re.sub('<.*?>', '', str(text))
    return clean.strip()

# ── SSE globals for QR visit wait endpoint ───────────────────────────────────
_visit_events:  dict = {}          # visit_token -> threading.Event
_visit_results: dict = {}          # visit_token -> partner_data (early pickup)
_visit_lock    = threading.Lock()
VISIT_SSE_TIMEOUT   = 300         # 5 min — how long to hold the SSE connection
VISIT_SSE_HEARTBEAT = 20          # send a heartbeat comment every 20 s

def _sse_write(handler, data: dict):
    """Write one SSE data frame and flush."""
    payload = f"data: {json.dumps(data)}\n\n".encode()
    handler.wfile.write(payload)
    handler.wfile.flush()
# ─────────────────────────────────────────────────────────────────────────────

class EnhancedApiHandler(http.server.BaseHTTPRequestHandler):

    def _send_response(self, data, status=200):
        try:  # FIX: Wrap response in try-except
            self.send_response(status)
            self.send_header('Content-type', 'application/json')
            self.send_header('Access-Control-Allow-Origin', '*')
            self.send_header('Access-Control-Allow-Methods', 'GET, POST, PUT, DELETE, OPTIONS')
            self.send_header('Access-Control-Allow-Headers', 'Content-Type, Authorization')
            self.end_headers()
            self.wfile.write(json.dumps(data, indent=2).encode('utf-8'))
        except Exception as e:
            logger.error(f"Failed to send response: {str(e)}", exc_info=True)

    def do_OPTIONS(self):
        try:  # FIX: Wrap in try-except
            self.send_response(200)
            self.send_header('Access-Control-Allow-Origin', '*')
            self.send_header('Access-Control-Allow-Methods', 'GET, POST, PUT, DELETE, OPTIONS')
            self.send_header('Access-Control-Allow-Headers', 'Content-Type, Authorization')
            self.end_headers()
        except Exception as e:
            logger.error(f"OPTIONS request failed: {str(e)}", exc_info=True)
        
    def do_GET(self):
        try:  # FIX: Wrap entire method in try-except
            cleanup_cache()  # Periodic cache cleanup
            if self.path == '/api/v1/health':
                otp_stats = _get_otp_stats()
                otp_fields_exist = _check_otp_fields_exist()
                
                with connection_lock:
                    conn_count = len(odoo_connections)
                with active_sessions_lock:
                    session_count = len(active_sessions)
                with cache_lock:
                    cache_count = len(cache_data)
                
                self._send_response({
                    'status': 'ok', 
                    'message': 'OPTIMIZED Enhanced Store API with Database OTP is running!',
                    'database': ODOO_DB,
                    'port': config.getint('server', 'port', fallback=8001),
                    'performance_info': {
                        'cache_entries': cache_count,
                        'active_connections': conn_count,
                        'active_sessions': session_count
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
                        'Compact JSON responses',
                        'Thread-safe operations',
                        'Fixed mutable defaults bug'
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
                user_id = self.path.split('/')[-1]
                self.handle_get_user_by_id(user_id)
            # ✅ NEW SSE ROUTE (place BEFORE else)
            elif re.match(r'^/api/v1/wait-visit/([^/?]+)', self.path):
                token = re.match(r'^/api/v1/wait-visit/([^/?]+)', self.path).group(1)
                self.handle_wait_visit(token)
                return
            else:
                logger.warning(f"404 Not Found for path: {self.path}")
                self._send_response({'error': 'Not Found'}, 404)
        except Exception as e:
            logger.error(f"GET request failed: {str(e)}", exc_info=True)
            self._send_response({'error': f'Internal server error: {str(e)}'}, 500)

    def handle_send_invoice_sms(self, data):
        try:  # FIX: Wrap in try-except
            print("[SMS SERVICE] ===============================")
            print("[SMS SERVICE] Request received")

            order_name = data.get("order_name")
            customer_name = data.get("customer_name", "Anonymous")
            phone_number = data.get("phone_number")
            invoice_url = data.get("invoice_url")

            print(f"[SMS SERVICE] Order: {order_name}")
            print(f"[SMS SERVICE] Customer: {customer_name}")
            print(f"[SMS SERVICE] Phone (raw): {phone_number}")
            print(f"[SMS SERVICE] Invoice URL: {invoice_url}")

            if not phone_number:
                self._send_response({
                    "success": False,
                    "message": "Phone number missing"
                }, 400)
                return

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
                self._send_response({
                    "success": True,
                    "message": "SMS sent successfully",
                    "response": response.text,
                    "invoice_url": invoice_url
                }, 200)
                return

            self._send_response({
                "success": False,
                "message": "019SMS API error",
                "response": response.text
            }, 500)

        except Exception as e:
            logger.error(f"Invoice SMS failed: {str(e)}", exc_info=True)
            self._send_response({
                "success": False,
                "message": str(e)
            }, 500)

    def handle_get_user_list(self):
        """GET /api/v1/user/list?active=true|false - Get user list filtered by active status."""
        try:
            from urllib.parse import urlparse, parse_qs
            query = urlparse(self.path).query
            params = parse_qs(query)
            active_param = params.get('active', ['true'])[0].lower()
            if active_param == 'false':
                active_value = False
            else:
                active_value = True
            
            domain = [[('active', '=', active_value)]]
            user_ids = execute_odoo_kw_optimized('res.partner', 'search', domain, cache_key=f"user_list_{active_value}")
            if not user_ids:
                self._send_response({'success': True, 'users': []}, 200)
                return
            
            users = execute_odoo_kw_optimized('res.partner', 'read', [user_ids, ['id', 'name', 'phone', 'email', 'last_name', 'vat', 'ref']], cache_key=f"user_list_data_{active_value}")
            user_list = []
            for user in users:
                user_list.append({
                    'id': user['id'],
                    'name': user['name'],
                    'phone': user['phone'],
                    'email': user['email'],
                    'last_name': user.get('last_name', ''),
                    'birthday': user.get('vat', ''),
                    'identification_id': user.get('ref', '')
                })
            self._send_response({'success': True, 'users': user_list}, 200)
        except Exception as e:
            logger.error(f"Get user list failed: {str(e)}", exc_info=True)
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
            elif self.path == '/api/v1/user/refresh':
                self.handle_user_refresh(data)
            elif self.path == '/api/v1/store-visit':
                self.handle_store_visit(data)
            elif self.path == '/api/v1/internal/activate-visit':
                self.handle_internal_activate_visit(data)
            elif self.path.startswith('/api/v1/user/') and len(self.path.split('/')) == 5:
                user_id = self.path.split('/')[-1]
                self.handle_update_user_by_id(data, user_id)
            elif self.path == "/api/v1/send-sms":
                self.handle_send_invoice_sms(data)
            else:
                self._send_response({'error': 'Not Found'}, 404)
        except json.JSONDecodeError as je:
            logger.error(f"Invalid JSON in request: {str(je)}", exc_info=True)
            self._send_response({'error': 'Invalid JSON in request body'}, 400)
        except Exception as e:
            logger.error(f"Request processing error: {str(e)}", exc_info=True)
            self._send_response({'error': f'Request processing error: {str(e)}'}, 500)

    def do_DELETE(self):
        try:
            if self.path.startswith('/api/v1/user/') and len(self.path.split('/')) == 5:
                user_id = self.path.split('/')[-1]
                self.handle_soft_delete_user(user_id)
            else:
                self._send_response({'error': 'Not Found'}, 404)
        except Exception as e:
            logger.error(f"DELETE request processing error: {str(e)}", exc_info=True)
            self._send_response({'error': f'Request processing error: {str(e)}'}, 500)

    def handle_soft_delete_user(self, user_id):
        """DELETE /api/v1/user/{user_id} - Soft delete user by setting active=False."""
        try:
            try:
                user_id = int(user_id)
            except ValueError:
                self._send_response({'error': 'Invalid user ID format'}, 400)
                return
            
            user_exists = execute_odoo_kw_optimized('res.partner', 'search', [[('id', '=', user_id), ('active', '=', True)]], cache_key=f"user_exists_{user_id}")
            if not user_exists:
                self._send_response({'error': 'User not found or already deleted'}, 404)
                return
            
            user_info = execute_odoo_kw_optimized('res.partner', 'read', [user_id, ['phone', 'email']])[0]
            
            # Clear cache
            with cache_lock:
                cache_data.pop(f"user_exists_{user_id}", None)
                cache_timestamps.pop(f"user_exists_{user_id}", None)
                if user_info.get('phone'):
                    cache_data.pop(f"user_exists_phone_{user_info['phone']}", None)
                    cache_timestamps.pop(f"user_exists_phone_{user_info['phone']}", None)
                    if user_info.get('email'):
                        cache_data.pop(f"user_exists_email_{user_info['email']}", None)
                        cache_timestamps.pop(f"user_exists_email_{user_info['email']}", None)
            execute_odoo_kw_optimized('res.partner', 'write', [[user_id], {'active': False}])
            logger.info(f"User {user_id} soft deleted successfully")
            self._send_response({'success': True, 'message': f'User {user_id} deleted (soft) successfully'}, 200)
        except Exception as e:
            logger.error(f"Soft delete user failed: {str(e)}", exc_info=True)
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
            
            user_data = execute_odoo_kw_optimized('res.partner', 'read', [user_id, ['name', 'phone', 'email', 'last_name', 'vat', 'ref']])[0]
            api_user_data = {
                'id': user_data['id'],
                'name': user_data['name'],
                'phone': user_data['phone'],
                'email': user_data['email'],
                'last_name': user_data.get('last_name', ''),
                'birthday': user_data.get('vat', ''),
                'identification_id': user_data.get('ref', '')
            }
            self._send_response({'success': True, 'data': api_user_data}, 200)
        except Exception as e:
            logger.error(f"Get user by ID failed: {str(e)}", exc_info=True)
            self._send_response({'error': f'Get user by ID failed: {str(e)}'}, 500)

    def handle_user_register(self, data):
        try:
            phone = data.get('phone')
            email = data.get('email')

            # --- FIX 2 & 3: Search both active AND inactive records ---
            # active_test=False tells Odoo to include soft-deleted (active=False) records in search.
            # This prevents creating duplicate res.partner records for the same phone/email.

            # Step 1: Check if an ACTIVE user already exists → reject immediately (409)
            if phone:
                active_users = execute_odoo_kw_optimized(
                    'res.partner', 'search',
                    [[('phone', '=', phone), ('active', '=', True)]]
                )
                if active_users:
                    self._send_response({'error': 'User with this phone already exists'}, 409)
                    return

            if email:
                active_users = execute_odoo_kw_optimized(
                    'res.partner', 'search',
                    [[('email', '=', email), ('active', '=', True)]]
                )
                if active_users:
                    self._send_response({'error': 'User with this email already exists'}, 409)
                    return

            # Step 2: Check if a SOFT-DELETED user exists for same phone/email → reactivate it
            # Without active_test=False, Odoo's search silently skips inactive records.
            inactive_user_id = None
            if phone:
                inactive_users = execute_odoo_kw_optimized(
                    'res.partner', 'search',
                    [[('phone', '=', phone), ('active', '=', False)]],
                    {'context': {'active_test': False}}
                )
                if inactive_users:
                    inactive_user_id = inactive_users[0]

            if not inactive_user_id and email:
                inactive_users = execute_odoo_kw_optimized(
                    'res.partner', 'search',
                    [[('email', '=', email), ('active', '=', False)]],
                    {'context': {'active_test': False}}
                )
                if inactive_users:
                    inactive_user_id = inactive_users[0]

            if inactive_user_id:
                # Reactivate the old record and update its fields with the new registration data
                reactivate_data = {
                    'active': True,
                    'name': data.get('name', 'Unknown User'),
                    'phone': phone,
                    'email': email or '',
                    'last_name': data.get('last_name', ''),
                    'vat': data.get('birthday', ''),
                    'ref': data.get('identification_id', ''),
                }
                execute_odoo_kw_optimized('res.partner', 'write', [[inactive_user_id], reactivate_data])

                # Clear any stale cache for this user
                with cache_lock:
                    cache_data.pop(f"user_exists_{inactive_user_id}", None)
                    cache_timestamps.pop(f"user_exists_{inactive_user_id}", None)
                    if phone:
                        cache_data.pop(f"user_exists_phone_{phone}", None)
                        cache_timestamps.pop(f"user_exists_phone_{phone}", None)
                    if email:
                        cache_data.pop(f"user_exists_email_{email}", None)
                        cache_timestamps.pop(f"user_exists_email_{email}", None)

                api_response_data = {
                    'name': data.get('name', 'Unknown User'),
                    'phone': phone,
                    'email': email or '',
                    'last_name': data.get('last_name', ''),
                    'birthday': data.get('birthday', ''),
                    'identification_id': data.get('identification_id', '')
                }

                logger.info(f"Reactivated soft-deleted user ID: {inactive_user_id}")
                self._send_response({
                    'success': True,
                    'message': 'User re-registered successfully',
                    'user_id': inactive_user_id,
                    'data': api_response_data
                }, 201)
                return

            # Step 3: No existing record at all → create fresh
            user_data = {
                'name': data.get('name', 'Unknown User'),
                'phone': phone,
                'email': email or '',
                'last_name': data.get('last_name', ''),
                'vat': data.get('birthday', ''),
                'ref': data.get('identification_id', ''),
            }

            user_id = execute_odoo_kw_optimized('res.partner', 'create', [user_data])

            api_response_data = {
                'name': data.get('name', 'Unknown User'),
                'phone': phone,
                'email': email or '',
                'last_name': data.get('last_name', ''),
                'birthday': data.get('birthday', ''),
                'identification_id': data.get('identification_id', '')
            }

            logger.info(f"Successfully registered new user with ID: {user_id}")
            self._send_response({
                'success': True,
                'message': 'User registered successfully',
                'user_id': user_id,
                'data': api_response_data
            }, 201)

        except Exception as e:
            logger.error(f"Registration failed: {str(e)}", exc_info=True)
            self._send_response({'error': f'Registration failed: {str(e)}'}, 500)


    def handle_user_login(self, data):
        try:
            logger.info("="*60)
            logger.info("NEW LOGIN REQUEST - SEND OTP")
            logger.info(f"Request data: {json.dumps(data, indent=2)}")
            
            phone_or_email = data.get('phone_or_email')
            if not phone_or_email:
                logger.warning("LOGIN FAILED: Missing phone_or_email")
                self._send_response({'error': 'Phone or email is required'}, 400)
                return
 
            logger.info(f"Login attempt for: {phone_or_email}")
 
            domain = ['&', '|', ('phone', '=', phone_or_email), ('email', '=', phone_or_email), ('active', '=', True)]
            logger.info(f"Searching user with domain: {domain}")
            user_ids = execute_odoo_kw_optimized('res.partner', 'search', [domain])
            logger.info(f"User search result: {user_ids}")
            
            if not user_ids:
                logger.warning(f"LOGIN FAILED: User not found for {phone_or_email}")
                self._send_response({'error': 'User not found'}, 404)
                return
 
            user_id = user_ids[0]
            logger.info(f"User found: ID={user_id}")
            
            user = execute_odoo_kw_optimized('res.partner', 'read', [user_id, ['phone', 'name', 'email']])[0]
            logger.info(f"User details: name={user.get('name')}, phone={user.get('phone')}, email={user.get('email')}")
            
            phone_value = user.get('phone') or (phone_or_email if '@' not in str(phone_or_email) else None)
            logger.info(f"Phone value for OTP: {phone_value}")
            
            sanitized = _sanitize_phone(phone_value)
            logger.info(f"Sanitized phone: {sanitized}")
            
            if not sanitized:
                logger.error("LOGIN FAILED: Invalid phone number")
                self._send_response({'error': 'User does not have a valid phone number for OTP'}, 400)
                return
            IS_DEMO_USER = sanitized == '0000001234'  # compare digits-only to avoid format mismatch
 
            if IS_DEMO_USER:
                otp = 123456
            else:
                otp = _generate_otp(6)
            logger.info(f"Generated OTP: {otp} for user_id={user_id}")
            print(f"Generated OTP for user_id={user_id}: {otp}")  # Also print to console for easy testing
            logger.info(f"Storing OTP in database/storage...")
            _put_otp(sanitized, otp, user_id)
            logger.info(f"OTP stored successfully")
 
            if IS_DEMO_USER:
                logger.info(f"Skipping SMS for demo number: {phone_value} (sanitized: {sanitized})")
                logger.info(f"✅ LOGIN SUCCESS (TEST MODE): OTP generated for user_id={user_id}")
                logger.info("="*60)
                self._send_response({
                    'success': True,
                    'message': 'OTP generated successfully (test mode)',
                    'user_id': user_id,
                    'otp': otp
                    }, 200)
                return
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


    def _generate_tokens_for_user(self, user_id, user):
        """
        Issues a new access token (24 h) + refresh token (7 d).
        Stores the refresh token in the in-memory store.
        Returns (access_token, refresh_token, session_id).
        """
        import secrets as _secrets  # already imported at top level, this is a reminder
    
        current_time = int(time.time())
    
        # --- Access token (short-lived) ---
        access_payload = {
            'user_id': user_id,
            'phone':   user.get('phone'),
            'email':   user.get('email'),
            'name':    user.get('name'),
            'iat':     current_time,
            'exp':     current_time + ACCESS_TOKEN_TTL,  # 24 h
            'type':    'access',
        }
        access_token = jwt.encode(access_payload, JWT_SECRET, algorithm='HS256')
    
        # --- Refresh token (long-lived, opaque) ---
        raw_refresh = secrets.token_hex(32)
        refresh_payload = {
            'user_id': user_id,
            'iat':     current_time,
            'exp':     current_time + REFRESH_TOKEN_TTL,  # 7 d
            'type':    'refresh',
            'jti':     raw_refresh,   # unique identifier so it can be revoked
        }
        refresh_token = jwt.encode(refresh_payload, JWT_SECRET, algorithm='HS256')
    
        # Store refresh token (keyed by jti for easy revocation)
        with refresh_tokens_lock:
            refresh_tokens[raw_refresh] = {
                'user_id':  user_id,
                'exp':      current_time + REFRESH_TOKEN_TTL,
                'rt_str':   refresh_token,  # full encoded JWT (returned to client)
            }
    
        session_id = create_session(user_id, user, access_token)
    
        return access_token, refresh_token, session_id
    def handle_user_verify(self, data):
        try:
            logger.info("="*60)
            logger.info("NEW VERIFY REQUEST")
            logger.info(f"Request data: {json.dumps(data, indent=2)}")
            
            phone_or_email = data.get('phone_or_email')
            otp = data.get('otp')
            
            if not phone_or_email or not otp:
                logger.warning("VERIFY FAILED: Missing phone_or_email or OTP")
                self._send_response({'error': 'Phone/email and OTP are required'}, 400)
                return

            logger.info(f"Verify attempt for: {phone_or_email} with OTP: {otp}")

            domain = ['&', '|', ('phone', '=', phone_or_email), ('email', '=', phone_or_email), ('active', '=', True)]
            logger.info(f"Searching user with domain: {domain}")
            user_ids = execute_odoo_kw_optimized('res.partner', 'search', [domain])
            logger.info(f"User search result: {user_ids}")
            
            if not user_ids:
                logger.warning(f"VERIFY FAILED: User not found for {phone_or_email}")
                self._send_response({'error': 'User not found'}, 404)
                return
                
            user_id = user_ids[0]
            logger.info(f"User found: ID={user_id}")
            
            user = execute_odoo_kw_optimized('res.partner', 'read', [user_id, ['name', 'phone', 'email']])[0]
            logger.info(f"User details: name={user.get('name')}, phone={user.get('phone')}, email={user.get('email')}")
            
            phone_value = user.get('phone') or (phone_or_email if '@' not in str(phone_or_email) else None)
            sanitized = _sanitize_phone(phone_value)
            logger.info(f"Phone for OTP lookup: {phone_value} -> sanitized: {sanitized}")
            
            if not sanitized:
                logger.error("VERIFY FAILED: Invalid phone number")
                self._send_response({'error': 'User does not have a valid phone number for OTP'}, 400)
                return

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

            current_time = int(time.time())
            refresh_exp  = current_time + (365 * 24 * 3600)  # 365 days

            # Short-lived access token (3 hours)
            access_payload = {
                'user_id': user_id,
                'phone':   user.get('phone'),
                'email':   user.get('email'),
                'name':    user.get('name'),
                'iat':     current_time,
                'exp':     current_time + 10800,
                'type':    'access'
            }

            # Long-lived refresh token (365 days) — includes jti for DB tracking
            refresh_jti = secrets.token_hex(16)
            refresh_payload = {
                'user_id': user_id,
                'iat':     current_time,
                'exp':     refresh_exp,
                'type':    'refresh',
                'jti':     refresh_jti,
            }

            access_token  = jwt.encode(access_payload,  JWT_SECRET, algorithm='HS256')
            refresh_token = jwt.encode(refresh_payload, JWT_SECRET, algorithm='HS256')

            # Persist refresh JTI to Odoo so it survives server restarts
            _store_refresh_token(user_id, refresh_jti, refresh_exp)

            session_id = create_session(user_id, user, access_token)

            self._send_response({
                'success':       True,
                'token':  access_token,
                'refresh_token': refresh_token,
                'session_id':    session_id,
                'user_id':       user_id,
                'data':          user,
                'expires_in':    10800
            }, 200)
        except Exception as e:
            logger.error(f"❌ VERIFY EXCEPTION: {str(e)}", exc_info=True)
            logger.info("="*60)
            self._send_response({'error': f'Verification failed: {str(e)}'}, 500)



    def handle_wait_visit(self, visit_token):
        """
        GET /api/v1/wait-visit/<visit_token>
        SSE endpoint — holds connection open until mobile scans QR or timeout.
        """
        evt = threading.Event()
        with _visit_lock:
            _visit_events[visit_token] = evt

        try:
            self.send_response(200)
            self.send_header("Content-Type",  "text/event-stream")
            self.send_header("Cache-Control", "no-cache")
            self.send_header("Connection",    "keep-alive")
            self.send_header("Access-Control-Allow-Origin", "*")
            self.end_headers()

            deadline = time.monotonic() + VISIT_SSE_TIMEOUT

            while True:
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    try:
                        _sse_write(self, {"timeout": True, "visit_token": visit_token})
                    except (BrokenPipeError, ConnectionResetError):
                        pass  # browser already disconnected — normal
                    break

                wait_secs = min(VISIT_SSE_HEARTBEAT, remaining)
                activated = evt.wait(timeout=wait_secs)

                if activated:
                    with _visit_lock:
                        partner_data = _visit_results.pop(visit_token, {})
                    try:
                        _sse_write(self, {"activated": True, "visit_token": visit_token, **partner_data})
                    except (BrokenPipeError, ConnectionResetError):
                        pass
                    break
                else:
                    try:
                        self.wfile.write(b": heartbeat\n\n")
                        self.wfile.flush()
                    except (BrokenPipeError, ConnectionResetError):
                        break

        finally:
            with _visit_lock:
                _visit_events.pop(visit_token, None)

    def handle_internal_activate_visit(self, data):
        """
        POST /api/v1/internal/activate-visit
        Auth: X-Service-Key == JWT_SECRET
        Body: { "visit_token": "...", "partner_id": 123 }
        """
        try:
            service_key = self.headers.get('X-Service-Key', '')
            if service_key != JWT_SECRET:
                logger.warning("Internal endpoint: wrong service key")
                self._send_response({'error': 'Forbidden'}, 403)
                return

            visit_token = data.get('visit_token')
            partner_id  = data.get('partner_id')
            if not visit_token or not partner_id:
                logger.warning(f"Missing fields: visit_token={visit_token} partner_id={partner_id}")
                self._send_response({'error': 'Missing visit_token or partner_id'}, 400)
                return

            print(f"[STEP 1] token={visit_token} partner_id={partner_id}", flush=True)
            logger.info(f"Internal activate-visit: token={visit_token} partner_id={partner_id}")

            # ── STEP 2: activate via tl_pos_store_visit's activate_visit ─────────
            # This writes qr_state='open' (valid in tl_pos_store_visit's selection).
            # DO NOT use mark_scanned — it writes qr_state='scanned' which does NOT
            # exist in tl_pos_store_visit's redefined qr_state field → ValueError.
            print(f"[STEP 2] Calling activate_visit...", flush=True)
            activated = execute_odoo_kw_optimized(
                'store.visit', 'activate_visit',
                [visit_token, int(partner_id)],
            )
            print(f"[STEP 2 result] activated={activated}", flush=True)

            if not activated:
                logger.warning(f"activate_visit returned False for token={visit_token}")
                self._send_response({
                    'error': 'Visit token not found, already used, or expired.'
                }, 404)
                return

            # activate_visit returns a dict: {visit_id, partner_id, partner_name, first_name, lang}
            # Fall back to a basic dict if old Odoo model returns True instead of dict
            if isinstance(activated, dict):
                partner_data = activated
            else:
                # Old model — fetch partner info manually as fallback
                print(f"[STEP 2b] activate_visit returned True (old model) — reading partner", flush=True)
                try:
                    partner_info = execute_odoo_kw_optimized(
                        'res.partner', 'read',
                        [int(partner_id), ['name', 'phone', 'mobile', 'email', 'lang']],
                    )[0]
                except Exception as e:
                    logger.warning(f"Could not read partner {partner_id}: {e}")
                    partner_info = {}
                partner_data = {
                    'partner_id':   int(partner_id),
                    'partner_name': partner_info.get('name', ''),
                    'first_name':   (partner_info.get('name') or '').split()[0],
                    'lang':         partner_info.get('lang', 'en_US'),
                }

            # ── STEP 3: store result FIRST, then fire SSE ────────────────────────
            # Storing first handles the race where POS SSE opens AFTER activation.
            # handle_wait_visit checks _visit_results on open and fires immediately.
            print(f"[STEP 3] Storing result and firing SSE...", flush=True)
            with _visit_lock:
                _visit_results[visit_token] = partner_data
                evt = _visit_events.get(visit_token)
            if evt:
                evt.set()
                print(f"[STEP 3 OK] SSE fired for token={visit_token}", flush=True)
                logger.info(f"SSE fired for token={visit_token}")
            else:
                print(f"[STEP 3] No SSE waiting — stored for early pickup: token={visit_token}", flush=True)
                logger.info(f"No SSE yet — stored for early pickup: token={visit_token}")

            self._send_response({
                'success':     True,
                'message':     'Visit activated — POS will unlock shortly',
                'visit_token': visit_token,
                **partner_data,
            }, 200)

        except Exception as e:
            logger.error(f"handle_internal_activate_visit failed: {e}", exc_info=True)
            self._send_response({'error': f'Internal error: {str(e)}'}, 500)


    def handle_store_visit(self, data):
        """
        POST /api/v1/store-visit

        MODE A — visit_token present (normal QR scan flow)
        MODE B — no visit_token (legacy / direct check-in)
        """
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

            user_id     = decoded_token['user_id']
            visit_token = data.get('visit_token')

            # ── MODE A: QR scan ───────────────────────────────────────────────────
            if visit_token:
                logger.info(f"Store visit activation: token={visit_token} user_id={user_id}")

                # DO NOT use mark_scanned — writes qr_state='scanned' which crashes.
                # Use activate_visit — writes qr_state='open' which is valid.
                activated = execute_odoo_kw_optimized(
                    'store.visit', 'activate_visit',
                    [visit_token, int(user_id)],
                )

                if not activated:
                    logger.warning(f"activate_visit returned False for token={visit_token}")
                    self._send_response({
                        'error': 'Visit token not found, already used, or expired.'
                    }, 404)
                    return

                if isinstance(activated, dict):
                    partner_data = activated
                else:
                    # Old model fallback
                    try:
                        user_data = execute_odoo_kw_optimized(
                            'res.partner', 'read',
                            [int(user_id), ['name', 'phone', 'email', 'lang']],
                        )[0]
                    except Exception:
                        user_data = {}
                    partner_data = {
                        'partner_id':   int(user_id),
                        'partner_name': user_data.get('name', ''),
                        'first_name':   (user_data.get('name') or '').split()[0],
                        'lang':         user_data.get('lang', 'en_US'),
                    }

                # Store FIRST then fire — handles race where SSE opens after scan
                with _visit_lock:
                    _visit_results[visit_token] = partner_data
                    evt = _visit_events.get(visit_token)
                if evt:
                    evt.set()
                    logger.info(f"SSE fired for token={visit_token}")
                else:
                    logger.info(f"No SSE yet — stored for early pickup: token={visit_token}")

                self._send_response({
                    'success':     True,
                    'message':     'Visit activated — POS will unlock shortly',
                    'visit_token': visit_token,
                    **partner_data,
                }, 200)
                return

            # ── MODE B: legacy direct check-in — only read partner here ──────────
            user_data = execute_odoo_kw_optimized(
                'res.partner', 'read', [int(user_id), ['name', 'phone', 'email']],
            )[0]

            visit_data = {
                'name':      data.get('name',  user_data.get('name',  'Anonymous Visit')),
                'phone':     data.get('phone', user_data.get('phone', '')),
                'email':     data.get('email', user_data.get('email', '')),
                'user_id':   str(user_id),
                'last_name': data.get('last_name', ''),
                'mobile':    data.get('mobile', data.get('phone', user_data.get('phone', ''))),
                'entered':   True,
            }
            if data.get('warehouse_id'):
                visit_data['warehouse_id'] = data['warehouse_id']

            visit_id = execute_odoo_kw_optimized('store.visit', 'create', [visit_data])
            logger.info(f"Store visit created (legacy mode): id={visit_id} user={user_id}")
            self._send_response({
                'success':  True,
                'message':  'Store visit created successfully',
                'visit_id': visit_id,
                'data':     visit_data,
            }, 201)

        except Exception as e:
            logger.error(f"Store visit failed: {str(e)}", exc_info=True)
            self._send_response({'error': f'Store visit failed: {str(e)}'}, 500)

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
                user_data = execute_odoo_kw_optimized('res.partner', 'read', [user_id, ['name', 'phone', 'email', 'last_name', 'vat', 'ref']])[0]
                # print(user_data)
                api_user_data = {
                    'id': user_data['id'],
                    'name': user_data['name'],
                    'phone': user_data['phone'],
                    'email': user_data['email'],
                    'last_name': user_data.get('last_name', ''),
                    'birthday': user_data.get('vat', ''),
                    'identification_id': user_data.get('ref', '')
                }
                
                session_info = {
                    'user_id': user_id,
                    'token_expires': decoded_token['exp'],
                    'issued_at': decoded_token['iat']
                }
                
                logger.info(f"User details retrieved for user ID: {user_id}")
                self._send_response({
                    'success': True,
                    'data': api_user_data,
                    'session_info': session_info
                }, 200)
                
            except Exception as e:
                logger.error(f"Get user details failed: {str(e)}", exc_info=True)
                self._send_response({'error': f'Get user details failed: {str(e)}'}, 500)

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
                    existing_users = execute_odoo_kw_optimized('res.partner', 'search', [[('phone', '=', data['phone']), ('id', '!=', user_id)]])
                    if existing_users:
                        self._send_response({'error': 'Phone number already in use by another user'}, 409)
                        return
                    update_data['phone'] = data['phone']
                if 'email' in data:
                    existing_users = execute_odoo_kw_optimized('res.partner', 'search', [[('email', '=', data['email']), ('id', '!=', user_id)]])
                    if existing_users:
                        self._send_response({'error': 'Email already in use by another user'}, 409)
                        return
                    update_data['email'] = data['email']
                if 'last_name' in data:
                    update_data['last_name'] = data['last_name']
                if 'birthday' in data:
                    update_data['vat'] = data['birthday']
                if 'identification_id' in data:
                    update_data['ref'] = data['identification_id']
                
                if not update_data:
                    self._send_response({'error': 'No valid fields to update'}, 400)
                    return
                
                execute_odoo_kw_optimized('res.partner', 'write', [[user_id], update_data])
                updated_user_data = execute_odoo_kw_optimized('res.partner', 'read', [user_id, ['name', 'phone', 'email', 'last_name', 'vat', 'ref']])[0]
                
                api_updated_data = {
                    'id': updated_user_data['id'],
                    'name': updated_user_data['name'],
                    'phone': updated_user_data['phone'],
                    'email': updated_user_data['email'],
                    'last_name': updated_user_data.get('last_name', ''),
                    'birthday': updated_user_data.get('vat', ''),
                    'identification_id': updated_user_data.get('ref', '')
                }
                
                with active_sessions_lock:
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
                logger.error(f"User update failed: {str(e)}", exc_info=True)
                self._send_response({'error': f'User update failed: {str(e)}'}, 500)

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

                # Revoke refresh token from Odoo DB so it doesn't survive a restart
                _revoke_refresh_token_db(user_id)
                
                logger.info(f"User logged out successfully: {user_id}")
                self._send_response({
                    'success': True,
                    'message': 'Logged out successfully'
                }, 200)
                
            except Exception as e:
                logger.error(f"Logout failed: {str(e)}", exc_info=True)
                self._send_response({'error': f'Logout failed: {str(e)}'}, 500)

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
                with active_sessions_lock:
                    for session_id, session_data in active_sessions.items():
                        sessions_info.append({
                            'session_id': session_id,
                            'user_id': session_data['user_id'],
                            'user_name': session_data['user_data'].get('name', 'Unknown'),
                            'created_at': session_data['created_at'].isoformat(),
                            'last_activity': session_data['last_activity'].isoformat(),
                            'is_current': session_data['token'] == token
                        })
                
                with blacklisted_tokens_lock:
                    blacklist_count = len(blacklisted_tokens)
                
                logger.info(f"Active sessions retrieved by user: {decoded_token['user_id']}")
                self._send_response({
                    'success': True,
                    'active_sessions_count': len(sessions_info),
                    'sessions': sessions_info,
                    'blacklisted_tokens_count': blacklist_count
                }, 200)
                
            except Exception as e:
                logger.error(f"Get active sessions failed: {str(e)}", exc_info=True)
                self._send_response({'error': f'Get active sessions failed: {str(e)}'}, 500)

        def handle_update_user_by_id(self, data, user_id):
            """POST/PUT /api/v1/user/{user_id} - Update user details by their ID."""
            try:
                try:
                    user_id = int(user_id)
                except ValueError:
                    self._send_response({'error': 'Invalid user ID format'}, 400)
                    return
                
                user_exists = execute_odoo_kw_optimized('res.partner', 'search', 
                                                    [[('id', '=', user_id), ('active', '=', True)]], 
                                                    cache_key=f"user_exists_{user_id}")
                if not user_exists:
                    self._send_response({'error': 'User not found'}, 404)
                    return
                
                update_data = {}
                
                if 'name' in data:
                    update_data['name'] = data['name']
                    
                if 'phone' in data:
                    existing_users = execute_odoo_kw_optimized('res.partner', 'search', 
                                                    [[('phone', '=', data['phone']), ('id', '!=', user_id)]])
                    if existing_users:
                        self._send_response({'error': 'Phone number already in use by another user'}, 409)
                        return
                    update_data['phone'] = data['phone']
                    
                if 'email' in data:
                    existing_users = execute_odoo_kw_optimized('res.partner', 'search', 
                                                    [[('email', '=', data['email']), ('id', '!=', user_id)]])
                    if existing_users:
                        self._send_response({'error': 'Email already in use by another user'}, 409)
                        return
                    update_data['email'] = data['email']
                    
                if 'last_name' in data:
                    update_data['last_name'] = data['last_name']
                    
                if 'birthday' in data:
                    update_data['vat'] = data['birthday']
                    
                if 'identification_id' in data:
                    update_data['ref'] = data['identification_id']
                
                if not update_data:
                    self._send_response({'error': 'No valid fields to update'}, 400)
                    return
                
                execute_odoo_kw_optimized('res.partner', 'write', [[user_id], update_data])
                
                updated_user_data = execute_odoo_kw_optimized('res.partner', 'read', 
                                                [user_id, ['name', 'phone', 'email', 'last_name', 'vat', 'ref']])[0]
                
                api_updated_data = {
                    'id': updated_user_data['id'],
                    'name': updated_user_data['name'],
                    'phone': updated_user_data['phone'],
                    'email': updated_user_data['email'],
                    'last_name': updated_user_data.get('last_name', ''),
                    'birthday': updated_user_data.get('vat', ''),
                    'identification_id': updated_user_data.get('ref', '')
                }
                
                # Clear cache
                with cache_lock:
                    cache_key = f"user_exists_{user_id}"
                    cache_data.pop(cache_key, None)
                    cache_timestamps.pop(cache_key, None)
                
                logger.info(f"User {user_id} details updated successfully")
                self._send_response({
                    'success': True,
                    'message': f'User {user_id} updated successfully',
                    'data': api_updated_data
                }, 200)
                
            except Exception as e:
                logger.error(f"Update user by ID failed: {str(e)}", exc_info=True)
                self._send_response({'error': f'Update user by ID failed: {str(e)}'}, 500)
        def handle_token_refresh(self, data):
            """POST /api/v1/user/refresh - Silent token rotation backed by Odoo DB."""
            try:
                refresh_token = data.get('refresh_token')
                if not refresh_token:
                    self._send_response({'error': 'refresh_token is required'}, 400)
                    return

                # --- Decode JWT first (validates signature + expiry) ---
                try:
                    decoded = jwt.decode(refresh_token, JWT_SECRET, algorithms=['HS256'])
                except jwt.ExpiredSignatureError:
                    self._send_response(
                        {'error': 'Refresh token expired', 'sessionExpired': True}, 401
                    )
                    return
                except jwt.InvalidTokenError:
                    self._send_response({'error': 'Invalid refresh token'}, 401)
                    return

                if decoded.get('type') != 'refresh':
                    self._send_response({'error': 'Invalid token type'}, 401)
                    return

                user_id  = decoded['user_id']
                old_jti  = decoded.get('jti', '')

                # --- Validate against Odoo DB (restart-safe) ---
                # If the DB fields aren't installed yet, fall back to JWT-only validation
                # (still safe — signature + expiry are verified by jwt.decode above).
                if old_jti and _is_refresh_db_available():
                    ok, err = _validate_refresh_token_db(user_id, old_jti)
                    if not ok:
                        logger.warning(f"Refresh rejected (DB) for user_id={user_id}: {err}")
                        self._send_response(
                            {'error': err, 'sessionExpired': True}, 401
                        )
                        return
                    logger.info(f"Refresh token validated via DB for user_id={user_id}")
                elif old_jti:
                    # DB not available — JWT signature already verified, proceed
                    logger.warning(
                        f"DB refresh validation skipped (fields not installed) for user_id={user_id}. "
                        "Upgrade hagrocery module to enable restart-safe token validation."
                    )
                else:
                    # Legacy tokens (no jti) — accept once, will get jti on next refresh
                    logger.warning(
                        f"Legacy refresh token (no jti) accepted for user_id={user_id}. "
                        "Will be upgraded to DB-tracked token."
                    )

                # --- Build new token pair ---
                user = execute_odoo_kw_optimized(
                    'res.partner', 'read',
                    [user_id, ['name', 'phone', 'email']]
                )[0]

                current_time = int(time.time())
                new_refresh_exp = current_time + (365 * 24 * 3600)  # 365 days
                new_jti = secrets.token_hex(16)

                new_access_payload = {
                    'user_id': user_id,
                    'phone':   user.get('phone'),
                    'email':   user.get('email'),
                    'name':    user.get('name'),
                    'iat':     current_time,
                    'exp':     current_time + 10800,        # 3 h
                    'type':    'access'
                }
                new_refresh_payload = {
                    'user_id': user_id,
                    'iat':     current_time,
                    'exp':     new_refresh_exp,             # 365 d
                    'type':    'refresh',
                    'jti':     new_jti,
                }

                new_access_token  = jwt.encode(new_access_payload,  JWT_SECRET, algorithm='HS256')
                new_refresh_token = jwt.encode(new_refresh_payload, JWT_SECRET, algorithm='HS256')

                # --- Atomically rotate JTI in Odoo DB (if fields available) ---
                if _is_refresh_db_available():
                    if old_jti:
                        rotated = _rotate_refresh_token_db(user_id, old_jti, new_jti, new_refresh_exp)
                    else:
                        rotated = _store_refresh_token(user_id, new_jti, new_refresh_exp)

                    if not rotated:
                        # Another request already rotated this token — reject to prevent replay
                        self._send_response(
                            {'error': 'Token already rotated, please retry', 'sessionExpired': True}, 401
                        )
                        return
                else:
                    # DB not available — skip rotation, new JWT is still valid on its own
                    logger.warning(f"DB rotation skipped for user_id={user_id} — JWT-only mode")

                # Keep in-memory blacklist as secondary guard (best effort, not required)
                if old_jti:
                    with blacklisted_tokens_lock:
                        blacklisted_tokens.add(refresh_token)

                logger.info(f"Token rotated (DB) for user_id={user_id}")
                self._send_response({
                    'success':       True,
                    'token':  new_access_token,
                    'access_token':  new_access_token,
                    'refresh_token': new_refresh_token,
                }, 200)

            except Exception as e:
                logger.error(f"Token refresh failed: {str(e)}", exc_info=True)
                self._send_response({'error': f'Token refresh failed: {str(e)}'}, 500)

        # Alias — do_POST calls handle_user_refresh, method was misnamed handle_token_refresh
        handle_user_refresh = handle_token_refresh

        def log_message(self, format, *args):
            """Override to add error handling for logging"""
            try:
                super().log_message(format, *args)
            except Exception:
                pass  # Silently ignore logging errors

def run(server_class=http.server.HTTPServer, handler_class=EnhancedApiHandler, port=8001):
    """Start server with error handling"""
    try:
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
        logger.info("   - Thread-safe operations")
        logger.info("   - Fixed mutable defaults bug")
        logger.info("NEW ENDPOINTS AVAILABLE:")
        logger.info("   1. GET /api/v1/user/details - Get authenticated user's details")
        logger.info("   2. POST /api/v1/user/update - Update authenticated user's details")
        logger.info("   3. POST/PUT /api/v1/user/{user_id} - Update user by ID")
        logger.info("   4. POST /api/v1/user/logout - Logout user and invalidate session")
        logger.info("   5. GET /api/v1/user/sessions - Get active sessions")
        logger.info("   6. DELETE /api/v1/user/{user_id} - Soft delete user")
        logger.info("   7. GET /api/v1/user/list - Get user list")
        logger.info("   8. POST /api/v1/store-visit - QR activate (visit_token) or legacy create")

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
        print("   - Thread-safe operations")
        print("   - Fixed mutable defaults bug")
        print("8 ENDPOINTS READY!")
        print("QR GATE: POST /api/v1/store-visit with visit_token → activates via Odoo XML-RPC")
        print("=" * 70)

        httpd.serve_forever()
    except KeyboardInterrupt:
        logger.info("Server shutdown requested")
        print("\nServer shutdown requested")
    except Exception as e:
        logger.error(f"Server failed to start: {str(e)}", exc_info=True)
        print(f"FATAL ERROR: {str(e)}")
        raise

if __name__ == '__main__':
    try:
        run()
    except Exception as e:
        logger.error(f"Fatal error in main: {str(e)}", exc_info=True)
        print(f"FATAL ERROR: {str(e)}")
        import traceback
        traceback.print_exc()