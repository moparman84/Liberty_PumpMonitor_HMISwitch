import hashlib
import json

def hash_password(password):
    return hashlib.sha256(password.encode('utf-8')).hexdigest()

def verify_password(input_password, stored_hash):
    return hash_password(input_password) == stored_hash

# Load config
with open('config.json', 'r') as f:
    config = json.load(f)

# Test password verification
test_password = "LBRT123!"
admin_hash = config['users']['admin']['password_hash']

print(f"Testing password: {test_password}")
print(f"Generated hash: {hash_password(test_password)}")
print(f"Stored hash:    {admin_hash}")
print(f"Password valid: {verify_password(test_password, admin_hash)}")

# Test other common passwords
test_passwords = ["LBRT123!", "admin", "password", "123456", ""]
print("\nTesting various passwords:")
for pwd in test_passwords:
    result = verify_password(pwd, admin_hash)
    print(f"'{pwd}' -> {result}")
