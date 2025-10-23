import hashlib

def hash_password(password):
    return hashlib.sha256(password.encode('utf-8')).hexdigest()

# Test the hash for LBRT123!
test_password = "LBRT123!"
generated_hash = hash_password(test_password)
config_hash = "640cbd95ca7266f30b4fd317d5f59998c2b975581666dfb6574b9b923c735658"

print(f"Password: {test_password}")
print(f"Generated hash: {generated_hash}")
print(f"Config hash:    {config_hash}")
print(f"Hashes match: {generated_hash == config_hash}")
