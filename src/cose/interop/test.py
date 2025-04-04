import subprocess
from pycose.keys import OKPKey, CoseKey
from pycose.messages import Sign1Message
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric import ed25519

print('Generating random key')

privkey = ed25519.Ed25519PrivateKey.generate()
open('message.privkey', 'wb').write(
    privkey.private_bytes(
        encoding=serialization.Encoding.DER,
        format=serialization.PrivateFormat.PKCS8,
        encryption_algorithm=serialization.NoEncryption(),
    ),
)

key = CoseKey._from_cryptography_key(privkey)

payload = b'payload'
open('message.data', 'wb').write(payload)

print('Running ./signtest')
subprocess.check_call(['./signtest', 'message.data', 'message.privkey', 'message.cbor'])

msg = Sign1Message.decode(open('message.cbor', 'rb').read())

msg.key = key
assert msg.verify_signature()
assert msg.payload == b'payload', msg.payload
assert msg.external_aad == b'', msg.aad
print('Signature verifies!')
