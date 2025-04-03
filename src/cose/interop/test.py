import subprocess
from pycose.keys import CoseKey
from pycose.messages import Sign1Message
from cryptography.hazmat.primitives.serialization import load_der_private_key

print('Running ./signtest')
subprocess.run(['./signtest'])

key = CoseKey._from_cryptography_key(load_der_private_key(open('message.key', 'rb').read(), password=None))
msg = Sign1Message.decode(open('message.cbor', 'rb').read())

msg.key = key
assert msg.verify_signature()
assert msg.payload == b'payload', msg.payload
assert msg.external_aad == b'', msg.aad
print('Signature verifies!')
