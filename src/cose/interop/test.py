import subprocess
from pycose.keys import OKPKey
from pycose.messages import Sign1Message
from pycose.headers import Algorithm, ContentType
from pycose.algorithms import EdDSA
import cbor2

print('Generating random key')
key = OKPKey.generate_key('ed25519')

open('message.privkey', 'wb').write(key.encode())

# pycose doesn't support public key exports yet
cose_pubkey = cbor2.dumps({1: 1, -1: 6, -2: key.x})
open('message.pubkey', 'wb').write(cose_pubkey)

payload = b'payload'
open('message.data', 'wb').write(payload)

print('Running ./signtest.exe')
subprocess.check_call(['./signtest.exe', 'message.data', 'message.privkey', 'message.cbor'])

msg = Sign1Message.decode(open('message.cbor', 'rb').read())

msg.key = key
assert msg.verify_signature()
assert msg.payload == b'payload', msg.payload
assert msg.external_aad == b'', msg.aad
print('Signature verifies!')

print('Running ./verifytest.exe')
verify = subprocess.run(['./verifytest.exe', 'message.pubkey', 'message.cbor'], stdout=subprocess.PIPE)
verify.check_returncode()
assert verify.stdout == payload, verify.stdout
print('Signature verifies using our tool!')



print('Signing with pycose')
# Setting some extra headers, otherwise the signed message is bitwise identical to the one we're producing
msg2 = Sign1Message(phdr={Algorithm: EdDSA}, uhdr={ContentType: 'text/plain'}, payload=payload)
msg2.key = key
open('message.pycose.cbor', 'wb').write(msg2.encode())

print('Running ./verifytest.exe')
verify = subprocess.run(['./verifytest.exe', 'message.pubkey', 'message.pycose.cbor'], stdout=subprocess.PIPE)
verify.check_returncode()
assert verify.stdout == payload, verify.stdout
print('PyCOSE Signature verifies using our tool!')
