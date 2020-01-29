#####################################################
# GA17 Privacy Enhancing Technologies -- Lab 01
#
# Basics of Petlib, encryption, signatures and
# an end-to-end encryption system.
#
# Run the tests through:
# $ py.test-2.7 -v Lab01Tests.py 

###########################
# Group Members: Kamil Zajac
###########################


#####################################################
# TASK 1 -- Ensure petlib is installed on the System
#           and also pytest. Ensure the Lab Code can 
#           be imported.

import petlib

#####################################################
# TASK 2 -- Symmetric encryption using AES-GCM 
#           (Galois Counter Mode)
#
# Implement a encryption and decryption function
# that simply performs AES_GCM symmetric encryption
# and decryption using the functions in petlib.cipher.

from os import urandom
from petlib.cipher import Cipher

def encrypt_message(K, message):
    """ Encrypt a message under a key K """

    plaintext = message.encode("utf8")
    
    ## YOUR CODE HERE
    aes = Cipher("aes-128-gcm")
    iv = urandom(16)

    # Perform encryption 
    ciphertext, tag = aes.quick_gcm_enc(K, iv, plaintext)

    return (iv, ciphertext, tag)

def decrypt_message(K, iv, ciphertext, tag):
    """ Decrypt a cipher text under a key K 

        In case the decryption fails, throw an exception.
    """

    ## YOUR CODE HERE
    aes = Cipher("aes-128-gcm")

    # Perform decryption
    try:
 	plain = aes.quick_gcm_dec(K, iv, ciphertext, tag)
    except:
	raise RuntimeError("decryption failed")

    return plain.encode("utf8")

#####################################################
# TASK 3 -- Understand Elliptic Curve Arithmetic
#           - Test if a point is on a curve.
#           - Implement Point addition.
#           - Implement Point doubling.
#           - Implement Scalar multiplication (double & add).
#           - Implement Scalar multiplication (Montgomery ladder).
#
# MUST NOT USE ANY OF THE petlib.ec FUNCIONS. Only petlib.bn!

from petlib.bn import Bn

def is_point_on_curve(a, b, p, x, y):
    """
    Check that a point (x, y) is on the curve defined by a,b and prime p.
    Reminder: an Elliptic Curve on a prime field p is defined as:

              y^2 = x^3 + ax + b (mod p)
                  (Weierstrass form)

    Return True if point (x,y) is on curve, otherwise False.
    By convention a (None, None) point represents "infinity".
    """
    assert isinstance(a, Bn)
    assert isinstance(b, Bn)
    assert isinstance(p, Bn) and p > 0
    assert (isinstance(x, Bn) and isinstance(y, Bn)) \
           or (x == None and y == None)

    # Edited the code here, '==' is changed to 'is'
    if x is None and y is None:
       return True

    lhs = (y * y) % p
    rhs = (x*x*x + a*x + b) % p
    on_curve = (lhs == rhs)

    return on_curve


def point_add(a, b, p, x0, y0, x1, y1):
    """Define the "addition" operation for 2 EC Points.

    Reminder: (xr, yr) = (xq, yq) + (xp, yp)
    is defined as:
        lam = (yq - yp) * (xq - xp)^-1 (mod p)
        xr  = lam^2 - xp - xq (mod p)
        yr  = lam * (xp - xr) - yp (mod p)

    Return the point resulting from the addition. Raises an Exception if the points are equal.
    """

    # ADD YOUR CODE BELOW

    # Handle cases where points are infinity
    if (x0 is None and y0 is None):
        return x1, y1
    elif (x1 is None and y1 is None):
	return x0, y0

    # Handle cases where points are equal
    if (x0 == x1) and (y0 == y1):
        raise Exception("EC Points must not be equal")

    # Calculate the addition
    # lam = (yq - yp) * (xq - xp)^-1 (mod p)
    dy = y0 - y1
    dx = x0 - x1
    try: 
        idx = dx.mod_inverse(p)
    except:
        return None, None
  
    # lam = (dy * idx).mod(p)
    lam = dy * idx 

    # xr  = lam^2 - xp - xq (mod p)
    lamsq = lam.pow(2)
    temp = lamsq - x0 - x1
    xr = temp.mod(p)

    # yr  = lam * (xp - xr) - yp (mod p)
    temp = x0 - xr
    calc = lam * temp - y0
    yr = calc.mod(p)
    
    return xr, yr

def point_double(a, b, p, x, y):
    """Define "doubling" an EC point.
     A special case, when a point needs to be added to itself.

     Reminder:
        lam = (3 * xp ^ 2 + a) * (2 * yp) ^ -1 (mod p)
        xr  = lam ^ 2 - 2 * xp
        yr  = lam * (xp - xr) - yp (mod p)

    Returns the point representing the double of the input (x, y).
    """  

    if x is None or y is None:
        return None, None

    # ADD YOUR CODE BELOW
    # Perform calculation using Bn functions
    fhalf = 3 * x.pow(2) + a
    shalf = (2 * y).mod_inverse(p)

    lam = fhalf * shalf

    xr = (lam.pow(2) - 2 * x).mod(p)
    yr = (lam * (x - xr) - y).mod(p)

    return xr, yr

def point_scalar_multiplication_double_and_add(a, b, p, x, y, scalar):
    """
    Implement Point multiplication with a scalar:
        r * (x, y) = (x, y) + ... + (x, y)    (r times)

    Reminder of Double and Multiply algorithm: r * P
        Q = infinity
        for i = 0 to num_bits(P)-1
            if bit i of r == 1 then
                Q = Q + P
            P = 2 * P
        return Q

    """
    Q = (None, None)
    P = (x, y)

    for i in range(scalar.num_bits()):
        # CODE ADDED HERE
        # Check bits and act accordingly 
        if scalar.is_bit_set(i):
            Q = point_add(a, b, p, Q[0], Q[1], P[0], P[1])
        P = point_double(a, b, p, P[0], P[1])

    return Q

def point_scalar_multiplication_montgomerry_ladder(a, b, p, x, y, scalar):
    """
    Implement Point multiplication with a scalar:
        r * (x, y) = (x, y) + ... + (x, y)    (r times)

    Reminder of Double and Multiply algorithm: r * P
        R0 = infinity
        R1 = P
        for i in num_bits(P)-1 to zero:
            if di = 0:
                R1 = R0 + R1
                R0 = 2R0
            else
                R0 = R0 + R1
                R1 = 2 R1
        return R0

    """
    R0 = (None, None)
    R1 = (x, y)

    for i in reversed(range(0,scalar.num_bits())):
        # CODE ADDED HERE
        # Check bits and act accordingly 
        if not scalar.is_bit_set(i):
            R1 = point_add(a, b, p, R0[0], R0[1], R1[0], R1[1])
            R0 = point_double(a, b, p, R0[0], R0[1])
        else:
            R0 = point_add(a, b, p, R0[0], R0[1], R1[0], R1[1])
            R1 = point_double(a, b, p, R1[0], R1[1])

    return R0


#####################################################
# TASK 4 -- Standard ECDSA signatures
#
#          - Implement a key / param generation 
#          - Implement ECDSA signature using petlib.ecdsa
#          - Implement ECDSA signature verification 
#            using petlib.ecdsa

from hashlib import sha256
from petlib.ec import EcGroup
from petlib.ecdsa import do_ecdsa_sign, do_ecdsa_verify

def ecdsa_key_gen():
    """ Returns an EC group, a random private key for signing 
        and the corresponding public key for verification"""
    G = EcGroup()
    priv_sign = G.order().random()
    pub_verify = priv_sign * G.generator()
    return (G, priv_sign, pub_verify)


def ecdsa_sign(G, priv_sign, message):
    """ Sign the SHA256 digest of the message using ECDSA and return a signature """
    plaintext =  message.encode("utf8")

    ## YOUR CODE HERE
    digest = sha256(plaintext).digest()

    # Sign the digest
    sig = do_ecdsa_sign(G, priv_sign, digest)

    return sig

def ecdsa_verify(G, pub_verify, message, sig):
    """ Verify the ECDSA signature on the message """
    plaintext =  message.encode("utf8")

    ## YOUR CODE HERE
    digest = sha256(plaintext).digest()

    # Verify signature 
    res = do_ecdsa_verify(G, pub_verify, sig, digest)

    return res

#####################################################
# TASK 5 -- Diffie-Hellman Key Exchange and Derivation
#           - use Bob's public key to derive a shared key.
#           - Use Bob's public key to encrypt a message.
#           - Use Bob's private key to decrypt the message.
#
# NOTE: 

def dh_get_key():
    """ Generate a DH key pair """
    G = EcGroup()
    priv_dec = G.order().random()
    pub_enc = priv_dec * G.generator()
    return (G, priv_dec, pub_enc)


def dh_encrypt(pub, message, aliceSig = None):
    """ Assume you know the public key of someone else (Bob), 
    and wish to Encrypt a message for them.
        - Generate a fresh DH key for this message.
        - Derive a fresh shared key.
        - Use the shared key to AES_GCM encrypt the message.
        - Optionally: sign the message with Alice's key.
    """
    
    ## YOUR CODE HERE

    # pub is Q_B = d_B G
    # we generate Q_A = d_A G
    # if we send Q_A, recipient calculates d_B Q_A = d_A d_B G
    # we can calculate d_A Q_B = d_A d_B G
    # shared key is x coord of d_A d_B G

    # Generate a fresh public key
    G, priv, public = dh_get_key()

    # Use private part of key to generate shared key
    # - scalar multiplication instead of exponentiation
    ''' Multiply the private part by Bob's public key '''
    secret = pub.pt_mul(priv)
    x, y = secret.get_affine()
    shared = x.binary()[:24]

    # Perform encryption with shared key
    plaintext = message.encode("utf8")
    aes = Cipher("aes-192-gcm")
    iv = urandom(16)
    ciphertext, tag = aes.quick_gcm_enc(shared, iv, plaintext)

    # Send fresh public key, output of AEAD and possibly signatures
    return (public, iv, ciphertext, tag)


def dh_decrypt(priv, ciphertext, aliceVer = None):
    """ Decrypt a received message encrypted using your public key, 
    of which the private key is provided. Optionally verify 
    the message came from Alice using her verification key."""
    
    ## YOUR CODE HERE
    pub = ciphertext[0]
    iv = ciphertext[1]
    tag = ciphertext[3]

    # We want d_B Q_A = d_A d_B G, to use as shared key
    secret = pub.pt_mul(priv)
    x, y = secret.get_affine()
    shared = x.binary()[:24]

    # Perform decryption with shared key
    aes = Cipher("aes-192-gcm")
    try:
 	plain = aes.quick_gcm_dec(shared, iv, ciphertext[2], tag)
    except:
	raise RuntimeError("decryption failed")
    return plain.encode("utf8")

## NOTE: populate those (or more) tests
#  ensure they run using the "py.test filename" command.
#  What is your test coverage? Where is it missing cases?
#  $ py.test-2.7 --cov-report html --cov Lab01Code Lab01Code.py 

def test_encrypt():
    msg = u"Hello World"
    G, priv, pub = dh_get_key()

    # Perform encryption with given public key
    public, iv, ciphertext, tag = dh_encrypt(pub, msg)

    # Validate outputs
    assert len(ciphertext) == len(msg)
    assert len(iv) == 16
    assert len(tag) == 16

def test_decrypt(): 
    msg = u"Hello World"
    G, priv, pub = dh_get_key()

    # Perform encryption with given public key
    public, iv, ciphertext, tag = dh_encrypt(pub, msg)

    # Validate outputs
    assert len(ciphertext) == len(msg)
    assert len(iv) == 16
    assert len(tag) == 16

    # Perform decryption with given private key and encryption output
    m = dh_decrypt(priv, (public, iv, ciphertext, tag))
    assert m == msg

def test_fails():

    # For checking exception messages, as used in the test script
    from pytest import raises
    msg = u"Hello World"
    G, priv, pub = dh_get_key()

    # Perform encryption with given public key
    public, iv, ciphertext, tag = dh_encrypt(pub, msg)

    # Using the wrong private key
    with raises(Exception) as excinfo:
        G_, priv_, pub_ = dh_get_key()
        dh_decrypt(priv_, (public, iv, ciphertext, tag))
    assert 'decryption failed' in str(excinfo.value)

    # Using the wrong public key
    with raises(Exception) as excinfo:
        dh_decrypt(priv, (pub, iv, ciphertext, tag))
    assert 'decryption failed' in str(excinfo.value)


    # Using incorrect outputs of encryption
    with raises(Exception) as excinfo:
        dh_decrypt(priv, (public, urandom(len(iv)), ciphertext, tag))
    assert 'decryption failed' in str(excinfo.value)

    with raises(Exception) as excinfo:
        dh_decrypt(priv, (public, iv, urandom(len(ciphertext)), tag))
    assert 'decryption failed' in str(excinfo.value)

    with raises(Exception) as excinfo:
        dh_decrypt(priv, (public, iv, ciphertext, urandom(len(tag))))
    assert 'decryption failed' in str(excinfo.value)


#####################################################
# TASK 6 -- Time EC scalar multiplication
#             Open Task.
#           
#           - Time your implementations of scalar multiplication
#             (use time.clock() for measurements)for different 
#              scalar sizes)
#           - Print reports on timing dependencies on secrets.
#           - Fix one implementation to not leak information.

def time_scalar_mul():
    pass
