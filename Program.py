import tkinter as tk
from tkinter import *
from flask import Flask, request, session, redirect, url_for, render_template
from flask_mysqldb import MySQL 
import mysql.connector as mysql2
from werkzeug.utils import secure_filename
from multiprocessing import Process
from typing import NamedTuple
import rabbit
from termcolor import colored
from threading import Thread
import time
import socket, sys, threading, time, random, winsound, os
import hashlib
import hashlib as hasher
from hashlib import sha256
from datetime import datetime
from time import strftime
from six.moves import xrange
from math import log
import operator
import numpy,csv,json
import string
import collections
import struct
import binascii
import base64
from copy import copy
from fractions import gcd # Greatest Common Denominator
from random import SystemRandom # cryptographic random byte generator
rand=SystemRandom()
from numpy import asarray
from numpy import save
from numpy import load
import webbrowser
from web3 import Web3
from web3.middleware import geth_poa_middleware
os.system('color A')
# Convert a string with hex digits, colons, and whitespace to a long integer

# Convert a string with hex digits, colons, and whitespace to a long integer
def hex2int(hexString):
	return int("".join(hexString.replace(":","").split()),16)

# Half the extended Euclidean algorithm:
#    Computes   gcd(a,b) = a*x + b*y
#    Returns only gcd, x (not y)
# From http://rosettacode.org/wiki/Modular_inverse#Python
def half_extended_gcd(aa, bb):
	lastrem, rem = abs(aa), abs(bb)
	x, lastx = 0, 1
	while rem:
		lastrem, (quotient, rem) = rem, divmod(lastrem, rem)
		x, lastx = lastx - quotient*x, x
	return lastrem, lastx

# Modular inverse: compute the multiplicative inverse i of a mod m:
#     i*a = a*i = 1 mod m
def modular_inverse(a, m):
	g, x = half_extended_gcd(a, m)
	if g != 1:
		raise ValueError
	return x % m


# An elliptic curve has these fields:
#   p: the prime used to mod all coordinates
#   a: linear part of curve: y^2 = x^3 + ax + b
#   b: constant part of curve
#   G: a curve point (G.x,G.y) used as a "generator"
#   n: the order of the generator
class ECcurve:
	def __init__(self):
		return

	# Prime field multiplication: return a*b mod p
	def field_mul(self,a,b):
		return (a*b)%self.p

	# Prime field division: return num/den mod p
	def field_div(self,num,den):
		inverse_den=modular_inverse(den%self.p,self.p)
		return self.field_mul(num%self.p,inverse_den)

	# Prime field exponentiation: raise num to power mod p
	def field_exp(self,num,power):
		return pow(num%self.p,power,self.p)

	# Return the special identity point
	#   We pick x=p, y=0
	def identity(self):
		return ECpoint(self,self.p,0,1)

	# Return true if point Q lies on our curve

	def touches(self,Q):
		x=Q.get_x()
		y=Q.get_y()
		y2=(y*y)%self.p
		x3ab=(self.field_mul((x*x)%self.p+self.a,x)+self.b)%self.p
		return y2==(x3ab)%self.p

	# Return the slope of the tangent of this curve at point Q
	def tangent(self,Q):
		return self.field_div(Q.x*Q.x*3+self.a,Q.y*2)

	# Return a doubled version of this elliptic curve point
	#  Closely follows Gueron & Krasnov 2013 figure 2
	def double(self,Q):
		if (Q.x==self.p): # doubling the identity
			return Q
		S=(4*Q.x*Q.y*Q.y)%self.p
		Z2=Q.z*Q.z
		Z4=(Z2*Z2)%self.p
		M=(3*Q.x*Q.x+self.a*Z4)
		x=(M*M-2*S)%self.p
		Y2=Q.y*Q.y
		y=(M*(S-x)-8*Y2*Y2)%self.p
		z=(2*Q.y*Q.z)%self.p
		return ECpoint(self,x,y,z)

	# Return the "sum" of these elliptic curve points
	#  Closely follows Gueron & Krasnov 2013 figure 2
	def add(self,Q1,Q2):
		# Identity special cases
		if (Q1.x==self.p): # Q1 is identity
			return Q2
		if (Q2.x==self.p): # Q2 is identity
			return Q1
		Q1z2=Q1.z*Q1.z
		Q2z2=Q2.z*Q2.z
		xs1=(Q1.x*Q2z2)%self.p
		xs2=(Q2.x*Q1z2)%self.p
		ys1=(Q1.y*Q2z2*Q2.z)%self.p
		ys2=(Q2.y*Q1z2*Q1.z)%self.p

		# Equality special cases
		if (xs1==xs2):
			if (ys1==ys2): # adding point to itself
				return self.double(Q1)
			else: # vertical pair--result is the identity
				return self.identity()

		# Ordinary case
		xd=(xs2-xs1)%self.p   # caution: if not python, negative result?
		yd=(ys2-ys1)%self.p
		xd2=(xd*xd)%self.p
		xd3=(xd2*xd)%self.p
		x=(yd*yd-xd3-2*xs1*xd2)%self.p
		y=(yd*(xs1*xd2-x)-ys1*xd3)%self.p
		z=(xd*Q1.z*Q2.z)%self.p
		return ECpoint(self,x,y,z)

	# "Multiply" this elliptic curve point Q by the scalar (integer) m
	#    Often the point Q will be the generator G
	def mul(self,m,Q):
		R=self.identity() # return point
		while m!=0:  # binary multiply loop
			if m&1: # bit is set
				#print("  mul: adding Q to R =",R);
				R=self.add(R,Q)
				#print("  mul: added Q to R =",R);
			m=m>>1
			if (m!=0):
				#print("  mul: doubling Q =",Q);
				Q=self.double(Q)

		return R



# A point on an elliptic curve: (x,y)
#   Using special (X,Y,Z) Jacobian point representation
class ECpoint:
	"""A point on an elliptic curve (x/z^2,y/z^3)"""
	def __init__(self,curve, x,y,z):
		self.curve=curve
		self.x=x
		self.y=y
		self.z=z
		# This self-check has a big performance cost.
		#if not x==curve.p and not curve.touches(self):
		#	print(" ECpoint left curve: ",self)

	# "Add" this point to another point on the same curve
	def add(self,Q2):
		return self.curve.add(self,Q2)

	# "Multiply" this point by a scalar
	def mul(self,m):
		return self.curve.mul(m,self)

	# Extract non-projective X and Y coordinates
	#   This is the only time we need the expensive modular inverse
	def get_x(self):
		return self.curve.field_div(self.x,(self.z*self.z)%self.curve.p);
	def get_y(self):
		return self.curve.field_div(self.y,(self.z*self.z*self.z)%self.curve.p);

	# Print this ECpoint
	def __str__(self):
		if (self.x==self.curve.p):
			return "identity_point"
		else:
			return "("+str(self.get_x())+", "+str(self.get_y())+")"


# This is the BitCoin elliptic curve, SECG secp256k1
#   See http://www.secg.org/SEC2-Ver-1.0.pdf
secp256k1=ECcurve()
secp256k1.p=hex2int("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F");
secp256k1.a=0 # it's a Koblitz curve, with no linear part
secp256k1.b=7

# n is the order of the curve, used for ECDSA
secp256k1.n=hex2int("FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFE BAAEDCE6 AF48A03B BFD25E8C D0364141");

# SEC's "04" means they're representing the generator point's X,Y parts explicitly.
secp256k1.G=ECpoint(curve=secp256k1,
  x = hex2int("79BE667E F9DCBBAC 55A06295 CE870B07 029BFCDB 2DCE28D9 59F2815B 16F81798"),
  y = hex2int("483ADA77 26A3C465 5DA4FBFC 0E1108A8 FD17B448 A6855419 9C47D08F FB10D4B8"),
  z = 1  # projective coordinates, start with Z==1
);

#################
# Test program:
curve=secp256k1
G=curve.G; # generator of curve
n=curve.n; # order of curve
def ECPM(sk):
	pk=G.mul(sk);
	return pk

def encode_public_key(P):
        x = P.get_x().to_bytes(32, "big")
        y = P.get_y().to_bytes(32, "big")
        return b"\x04" + x + y

def decode_public_key(public_key_bytes):
    left = int.from_bytes(public_key_bytes[1:33], byteorder='big')
    right = int.from_bytes(public_key_bytes[33:65], byteorder='big')
    return ECpoint(curve,x=left,y=right,z=1)







def compress_public_key(public_key):
    x, y = public_key.get_x(),public_key.get_y()
    if y % 2 == 0:
        prefix = b"\x02"
    else:
        prefix = b"\x03"
    return (prefix + x.to_bytes(32,'big')).hex()


def decompress_public_key(compressed_public_key):
    compressed_public_key_bytes=bytes.fromhex(compressed_public_key) 
    if len(compressed_public_key_bytes) != 33:
        raise ValueError("Invalid compressed public key")

    prefix = compressed_public_key_bytes[0]
    if prefix not in (2, 3):
        raise ValueError("Invalid compressed public key")

    x = int.from_bytes(compressed_public_key_bytes[1:], byteorder='big')
    y_squared = (x**3 +  7) % curve.p
    y_abs = pow(y_squared, ((curve.p + 1) // 4), curve.p)

    if (prefix == 2 and y_abs & 1 == 1) or (prefix == 3 and y_abs & 1 == 0):
        y = (-y_abs) % curve.p
    else:
        y = y_abs

    return ECpoint(curve,x,y,z=1)

def sign(sk, msg):
	mhash=msg.hex();
	z=int(mhash,16);
	k=rand.getrandbits(256)%n; # message nonce
	C=G.mul(k);
	r=C.get_x()%n; # part 1 of signature
	s=(((z+r*sk)%n)*modular_inverse(k,n))%n; # part 2 of signature
	r=r.to_bytes(32,'big').hex()
	s=s.to_bytes(32,'big').hex()
	sig =r+s
	return sig

def verify(pk, msg,sig):
	mhash=msg.hex();

	z1=int(mhash,16);
	r=int.from_bytes(bytes.fromhex(sig[:64]),byteorder='big')
	s=int.from_bytes(bytes.fromhex(sig[64:]),byteorder='big')
	si=modular_inverse(s,n) # =1/s
	u1=(z1*si)%n  # u1=z/s mod n
	u2=(r*si)%n  # u2=r/s mod n
	C=G.mul(u1).add(pk.mul(u2)); # C = u1 G + u2 Q
	return (r%n==C.get_x()%n)

def hash_sha256(data):
    m= hashlib.sha256()
    m.update(data.encode('UTF'))
    return m.hexdigest()


def ripemd160(x):
    d = hashlib.new("ripemd160")
    d.update(x)
    return d.digest()


def b58(data):
    B58 = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"

    if data[0] == 0:
        return "1" + b58(data[1:])

    x = sum([v * (256 ** i) for i, v in enumerate(data[::-1])])
    ret = ""
    while x > 0:
        ret = B58[x % 58] + ret
        x = x // 58

    return ret

def b58encode(hex_string) :
	alphabet = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'
	''' Return a base58 encoded string from hex string '''
	num = int(hex_string, 16)
	encode = ""
	base_count = len(alphabet)
	while (num > 0) :
		num, res = divmod(num,base_count)
		encode = alphabet[res] + encode
	return encode

def b58decode(v):
	alphabet = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'
	''' Decode a Base58 encoded string as an integer and return a hex string '''
	if not isinstance(v, str):
		v = v.decode('ascii')
	decimal = 0
	for char in v:
		decimal = decimal * 58 + alphabet.index(char)
	return hex(decimal)[2:] # (remove "0x" prefix)

def getAddress(pubkey):
    hash160 = ripemd160(hash_sha256(encode_public_key(pubkey)))
    address = b"\x00" + hash160
    address = b58(address + hash_sha256(hash_sha256(address))[:4])
    return address

def enc_long(n):
    '''Encodes arbitrarily large number n to a sequence of bytes.
    Big endian byte order is used.'''
    s = ""
    while n > 0:
        s = chr(n & 0xFF) + s
        n >>= 8
    return s

WORDSIZE = 0x100000000

rot08 = lambda x: ((x <<  8) & 0xFFFFFFFF) | (x >> 24)
rot16 = lambda x: ((x << 16) & 0xFFFFFFFF) | (x >> 16)

def _nsf(u, v):
    '''Internal non-linear state transition'''
    s = (u + v) % WORDSIZE
    s = s * s
    return (s ^ (s >> 32)) % WORDSIZE

class Rabbit:

    def __init__(self, key, iv = None):
        '''Initialize Rabbit cipher using a 128 bit integer/string'''
        
        if isinstance(key, str):
            # interpret key string in big endian byte order
            if len(key) < 16:
                key = '\x00' * (16 - len(key)) + key
            # if len(key) > 16 bytes only the first 16 will be considered
            k = [ord(key[i + 1]) | (ord(key[i]) << 8)
                 for i in range(14, -1, -2)]
        else:
            # k[0] = least significant 16 bits
            # k[7] = most significant 16 bits
            k = [(key >> i) & 0xFFFF for i in range(0, 128, 16)]
            
        # State and counter initialization
        x = [(k[(j + 5) % 8] << 16) | k[(j + 4) % 8] if j & 1 else
             (k[(j + 1) % 8] << 16) | k[j] for j in range(8)]
        c = [(k[j] << 16) | k[(j + 1) % 8] if j & 1 else
             (k[(j + 4) % 8] << 16) | k[(j + 5) % 8] for j in range(8)]
        
        self.x = x
        self.c = c
        self.b = 0
        self._buf = 0           # output buffer
        self._buf_bytes = 0     # fill level of buffer
        
        next(self)
        next(self)
        next(self)
        next(self)

        for j in range(8):
            c[j] ^= x[(j + 4) % 8]
        
        self.start_x = self.x[:]    # backup initial key for IV/reset
        self.start_c = self.c[:]
        self.start_b = self.b

        if iv != None:
            self.set_iv(iv)

    def reset(self, iv = None):
        '''Reset the cipher and optionally set a new IV (int64 / string).'''
        
        self.c = self.start_c[:]
        self.x = self.start_x[:]
        self.b = self.start_b
        self._buf = 0
        self._buf_bytes = 0
        if iv != None:
            self.set_iv(iv)

    def set_iv(self, iv):
        '''Set a new IV (64 bit integer / bytestring).'''

        if isinstance(iv, str):
            i = 0
            for c in iv:
                i = (i << 8) | ord(c)
            iv = i

        c = self.c
        i0 = iv & 0xFFFFFFFF
        i2 = iv >> 32
        i1 = ((i0 >> 16) | (i2 & 0xFFFF0000)) % WORDSIZE
        i3 = ((i2 << 16) | (i0 & 0x0000FFFF)) % WORDSIZE
        
        c[0] ^= i0
        c[1] ^= i1
        c[2] ^= i2
        c[3] ^= i3
        c[4] ^= i0
        c[5] ^= i1
        c[6] ^= i2
        c[7] ^= i3

        next(self)
        next(self)
        next(self)
        next(self)
        

    def __next__(self):
        '''Proceed to the next internal state'''
        
        c = self.c
        x = self.x
        b = self.b

        t = c[0] + 0x4D34D34D + b
        c[0] = t % WORDSIZE
        t = c[1] + 0xD34D34D3 + t // WORDSIZE
        c[1] = t % WORDSIZE
        t = c[2] + 0x34D34D34 + t // WORDSIZE
        c[2] = t % WORDSIZE
        t = c[3] + 0x4D34D34D + t // WORDSIZE
        c[3] = t % WORDSIZE
        t = c[4] + 0xD34D34D3 + t // WORDSIZE
        c[4] = t % WORDSIZE
        t = c[5] + 0x34D34D34 + t // WORDSIZE
        c[5] = t % WORDSIZE
        t = c[6] + 0x4D34D34D + t // WORDSIZE
        c[6] = t % WORDSIZE
        t = c[7] + 0xD34D34D3 + t // WORDSIZE
        c[7] = t % WORDSIZE
        b = t // WORDSIZE
        
        g = [_nsf(x[j], c[j]) for j in range(8)]
        
        x[0] = (g[0] + rot16(g[7]) + rot16(g[6])) % WORDSIZE
        x[1] = (g[1] + rot08(g[0]) + g[7]) % WORDSIZE
        x[2] = (g[2] + rot16(g[1]) + rot16(g[0])) % WORDSIZE
        x[3] = (g[3] + rot08(g[2]) + g[1]) % WORDSIZE
        x[4] = (g[4] + rot16(g[3]) + rot16(g[2])) % WORDSIZE
        x[5] = (g[5] + rot08(g[4]) + g[3]) % WORDSIZE
        x[6] = (g[6] + rot16(g[5]) + rot16(g[4])) % WORDSIZE
        x[7] = (g[7] + rot08(g[6]) + g[5]) % WORDSIZE
        
        self.b = b
        return self


    def derive(self):
        '''Derive a 128 bit integer from the internal state'''
        
        x = self.x
        return ((x[0] & 0xFFFF) ^ (x[5] >> 16)) | \
               (((x[0] >> 16) ^ (x[3] & 0xFFFF)) << 16)| \
               (((x[2] & 0xFFFF) ^ (x[7] >> 16)) << 32)| \
               (((x[2] >> 16) ^ (x[5] & 0xFFFF)) << 48)| \
               (((x[4] & 0xFFFF) ^ (x[1] >> 16)) << 64)| \
               (((x[4] >> 16) ^ (x[7] & 0xFFFF)) << 80)| \
               (((x[6] & 0xFFFF) ^ (x[3] >> 16)) << 96)| \
               (((x[6] >> 16) ^ (x[1] & 0xFFFF)) << 112)

    
    def keystream(self, n):
        '''Generate a keystream of n bytes'''
        
        res = ""
        b = self._buf
        j = self._buf_bytes
        next = self.__next__
        derive = self.derive
        
        for i in range(n):
            if not j:
                j = 16
                next()
                b = derive()
            res += chr(b & 0xFF)
            j -= 1
            b >>= 1

        self._buf = b
        self._buf_bytes = j
        return res


    def encrypt(self, data):
        '''Encrypt/Decrypt data of arbitrary length.'''
        
        res = ""
        b = self._buf
        j = self._buf_bytes
        next = self.__next__
        derive = self.derive

        for c in data:
            if not j:   # empty buffer => fetch next 128 bits
                j = 16
                next()
                b = derive()
            res += chr(ord(c) ^ (b & 0xFF))
            j -= 1
            b >>= 1
        self._buf = b
        self._buf_bytes = j
        return res

    decrypt = encrypt


    



quorum_url = "http://localhost:22000"

web3 = Web3(Web3.HTTPProvider(quorum_url))
web3.middleware_onion.inject(geth_poa_middleware, layer=0)
# # set pre-funded account as sender
web3.eth.defaultAccount = Web3.toChecksumAddress('0xed9d02e382b34818e88b88a309c7fe71e65f419d')
sk=hex2int("1be3b50b31734be48452c29d714941ba165ef0cbf3ccea8ca16c45e3d8d45fb0")
pk=compress_public_key(ECPM(sk))


# # Create the contract instance with the newly-deployed address
contract = web3.eth.contract(
    address=Web3.toChecksumAddress('0x1932c48b2bf8102ba33b4a6b545c32236e342f34'),
    abi=json.loads('[{"anonymous":false,"name":"newDataAdded","inputs":[{"indexed":false,"name":"_tx_index","type":"uint256","internalType":"uint256"},{"indexed":false,"name":"_cid","type":"string","internalType":"string"},{"indexed":false,"name":"_timestamp","type":"string","internalType":"string"}],"type":"event","payable":false},{"constant":false,"name":"SensorDataList","inputs":[{"name":"","type":"uint256","internalType":"uint256"}],"outputs":[{"name":"","type":"string","internalType":"string"}],"type":"function","payable":false,"stateMutability":"view"},{"constant":false,"name":"countTx","inputs":[],"outputs":[{"name":"","type":"uint256","internalType":"uint256"}],"type":"function","payable":false,"stateMutability":"view"},{"constant":false,"name":"getData","inputs":[{"name":"_cid","type":"string","internalType":"string"}],"outputs":[{"name":"","type":"uint256","internalType":"uint256"},{"name":"","type":"string","internalType":"string"},{"name":"","type":"string","internalType":"string"},{"name":"","type":"string","internalType":"string"},{"name":"","type":"bytes","internalType":"bytes"},{"name":"","type":"bytes","internalType":"bytes"}],"type":"function","payable":false,"stateMutability":"view"},{"constant":false,"name":"newData","inputs":[{"name":"_tx_index","type":"uint256","internalType":"uint256"},{"name":"_cid","type":"string","internalType":"string"},{"name":"_url","type":"string","internalType":"string"},{"name":"_timestamp","type":"string","internalType":"string"},{"name":"_signature","type":"bytes","internalType":"bytes"},{"name":"_public_key","type":"bytes","internalType":"bytes"}],"outputs":[],"type":"function","payable":false,"stateMutability":"nonpayable"}]'),
)

def countTxEntry():
    # # Display the new greeting value
    return contract.functions.countTx().call()

def data_upload(filepath):
    print("\nFile/Folder upload")
    #upload
    #Write timestamp into ipfs-hashes.csv
    with open("IPFS-Hashes.csv", "a") as fin:
        fin.write(str(datetime.now()) + " ")
    #Write file/foldername into ipfs-hashes.csv
    command = "ipfs add -r " + filepath + " >> IPFS-Hashes.csv"
    os.system(command)
    print("The data was uploades to IPFS. The hash and the file/foldername")
    print("are printed to the end of 'IPFS-Hashes.csv'")


def data_download(cid):
    print("\nDownload file/folder")
    #download
    command = "ipfs get " + cid
    os.system(command)
    print("The data with the hash")
    print(cid)
    print("was downloaded.")

class Struct(NamedTuple):
    tx_index:int
    cid:str
    url:str
    timestamp:str
    signature:bytes
    public_key:bytes

class Client(tk.Frame):
    def __init__(self,master=None):
        tk.Frame.__init__(self,master)
        self.master.minsize(900,500)
        self.grid(sticky = tk.N + tk.S + tk.E + tk.W)
        self.master.rowconfigure(0,weight=1)
        self.master.columnconfigure(0,weight=1)
        self.master.protocol("WM_DELETE_WINDOW", self.on_closing)
        self.createWidgets()
        self.selectedUser=None
        self.master.title("Developer: Muhammad Mainul Islam, iBEL, Korea University, Seoul, South Korea.")
        self.ucho= Hear(self);
        self.ucho.start()

        
    def lastTx(self, Tx_index):
        self.chatBox.insert(tk.END,
		"\n\n**************************************************************************************")
        self.chatBox.insert(tk.END,
             "\n Tx Index: "+str(Tx_index))
             # "\n CID: "+str(transactions[1])+
             # "\n URL: "+str(transactions[2])+
             # "\n Timestamp: "+str(transactions[3])+
             # "\n Signature: "+str(transactions[4])+
             # "\n Public Key: "+str(transactions[5]))		 
        # self.chatBox.see(tk.END)
        self.chatBox.insert(tk.END,
		"\n**************************************************************************************")


      
    def createWidgets(self):
        global UTXO, input, receiving_bank, reference
        self.chatFrame= tk.Frame(self)
        self.chatFrame.grid(row = 0, column = 0, rowspan=10,sticky = tk.S+tk.N+tk.E+tk.W)
        self.chatBox= tk.Text(self.chatFrame, height=30, bg='white',fg='blue' ,font=("Courier", 10))
        self.chatBox.grid(row = 0, column = 0,sticky = tk.S+tk.N+tk.E+tk.W)
        self.chatBox.bind("<Key>", lambda e: "break")
        self.sscr=tk.Scrollbar(self.chatFrame)
        self.sscr.grid(column=1, row=0,sticky=tk.N + tk.S + tk.W + tk.E)
        self.chatBox.config(yscrollcommand=self.sscr.set)
        self.sscr.config(command=self.chatBox.yview)
        self.chatFrame.columnconfigure(0,weight=1)
        self.chatFrame.rowconfigure(0,weight=1)
		


        self.sendButton = tk.Button(self, text="Clean Window",bg='blue',fg='white')
        self.sendButton.myName = "Clean Window"
        self.sendButton.grid(row = 14, column = 0, sticky = tk.N+tk.S+tk.E+tk.W)
        self.sendButton.bind("<Button-1>" , self.clean)

		
        self.exitButton = tk.Button(self, text="Exit", bg='red',fg='white')
        self.exitButton.myName = "Exit Button"
        self.exitButton.grid(row=14,column=1, sticky = tk.N+tk.S+tk.E+tk.W)
        self.exitButton.bind("<Button-1>" , self.exit)
        self.master.bind_all("<Return>", self.clean)
        for i in range(15):
            self.rowconfigure(i,weight=1) 
        self.columnconfigure(0,weight=3)
        self.columnconfigure(1, weight=1)
    def handler(self, event):
        pass
 			
    def exit(self,event):
        self.master.destroy()
    def on_closing(self):
        if tk.messagebox.askokcancel("Quit", "Do you want to quit?"):
            self.exit(None)
    def clean(self,event):
        self.chatBox.delete("0.0",tk.END)









class Hear(threading.Thread):
    def __init__(self,root):
        self.root=root
        self.status=True
        super().__init__(daemon=True)

    def run(self):
        length=0
        Tx_index=0
        while True:
            with open('LoraData.csv', newline='') as csvfile:
                data=list(csv.reader(csvfile))
            loradata=data[1:]
            if len(loradata)-length>=160:
                start_time0=time.time()
                data=loradata[length:length+160]
	            #Symmetric Encryption
                M=str(data)
                start_time1=time.time()
                H=Rabbit(enc_long(sk)).encrypt(M).encode().hex()
                encryption_time=time.time()-start_time1
	           # print("Ciphertext: ", H)
                encrypted_data={}
                encrypted_data['Tx Index']=Tx_index
                encrypted_data['About']="LoRa Sensor Data"
                encrypted_data['Type']="Encrypted"
                encrypted_data['Ciphertext']=H
                filepath="Tx"+str(Tx_index)+".json"
                with open(filepath, 'w') as outfile:
                    json.dump(encrypted_data, outfile)
                timestamp=str(datetime.now())
                with open("IPFS-Hashes.csv", "a") as fin:
                    fin.write( timestamp + " ")
                #Write file/foldername into ipfs-hashes.csv
                start_time2=time.time()
                command = "ipfs add -r " + filepath + " >> IPFS-Hashes.csv"
                res=os.system(command)
                ipfs_adding_time=time.time()-start_time2
                with open('IPFS-Hashes.csv', 'r') as file:
                    rows= list(csv.reader(file))
                CID=rows[-1][0].split()[3]
                Tx=[Tx_index,CID,"http://ipfs.io/ipfs/"+str(CID),timestamp]
                datahash=bytes.fromhex(hash_sha256(str(Tx)))    
                signature=bytes.fromhex(sign(sk,datahash)) 
                public_key=bytes.fromhex(pk)
                URL="http://ipfs.io/ipfs/"+str(CID)
                data=Struct(Tx_index,CID,URL,timestamp,signature,public_key)
                start_time3=time.time()
                tx_hash = contract.functions.newData(data.tx_index,data.cid,data.url,data.timestamp,data.signature,data.public_key).transact()
                # # Wait for transaction to be mined...
                web3.eth.waitForTransactionReceipt(tx_hash)
                consensus_time=time.time()-start_time3
                elapsed_time=time.time()-start_time0
                print("Transaction-",Tx_index)
                print("Encryption time: ", encryption_time)
                print("Elapsed time to add object to IPFS: ", ipfs_adding_time)
                print("Elapsed time to execute consensus: ", consensus_time)
                print("Total time to make transaction : ", elapsed_time)
                length=length+160
                Tx_index=Tx_index+1
                Tx=Tx+[b58encode(signature.hex()),pk]
                self.root.lastTx(Tx)				
clientApp = Client()
clientApp.mainloop()
