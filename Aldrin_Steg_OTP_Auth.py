#!/usr/bin/python3

import os, random
import os.path
from os import listdir
from os.path import isfile, join
import time
import cv2
import docopt
import numpy as np
from Crypto.Cipher import AES
from Crypto.Hash import SHA256
from Crypto import Random
from PIL import Image
import glob
import numpy
# import Image and the graphics package Tkinter
import tkinter
from tkinter import *
import tkinter as tk
from PIL import Image, ImageTk
from tkinter.ttk import Frame, Button, Style
import uuid
import pyautogui, time




'''
Date: 05/04/2018
Student Name: Aldrin Wilfred Arokiasamy
Supervisor: Prof. dr hab. inż. Władysław Skarbek

"Deep Learning for Multimedia Security System" - Part 1
Code for Conference (Thesis) Work

Short Description:
This program includes a scripts to build a password to login and if the password matches,
the stegnography session opens up. The script asks for the source image(directory)(using PNG format images),
destination directory and then the text to be encoded is the information given by the user.

Then the decryption phase involves decryption(stegnography)....

LSB:
The bits of this secret file are embedded in the bits of the cover image by modifying the content of
the least significant bit, in the case of the LSB Algorithm. In the Lowest Significant Bit algorithm,
the information is hidden in the last bits of the pixels in the cover image..
Why?
As we can consider them as the noise. These changes are not viable to be detected by the normal eye.
A change in the LSB of a pixel is evidenced by minor changes in the intensity of the colors.

The following code demonstrates the working of The Code for Conference (Thesis) Work.
ConfThesis_PhaseOne.py

Registration Stage:
1. The user has to provide details
2. The user has to provide desired image
3. The user details will be embedded on to the image
4. The pin will be sent to the user through post/mail

Login Stage:
1. The user have to provide the pin along with details given at the time of registration
2. The user will be provides with the random image(may be the desired image, involving security)
3. At that time the user will obtain an OTP
4. The user has to provide the OTP to the login system
5. If the OTP given and teh OTP sent were the same, and if the image is the users desired image,
   the user will be given the login session

'''



with open('name.txt',"w") as name:
    input0 = str(input("Customer Name: "))
    name.write(input0)

with open('ID.txt',"w") as Cid:
    input1 = (input("Customer ID: "))
    Cid.write(input1)




#with open('DPass.txt',"w") as DPass:
 #   input2 = (input("Desired Password: "))
  #  DPass.write(input2)



    
#Defining the class
class Project():
    
    def __init__(self, im):
        self.image = im
        self.height, self.width, self.nbchannels = im.shape
        #(600, 600, 3)
        self.size = self.width*self.height
        #360000

        #Mask used to set bits:1->00000001, 2->00000010 ... (using OR gate)
        self.maskONEValues = [1<<0, 1<<1, 1<<2, 1<<3, 1<<4, 1<<5, 1<<6, 1<<7]
        #[1, 2, 4, 8, 16, 32, 64, 128]
        self.maskONE = self.maskONEValues.pop(0) #remove first value as it is being used

        #Mask used to clear bits: 254->11111110, 253->11111101 ... (using AND gate)
        self.maskZEROValues = [255-(1<<i) for i in range(8)]
        #[254, 253, 251, 247, 239, 223, 191, 127]
        self.maskZERO = self.maskZEROValues.pop(0)
        #254
        
        self.curwidth = 0  # Current width position
        self.curheight = 0 # Current height position
        self.curchan = 0   # Current channel position

    '''
    Function to insert bits into the image -- the actual steganography process

    param: bits - the binary values to be inserted in sequence
    '''
    def put_binary_value(self, bits):
        
        for c in bits:  #Iterate over all bits
            val = list(self.image[self.curheight,self.curwidth]) #Get the pixel value as a list (val is now a 3D array)
            if int(c):  #if bit is set, mark it in image
                val[self.curchan] = int(val[self.curchan])|self.maskONE 
            else:   #Else if bit is not set, reset it in image
                val[self.curchan] = int(val[self.curchan])&self.maskZERO 

            #Update image
            self.image[self.curheight,self.curwidth] = tuple(val)

            #Move pointer to the next space
            self.next_slot() 

    '''
    Function to move the pointer to the next location, and error handling if msg is too large
    '''
    def next_slot(self):
        if self.curchan == self.nbchannels-1: #If looped over all channels
            self.curchan = 0
            if self.curwidth == self.width-1: #Or the first channel of the next pixel of the same line
                self.curwidth = 0
                if self.curheight == self.height-1:#Or the first channel of the first pixel of the next line
                    self.curheight = 0
                    if self.maskONE == 128: #final mask, indicating all bits used up
                        raise SteganographyException("No available slot remaining (image filled)")
                    else: #else go to next bitmask
                        self.maskONE = self.maskONEValues.pop(0)
                        self.maskZERO = self.maskZEROValues.pop(0)
                else:
                    self.curheight +=1
            else:
                self.curwidth +=1
        else:
            self.curchan +=1

    '''
    Function to read in a bit from the image, at a certain [height,width][channel]
    '''
    def read_bit(self): #Read a single bit int the image
        val = self.image[self.curheight,self.curwidth][self.curchan]
        val = int(val) & self.maskONE
        #move pointer to next location after reading in bit
        self.next_slot()

        #Check if corresp bitmask and val have same set bit
        if val > 0:
            return "1"
        else:
            return "0"
    
    def read_byte(self):
        return self.read_bits(8)

    '''
    Function to read nb number of bits

    Returns image binary data and checks if current bit was masked with 1
    '''
    def read_bits(self, nb): 
        bits = ""
        for i in range(nb):
            bits += self.read_bit()
        return bits

    #Function to generate the byte value of an int and return it
    def byteValue(self, val):
        return self.binary_value(val, 8)

    #Function that returns the binary value of an int as a byte
    def binary_value(self, val, bitsize):
        #Extract binary equivalent
        binval = bin(val)[2:]

        #Check if out-of-bounds
        if len(binval)>bitsize:
            raise SteganographyException("Binary value larger than the expected size, catastrophic failure.")

        #Making it 8-bit by prefixing with zeroes
        while len(binval) < bitsize:
            binval = "0"+binval
            
        return binval

    def encode_text(self, txt):
        l = len(txt)
        binl = self.binary_value(l, 16) #Generates 4 byte binary value of the length of the secret msg
        self.put_binary_value(binl) #Put text length coded on 4 bytes
        for char in txt: #And put all the chars
            c = ord(char)
            self.put_binary_value(self.byteValue(c))
        return self.image
       
    def decode_text(self):
        ls = self.read_bits(16) #Read the text size in bytes
        l = int(ls,2)   #Returns decimal value ls
        i = 0
        unhideTxt = ""
        while i < l: #Read all bytes of the text
            tmp = self.read_byte() #So one byte
            i += 1
            unhideTxt += chr(int(tmp,2)) #Every chars concatenated to str
        return unhideTxt


class Encryptor:
    #Defining the Key
    def __init__(self, key):
        self.key = key

    def pad(self, s):
        return s + b"\0" * (AES.block_size - len(s) % AES.block_size)

    def encrypt(self, message, key, key_size=256):
        message = self.pad(message)
        iv = Random.new().read(AES.block_size)
        cipher = AES.new(key, AES.MODE_CBC, iv)
        return iv + cipher.encrypt(message)

    def encrypt_file(self, file_name):
        with open(file_name, 'rb') as fo:
            plaintext = fo.read()
        enc = self.encrypt(plaintext, self.key)
        with open(file_name + ".enc", 'wb') as fo:
            fo.write(enc)
        os.remove(file_name)

    def decrypt(self, ciphertext, key):
        iv = ciphertext[:AES.block_size]
        cipher = AES.new(key, AES.MODE_CBC, iv)
        plaintext = cipher.decrypt(ciphertext[AES.block_size:])
        return plaintext.rstrip(b"\0")

    def decrypt_file(self, file_name):
        with open(file_name, 'rb') as fo:
            ciphertext = fo.read()
        dec = self.decrypt(ciphertext, self.key)
        with open(file_name[:-4], 'wb') as fo:
            fo.write(dec)
        os.remove(file_name)

key = '*7Z?S3*H9e$2?YMz' 
enc = Encryptor(key)
clear = lambda: os.system('cls')

if os.path.isfile('data.txt.enc'):
    while True:
        #password = input2;
        password = str(input("Enter password: "))
        enc.decrypt_file("data.txt.enc")
        p = ''
        with open("data.txt", "r") as f:
            p = f.readlines()
        if p[0] == password:
            enc.encrypt_file("data.txt")
            break

    while True:
        clear()
                   
        ch = int(input( "Which operation would you like to perform?\n1.Encode Text\n2.Decode Text\n3.Exit Program\n"))
        clear()
        if ch==3:
            break
    
        if ch==1:
            print("Enter working directory of Desired image: ")
            wd=input()

        #Create object of class
            obj=Project(cv2.imread(wd))

           #print("\nEnter message to be encoded into source image: ")
            print("\nEntering message to be encoded into source image: ")
            inpute = input0+input1
            msg=input(pyautogui.typewrite(inpute,interval = 0.25))            
            

            #Invoke encode_text() function
            print("\nCreating encrypted image.")
            encrypted_img=obj.encode_text(msg)

            print("\nEnter destination image filename: ")
            dest=input()
            
            #Write into destination
            print("\nSaving image in destination.")
            cv2.imwrite(dest,encrypted_img)
            
            print("Encryption complete.")
            print("The encrypted file is available at",dest,"\n")

            im = Image.open(dest)

            root = tk.Tk()
            #canvas = Canvas(root, width = 300, height = 300)
            #canvas.pack()
            # A root window for displaying objects

            # Convert the Image object into a TkPhoto 
            object
            tkimage = ImageTk.PhotoImage(Image.open(dest))
            #canvas.create_image(20,20, anchor=NW, image=tkimage)

            tkinter.Label(root, image=tkimage).pack() 
            # Put it in the display window
            def my_random_string(string_length=10):
                """Returns a random string of length string_length."""
                random = str(uuid.uuid4()) # Convert UUID format to a Python string.
                random = random.upper() # Make all characters uppercase.
                random = random.replace("-","") # Remove the UUID '-'.
                return random[0:string_length] # Return the random string.
            with open ('otp_string.txt',"w") as otp_string:
                otp_string.write(my_random_string(6))
                
            root.after(10000, lambda: root.destroy())
               
            root.mainloop() # Start the GUI

            with open('testpass.txt',"w") as testpass:
                input5 = str(input("Enter the OTP: "))
                testpass.write(input5)
            f1 = open('testpass.txt','r')
            message1 = f1.read()
            print(message1)
            f1.close()
            f = open('otp_string.txt','r')
            message = f.read()
            print(message)
            f.close()
            while True:
                if message == message1:
                    print("Matched")
                    break
                else:
                    print('You are been logged out')
                    break
                             
                       
            
        elif ch==2:
            print("Enter working directory of source image: ")
            wd=input()
            img=cv2.imread(wd)
            obj=Project(img)

            print("\nText message obtained from decrypting image is:",obj.decode_text(),"\n")
            print('\n You have been granted permission')
            print('█▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀█')
            print('█░░╦─╦╔╗╦─╔╗╔╗╔╦╗╔╗░░█')
            print('█░░║║║╠─║─║─║║║║║╠─░░█')
            print('█░░╚╩╝╚╝╚╝╚╝╚╝╩─╩╚╝░░█')
            print('█▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄█')
            #format
         
else:
    while True:
        clear()
        #password = input2;
        password = str(input("Setting up stuff. Enter a password that will be used for decryption: "))
        repassword = str(input("Confirm password: "))
        if password == repassword:
            break
        else:
            print("Passwords Mismatched!")
    f = open("data.txt", "w+")
    f.write(password)
    f.close()
    enc.encrypt_file("data.txt")
    print("Please restart the program to complete the setup")
    time.sleep(7)




