// AESEncryption.cpp
// Employs the AESEncryption Scheme for a given string input from the user
//
// - Integers are stored as unsigned 8 bit integers for the sake of memory and keeing values in mod 255
// - For strings whos lengths are not a multiple of 16, it will padd the string to be a valid length by using 0's until it reaches a valid length
// - Currently uses the ECB Chaining mode, meaning the string gets split up into blocks of 16 and the key is used individually on each block
// 
// Next Steps:
// - Look into different message padding methods, as Zero padding is very bare. Look into benefits of each
// - Implement the option to select different chaining modes (CBC, CFB, OFB, CTR) and use initialization vectors
// - Add decrpyter
// - Add unit tests and look for edge cases
// - Put output into strings of hex values
// - Put output into different formats such as base 64

#include <iostream> //used for input and output from the user
#include <string> //string objects and  methods used for getting bytes and info from input
#include <iomanip>  //used for printing outputs in certain bases and manners
#include <Eigen/Dense> //used to hold the matrices of information. You can find it here: https://eigen.tuxfamily.org/index.php?title=Main_Page and just put it in your include path
#include <vector> //used to hold vectors of various object types (ints, vectors, matrices)
#include <cmath> //used for pow when calculating the rounding constant


using namespace std;
using namespace Eigen;



void printVectorOfVectors(const vector<vector<uint8_t>>& vec) {
    //prints each element of each vector in the vector of vectors in hexadecimal. Used in debugging
    for (const auto& innerVec : vec) {
        for (const auto& element : innerVec) {
            cout << hex << setw(2) << setfill('0') << static_cast<int>(element) << " ";
        }
        cout << endl;
    }
}

void printMatrixInHex(Matrix4d ourMat) {
    //prints out a matrix in hex. Used for state matrix debugging and correction
    for(int k = 0; k < 4; k++) {
        for(int j = 0; j < 4; j++) {
            cout << hex << setw(2) << setfill('0') << static_cast<int>(ourMat(k, j)) << " ";
        }
        cout << endl;
    }
}

void printVectorOfMatrices(const vector<Matrix4d>& ourMat) {
    //prints out each matrix in a vector, used for printing out the final encrypted vector of matrices
    for(const auto& mat: ourMat) {
        printMatrixInHex(mat);
        cout << endl;
    }
}

bool isValidKeyLength(int keyLength) {
    // Returns a boolean on whether the given key length is valid for one of the AES Schema
    return (keyLength == 16 || keyLength == 24 || keyLength == 32);
}

string addZeroPadding(string initInput) {
    // Adds padding onto the end of the string to make the information able to be put into blocks of size 16
    if(initInput.length() % 16 == 0) {
        return initInput; //returns the input if its a multiple of 16
    }

    int diff = 16 - (initInput.length() % 16);// finds how far the message length is from a multiple of 16

    string messageCopy = initInput; //creates a copy of our given message

    for(int i = 0; messageCopy.length() < 16; i++) {
        //This loop adds 0's onto the end of the string until it is the appropriate length
        messageCopy += '0';
    }

    return messageCopy;

}

Matrix4d stringToMatrix(string paddedMessage) {
    //Takes a strings char ascii values and puts them in a matrix for the AES Schema

    Matrix4d fourBlock;//initializes an empty 4x4 matrix;
    
    int ind = 0;//index variable to let us iterate over the string
    
    for(int i = 0; i < 4; i++) {
        for(int j = 0; j < 4; j++) {           
            fourBlock(j, i) = static_cast<uint8_t>(paddedMessage[ind]);//casts the ascii value to an 8 bit unsigned integer
            ind++;
        }
    }


    return fourBlock;
}

vector<uint8_t> stringToVector(string ourStr) {
    //Takes a string and put its ascii char values into a vector
    //Used to seperate our key for the creation of the key schedule

    vector<uint8_t> v;//initializes the vector to store the ascii values

    int size = ourStr.length();//gives us a maximum iteration for our loop

    for(int i = 0; i < size; i++) {
        //casts the ascii values to unsigned 8bit integers and pushes them to the vector
        v.push_back(static_cast<uint8_t>(ourStr[i]));
    }

    return v;

} 

vector<uint8_t> keyGenShift(vector<uint8_t> ourVec, int s[], int round) {
    //Every 4th key in the generation of a key schedule will undergo a transformation before being XOR'ed with key i - 4
    //This involves a process of
    //  shifting bytes
    //  subbing bytes
    //  and adding a round constant based on the round number

    vector<uint8_t> v; //initialized the vector that will hold our transformed bytes

    double rConD = pow(2.0, static_cast<double>(round - 1));//calculates the round constant

    uint8_t rCon = static_cast<uint8_t>(rConD);//puts the round constant into an unsigned 8 bit integer

    if(rConD == 256) {
        rCon = 0x1b;// This is 0x80 * 2 under the galois field GF(2^8)
    }

    if(rConD == 512) {
        rCon = 0x36;//This is 0x1b * 2 under the galois field GF(2^8)
    }

    for(int i = 0; i < ourVec.size(); i++) {
        v.push_back(ourVec[(i + 1) % ourVec.size()]);// this loop shifts everything in the vector left one
    } 

    for(int j = 0; j < ourVec.size(); j++) {
        v[j] = s[v[j]];//this puts each component of our vector through the Rjindael sBox
    } 
 
    v[0] = v[0] ^ rCon;//XOR's our new vector with the round constant, resulting in our new vector 
    
    return v;

}

vector<uint8_t> vectorXOR(vector<uint8_t> v1, vector<uint8_t> v2) {
    //conducts element wise XOR on two vectors and returns the result
    //mainly used for code cleanliness
    
    vector<uint8_t> v;

    for(int i = 0; i < v1.size(); i++) {
        v.push_back(v1[i] ^ v2[i]);//XOR's respective elements of two vectors
    }

    return v;
}

vector<vector<uint8_t>> createKeys(vector<uint8_t> keyVec, int s[]) {
    //creates a key schedule based on the initial key
    //generates 44 keys for aes128
    //generates 52 keys for aes192
    //generates 60 keys for aes256
    
    vector<vector<uint8_t>> v;//initializes our vector to hold our key schedule

    int size = keyVec.size();//gets the key size that will help us determine the encryption parameters

    int max;//initializes a variable to count the amount of keys we will need

    int Nk;//initializes a key count variable to get our initial key rounds

    int round = 1;//round variable that increments the round associated with the key to calculate the proper round constant in keyGenShift

    
    switch (size) {
        //switch statement to determine the key size parameters (for 128, 192, or 256)
        case 16:
            max = 44;
            Nk = 4;
            break;
        case 24:
            max = 52;
            Nk = 6;
            break;
        case 32:
            max = 60;
            Nk = 8;
            break;
        default:
            //should never be reached but will let know if so
            cout << "False key size" << endl;
            break;
    }

    //The below will initialize our first Nk round keys

    vector<uint8_t> roundKeyVec;//temp vec variable to put key vectors into our round keys

    for(int i = 0; i < (Nk * 4); i += 4) {

        roundKeyVec.push_back(keyVec[i]);
        roundKeyVec.push_back(keyVec[i+1]);
        roundKeyVec.push_back(keyVec[i+2]);
        roundKeyVec.push_back(keyVec[i+3]);

        v.push_back(roundKeyVec);

        roundKeyVec.clear();

    }

    vector<uint8_t> gVec = keyGenShift(v[v.size() - 1], s, round);// gVec is the variable that will hold any vector that goes through keyGen shift


    if(max == 44) {
        while(v.size() < max) {
            //notes will notate for the first round and the rest should follow
            v.push_back(vectorXOR(v[v.size() - 4], gVec)); //this does xor on w_0 and g(w_3) and creates w_4
            v.push_back(vectorXOR(v[v.size() - 4], v[v.size() - 1])); //does xor on w1 and w4 creating w5
            v.push_back(vectorXOR(v[v.size() - 4], v[v.size() - 1])); //does xor on w2 and w5 creating w6
            v.push_back(vectorXOR(v[v.size() - 4], v[v.size() - 1])); //does xor on w3 and w6 creating w7

            round++; // increases round value

            gVec = keyGenShift(v[v.size() - 1], s, round); // creates the next gvector to be used in generating the next word
            
            //wraps around to append w_4 XOR g(w_7)
        }
    }
    if(max == 52) {
        while(v.size() < max) {
            //notes will notate for the first round and the rest should follow
            v.push_back(vectorXOR(v[v.size() - 6], gVec)); //this does xor on w_0 and g(w_5) and creates w_6
            v.push_back(vectorXOR(v[v.size() - 6], v[v.size() - 1])); //does xor on w1 and w6 creating w7
            v.push_back(vectorXOR(v[v.size() - 6], v[v.size() - 1])); //does xor on w2 and w7 creating w8
            v.push_back(vectorXOR(v[v.size() - 6], v[v.size() - 1])); //does xor on w3 and w8 creating w9
            v.push_back(vectorXOR(v[v.size() - 6], v[v.size() - 1])); //does xor on w4 and w9 creating w10
            v.push_back(vectorXOR(v[v.size() - 6], v[v.size() - 1])); //does xor on w5 and w10 creating w11

            round++; // increases round value

            gVec = keyGenShift(v[v.size() - 1], s, round); // creates the next gvector to be used in generating the next word
            

        }
    }
    if(max == 60) {
        vector<uint8_t> tempVec;
        vector<uint8_t> tempVec2;
        //temp vector variables to handle the differences with AES256 usage of subBytes
        while(v.size() < max) {
            v.push_back(vectorXOR(v[v.size() - 8], gVec)); //this does xor on w_0 and g(w_7) and creates w_8
            v.push_back(vectorXOR(v[v.size() - 8], v[v.size() - 1])); //does xor on w1 and w8 creating w9
            v.push_back(vectorXOR(v[v.size() - 8], v[v.size() - 1])); //does xor on w2 and w9 creating w10
            v.push_back(vectorXOR(v[v.size() - 8], v[v.size() - 1])); //does xor on w3 and w10 creating w11
            tempVec2 = v[v.size() - 1];
            for(int j = 0; j < 4; j++) {
                tempVec.push_back(static_cast<uint8_t>(s[tempVec2[j]])); // creates the subByte vector on w11 
            }
            tempVec2.clear();
            v.push_back(vectorXOR(v[v.size() - 8], tempVec)); //does xor on w4 and sub(w11) creating w12
            v.push_back(vectorXOR(v[v.size() - 8], v[v.size() - 1])); //does xor on w3 and w12 creating w13
            v.push_back(vectorXOR(v[v.size() - 8], v[v.size() - 1])); //does xor on w4 and w13 creating w14
            v.push_back(vectorXOR(v[v.size() - 8], v[v.size() - 1])); //does xor on w5 and w14 creating w15

            round++; // increases round value

            tempVec.clear();

            gVec = keyGenShift(v[v.size() - 1], s, round); // creates the next gvector to be used in generating the next word
        }
    }

    return v;
    
}

int galois2x(int num) {
    //computes multiplication by 2 under GF(2^8)
    int value = num << 1;
    if (num & 0x80) {
        value ^= 0x1b;
    }
    return (value);
}

int galois3x(int num) {
    //computes multiplication by 3 under GF(2^8)
    return (galois2x(num) ^ num);
}

Matrix4d subBytes(Matrix4d ourMat, int s[]) {
    //uses the Rjindael S-Box on our whole state matrix

    Matrix4d matCopy = ourMat;

    for(int i = 0; i < 4; i++) {
        for(int j = 0; j < 4; j++) {
            matCopy(j, i) = s[static_cast<int>(matCopy(j, i))];
        }
    }

    return matCopy;

}

Matrix4d shiftRows(Matrix4d ourMat) {
    //shifts rows according to the aes schema
    //
    // a b c d
    // e f g h
    // i j k l
    // m n o p
    //
    // becomes
    //
    // a b c d
    // h e f g
    // k l i j
    // n o p m
    
    Matrix4d matCopy = ourMat;

    matCopy.row(1) << ourMat(1, 1), ourMat(1, 2), ourMat(1, 3), ourMat(1, 0);
    matCopy.row(2) << ourMat(2, 2), ourMat(2, 3), ourMat(2, 0), ourMat(2, 1);
    matCopy.row(3) << ourMat(3, 3), ourMat(3, 0), ourMat(3, 1), ourMat(3, 2);
    

    return matCopy;
}

Matrix4d mixColumns(Matrix4d ourMat) {
    //Utilizes a special kind of multiplication with polynomials defined under GF(2^8)
    Matrix4d matCopy = ourMat;

    for(int i = 0; i < 4; i++) {
        for(int j = 0; j < 4; j++) {
            if(j == 0) {
                matCopy(j, i) = static_cast<uint8_t>(galois2x(static_cast<int>(ourMat(0, i))) ^ galois3x(static_cast<int>(ourMat(1, i))) ^ static_cast<int>(ourMat(2, i)) ^ static_cast<int>(ourMat(3, i)));
            }
            if(j == 1) {
                matCopy(j, i) = static_cast<uint8_t>(static_cast<int>(ourMat(0, i)) ^ galois2x(static_cast<int>(ourMat(1, i))) ^ galois3x(static_cast<int>(ourMat(2, i))) ^ static_cast<int>(ourMat(3, i)));
            }
            if(j == 2) {
                matCopy(j, i) = static_cast<uint8_t>(static_cast<int>(ourMat(0, i)) ^ static_cast<int>(ourMat(1, i)) ^ galois2x(static_cast<int>(ourMat(2, i))) ^ galois3x(static_cast<int>(ourMat(3, i))));
            }
            if(j == 3) {
                matCopy(j, i) = static_cast<uint8_t>(galois3x(static_cast<int>(ourMat(0, i))) ^ static_cast<int>(ourMat(1, i)) ^ static_cast<int>(ourMat(2, i)) ^ galois2x(static_cast<int>(ourMat(3, i))));
            }
        }
    }

    return matCopy;
}

Matrix4d addRoundKey(Matrix4d ourMat, vector<vector<uint8_t>> keySection) {
    //adds round key to our state matrix based on the selected key section

    Matrix4d matCopy = ourMat;

    vector<uint8_t> currVec;

    for(int i = 0; i < 4; i++) {
        currVec = keySection[i];
        for(int j = 0; j < 4; j++) {
            matCopy(j, i) = static_cast<int>(matCopy(j, i)) ^ currVec[j];
        }
    }

    return matCopy;

}

int main() {

    bool flag = true; //sets flag for repeated usage of the encrypter

    int s[256] =  
    {0x63 ,0x7c ,0x77 ,0x7b ,0xf2 ,0x6b ,0x6f ,0xc5 ,0x30 ,0x01 ,0x67 ,0x2b ,0xfe ,0xd7 ,0xab ,0x76
    ,0xca ,0x82 ,0xc9 ,0x7d ,0xfa ,0x59 ,0x47 ,0xf0 ,0xad ,0xd4 ,0xa2 ,0xaf ,0x9c ,0xa4 ,0x72 ,0xc0
    ,0xb7 ,0xfd ,0x93 ,0x26 ,0x36 ,0x3f ,0xf7 ,0xcc ,0x34 ,0xa5 ,0xe5 ,0xf1 ,0x71 ,0xd8 ,0x31 ,0x15
    ,0x04 ,0xc7 ,0x23 ,0xc3 ,0x18 ,0x96 ,0x05 ,0x9a ,0x07 ,0x12 ,0x80 ,0xe2 ,0xeb ,0x27 ,0xb2 ,0x75
    ,0x09 ,0x83 ,0x2c ,0x1a ,0x1b ,0x6e ,0x5a ,0xa0 ,0x52 ,0x3b ,0xd6 ,0xb3 ,0x29 ,0xe3 ,0x2f ,0x84
    ,0x53 ,0xd1 ,0x00 ,0xed ,0x20 ,0xfc ,0xb1 ,0x5b ,0x6a ,0xcb ,0xbe ,0x39 ,0x4a ,0x4c ,0x58 ,0xcf
    ,0xd0 ,0xef ,0xaa ,0xfb ,0x43 ,0x4d ,0x33 ,0x85 ,0x45 ,0xf9 ,0x02 ,0x7f ,0x50 ,0x3c ,0x9f ,0xa8
    ,0x51 ,0xa3 ,0x40 ,0x8f ,0x92 ,0x9d ,0x38 ,0xf5 ,0xbc ,0xb6 ,0xda ,0x21 ,0x10 ,0xff ,0xf3 ,0xd2
    ,0xcd ,0x0c ,0x13 ,0xec ,0x5f ,0x97 ,0x44 ,0x17 ,0xc4 ,0xa7 ,0x7e ,0x3d ,0x64 ,0x5d ,0x19 ,0x73
    ,0x60 ,0x81 ,0x4f ,0xdc ,0x22 ,0x2a ,0x90 ,0x88 ,0x46 ,0xee ,0xb8 ,0x14 ,0xde ,0x5e ,0x0b ,0xdb
    ,0xe0 ,0x32 ,0x3a ,0x0a ,0x49 ,0x06 ,0x24 ,0x5c ,0xc2 ,0xd3 ,0xac ,0x62 ,0x91 ,0x95 ,0xe4 ,0x79
    ,0xe7 ,0xc8 ,0x37 ,0x6d ,0x8d ,0xd5 ,0x4e ,0xa9 ,0x6c ,0x56 ,0xf4 ,0xea ,0x65 ,0x7a ,0xae ,0x08
    ,0xba ,0x78 ,0x25 ,0x2e ,0x1c ,0xa6 ,0xb4 ,0xc6 ,0xe8 ,0xdd ,0x74 ,0x1f ,0x4b ,0xbd ,0x8b ,0x8a
    ,0x70 ,0x3e ,0xb5 ,0x66 ,0x48 ,0x03 ,0xf6 ,0x0e ,0x61 ,0x35 ,0x57 ,0xb9 ,0x86 ,0xc1 ,0x1d ,0x9e
    ,0xe1 ,0xf8 ,0x98 ,0x11 ,0x69 ,0xd9 ,0x8e ,0x94 ,0x9b ,0x1e ,0x87 ,0xe9 ,0xce ,0x55 ,0x28 ,0xdf
    ,0x8c ,0xa1 ,0x89 ,0x0d ,0xbf ,0xe6 ,0x42 ,0x68 ,0x41 ,0x99 ,0x2d ,0x0f ,0xb0 ,0x54 ,0xbb ,0x16}; //S-box: maps bute values from 0 to 255 to a new value under Rijndaels finite field
    // This and the shift columns function are based in galois theory with a polynomial interpretation

    string key; //initializes our key variable

    string message; //initializes our message variable

    string paddedMessage;

    int front; //These front and back variables let us grab parts of our key 4 bytes at a time
    int back; //to use in the addRoundKey function

    int rounds; //initializes our round count variable for determining how many loops aes will do

    Matrix4d state; //initializes our matrix that our message will be stored and mixed in

    vector<uint8_t> inputVec; //initializes the vector that will turn our key into bytes

    vector<vector<uint8_t>> keyVec; //initializes the vector that will hold all of our keys during the key generation process

    vector<vector<uint8_t>> keySection; //initializes the vector that will hold the keys used in addRoundKey

    vector<Matrix4d> matVec; //matrix to hold all of the 16 byte blocks of our initial string

    vector<Matrix4d> encVec; //matrix to hold all of our encrypted matrices

    string cont; //cont variable to see if people want to continue

    while(flag) {

        front = 0;//Resets front to 0 upon looping
        back = 3;//Resets back to 3 upon looping
        //These let us index back to the first 4 parts of our key

        cout << "Input Message: " << endl;

        getline(cin, message);//Prompts user to input message as a string

        cout << "Input Key (Key must be 16, 24, or 32 characters long): " << endl;

        getline(cin, key);//Prompts user to input key as a string

        while(!isValidKeyLength(key.length())) {
            //This loop validates key length

            cout << "Please input a key that is 16, 24, or 32 characters:" << endl;

            getline(cin, key);

        }

        switch (key.length()) {
            //This switch statement sets the number of rounds
            case 16:
                cout << "Starting AES128" << endl;
                rounds = 10;
                break;
            case 24:
                cout << "Starting AES192" << endl;
                rounds = 12;
                break;
            case 32:
                cout << "Starting AES256" << endl;
                rounds = 14;
                break;
            default:
                cout << "Invalid Key Length" << endl;
                break;
        }

        //Message: Two One Nine Two
        //Key: Thats my Kung Fu

        for(int k = 0; k < (message.length() / 16); k++) {
            matVec.push_back(stringToMatrix(message.substr(16 * k, 16)));// adds the blocks in 16 byte chunks into the vector of matrices
        }

        inputVec = stringToVector(key);//prepares our inital key vector to create our key schedule

        keyVec = createKeys(inputVec, s);//creates the key schedule

        for(int i = front; i <= back; i++) {
            keySection.push_back(keyVec[i]);//creates our first vector to be used in addRoundKey
        }

        for(int j = 0; j < matVec.size(); j++){

            state = matVec[j];;

            for(int i = 0; i < (rounds - 1); i++) {

                cout << "Starting round number " << dec << (front/4) + 1 << endl;

                state = addRoundKey(state, keySection);//adds the keys for the current round   
                
                front += 4;
                back += 4;
                //these are incremented by 4 to grab the next key section

                keySection.clear();//clears the key section to replace with new keys


                for(int j = front; j <= back; j++) {
                    keySection.push_back(keyVec[j]);//fills new key section with new keys
                }

                state = subBytes(state, s);//subs the bytes in the state matrix based on the Rigndael S-box

                state = shiftRows(state);//shifts the rows in the state matrix

                state = mixColumns(state);//mixes the columns in the state matrix

            }

            cout << "Starting round number " << dec << (front/4) + 1 << endl;

            state = addRoundKey(state, keySection);//adds second to final round key
                
            front += 4;
            back += 4;
            //front and back are incremented

            keySection.clear();

            for(int j = front; j <= back; j++) {
                keySection.push_back(keyVec[j]);//final key section is prepared
            }

            state = subBytes(state, s);//final sub bytes

            state = shiftRows(state);//final row shift

            cout << "Adding last round key" << endl;

            state = addRoundKey(state, keySection);//adds final round key

            encVec.push_back(state);

            front = 0;
            back = 3;

            keySection.clear();

            for(int i = front; i <= back; i++) {
                keySection.push_back(keyVec[i]);//creates our first vector to be used in addRoundKey for the next block
            }

        }

        cout << "Encrypted Message in blocks: " << endl;

        printVectorOfMatrices(encVec);

        encVec.clear();

        cout << "printing encVec post clear" << endl;
        
        printVectorOfMatrices(encVec);

        cout << "Would you like to encrypt again? (answer 'yes' or 'no')" << endl;

        getline(cin, cont);

        if(cont == "yes" || cont == "Yes") {
            keySection.clear(); //Clears the key section for the next run through
            matVec.clear(); //clears the string to matrix vector
            encVec.clear(); //clears the encrypted matrix vector
            continue;
        }
        else {
            cout << "Thank you for encrypting!" << endl;
            flag = false;
        }

    }

    return 0;
}