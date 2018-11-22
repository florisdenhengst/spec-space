#!/bin/bash
#pip install ply & pip install pytest & pip install pyeda
mkdir -p tmp
cd tmp
wget https://github.com/marcthurley/sharpSAT/archive/master.zip
unzip master.zip
rm master.zip
mv sharpSAT-master sharpSAT
cd sharpSAT
./setupdev.sh
cd build/Release
make
mkdir -p ../../../../bin
mv sharpSAT ../../../../bin/
cd ../../../../  
rm -rf tmp
