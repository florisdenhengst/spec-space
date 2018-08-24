#!/bin/bash
pip2 install ply & pip2 install pytest
mkdir lib
cd lib
wget https://github.com/marcthurley/sharpSAT/archive/master.zip
unzip master.zip
rm master.zip
mv sharpSAT-master sharpSAT
cd sharpSAT
./setupdev.sh
cd build/Release
make
