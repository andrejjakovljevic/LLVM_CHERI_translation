# LLVM IR Translation - Hybrid to Pure Capability

## About

This repository contains code dedicated to translating LLVM intermediate representation (IR) from a hybrid capability model to a pure capability model, supported by CHERI (more details can be found [here](https://www.cl.cam.ac.uk/research/security/ctsrd/cheri/)). 
The implementation addresses the crucial step of adapting software originally developed for a non-capability, traditional architecture to one that aligns with CheriABI.
The primary functionality centers around transforming LLVM IR code, ensuring compatibility with CheriABI's pure capability model. 
This involves handling the intricacies of hybrid capability structures and adapting them to a format suitable for CheriABI.
This work was done as part of the project in the MPhil in Advanced Computer Science course at the University of Cambridge, supervised by Dr. Robert Watson.

## Usage

After cloning the repository, navigate to the build folder and run

```
cmake .. -DCMAKE_C_FLAGS_INIT=-mabi=aapcs -DCMAKE_CXX_FLAGS_INIT=-mabi=aapcs
```

This will make the necessary files for the LLVM pass. 
For translating source code in the shape of an .ll file, position yourself in the build/HelloPass directory and run:
```
opt -S -enable-new-pm=0 -load ./HelloPass.so -hello < [PATH OF YOUR .ll FILE] > [PATH TO THE OUTPUT .ll FILE]
```
For example:
```
opt -S -enable-new-pm=0 -load ./HelloPass.so -hello < hello_hybrid.ll > hello_purecap.ll
```

To then create a pure-capability binary, run

```
cc -mabi=purecap hello_purecap.c -o a.out
```

Which you can then run on CHERI.

To fully utilize the translation capability of this project, you can build the fork of clang which can be found [here](https://github.com/andrejjakovljevic/llvm-morello-for-translation). 
The custom clang is used for compilation with the following command:
```
[PATH TO THE CLANG PROJECT]/build/bin/clang -fno-discard-value-names -O0 -S -emit-llvm -Wno-override-module -Wno-pointer-sign -Wno-unknown-attributes -Wno-implicit-int -fgnu89-inline [INPUT .c FILE] -o [OUPUT .ll FILE]
```
