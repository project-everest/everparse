1. DEPENDENCIES: EVERPARSE

This package depends on EverParse. To install EverParse, run
./install-everparse.sh and follow the instructions.

Alternatively, you can use the Dockerfile to have an environment with
EverParse already installed:
   docker build -t asn1star .
   docker run -i -t asn1star

2. HOW TO VERIFY, EXTRACT AND EVALUATE

To verify, extract the OCaml code and compile it, run:
   make -j

To run the evaluation experiments, run:
   make eval
