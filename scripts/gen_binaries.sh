#!/bin/bash

mkdir bin
cd ../model

MEMORY_SIZE=2
CACHE_SIZE=1

for NPROC in {2..16}; do
    # for MEMORY_SIZE in {1..2}; do
        # for CACHE_SIZE in $(seq 1 $MEMORY_SIZE); do
            sed -i "s/#define NPROC.*/#define NPROC $NPROC/" mesi.pml
            sed -i "s/#define CACHE_SIZE.*/#define CACHE_SIZE $CACHE_SIZE/" mesi.pml
            sed -i "s/#define MEMORY_SIZE.*/#define MEMORY_SIZE $MEMORY_SIZE/" mesi.pml

            make
            mv pan ../scripts/bin/pan_${NPROC}proc_${CACHE_SIZE}cache_${MEMORY_SIZE}mem
            # Run your other commands here with the modified file
    #     done
    # done
done

cd ../scripts
scp bin/pan* ljmarzen@prontodtn.las.iastate.edu:applied-formal-methods-final-project-cache-me-outside/

