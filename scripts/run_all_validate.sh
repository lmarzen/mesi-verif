set -x

CACHE_SIZE=1
MEMORY_SIZE=2

for NPROC in {2..8}; do
#time ./pan_${NPROC}proc_${CACHE_SIZE}cache_${MEMORY_SIZE}mem -m100000000 -a -w27 &> results/verif_${NPROC}proc_${CACHE_SIZE}cache_${MEMORY_SIZE}mem.out
time bash run_validate ${NPROC}proc_${CACHE_SIZE}cache_${MEMORY_SIZE}mem
done

CACHE_SIZE=1
MEMORY_SIZE=1

for NPROC in {2..4}; do
#time ./pan_${NPROC}proc_${CACHE_SIZE}cache_${MEMORY_SIZE}mem -m100000000 -a -w27 &> results/verif_${NPROC}proc_${CACHE_SIZE}cache_${MEMORY_SIZE}mem.out
time bash run_validate ${NPROC}proc_${CACHE_SIZE}cache_${MEMORY_SIZE}mem
done
