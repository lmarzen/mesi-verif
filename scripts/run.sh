set -x

CACHE_SIZE=1
MEMORY_SIZE=2

for NPROC in {2..16}; do
time ./pan_${NPROC}proc_${CACHE_SIZE}cache_${MEMORY_SIZE}mem -m10000000000 -a -w28 &> results/verif_${NPROC}proc_${CACHE_SIZE}cache_${MEMORY_SIZE}mem.out
time bash run_validate ${NPROC}proc_${CACHE_SIZE}cache_${MEMORY_SIZE}mem
done
