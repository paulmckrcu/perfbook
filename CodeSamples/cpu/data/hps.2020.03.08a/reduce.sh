echo Local cmpxchg:
grep localcmpxchg localtorture.sh.2020.03.08a.sh.out | awk '{ sum += $9 } END { print sum / NR }'

echo Local lock:
grep locallock localtorture.sh.2020.03.08a.sh.out | awk '{ sum += $9 } END { print sum / NR }'
