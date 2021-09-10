#!/bin/sh

../todat.sh 2.6.23-PREEMPT-DBG-atomic_inc > atomicincperfPREEMPTerr.dat
../todat.sh 2.6.23-PREEMPT-DBG-atomic_ref > atomicrefperfPREEMPTerr.dat
../todat.sh 2.6.23-PREEMPT-DBG-rwlr > rwlockperfPREEMPTerr.dat
