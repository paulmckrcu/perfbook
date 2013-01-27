#!/bin/sh

sh todat.sh 2.6.23-PREEMPT-DBG-atomic_inc16-wt > atomicrefperfwtPREEMPTerr.dat
sh todat.sh 2.6.23-PREEMPT-DBG-r16-wt > RCUperfwtPREEMPTerr.dat
sh todat.sh 2.6.23-PREEMPT-DBG-rwlr16-wt > rwlockperfwtPREEMPTerr.dat
