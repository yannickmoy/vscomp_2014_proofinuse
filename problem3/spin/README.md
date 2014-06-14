# SPIN version of problem 3: Lock-free Log-based Set Algorithm

To simulate a run:
    spin lock-free-log-based-set.pml

Verification:
    spin -a  lock-free-log-based-set.pml
    gcc -DMEMLIM=1024 -O2 -DXUSAFE -DSAFETY -DNOCLAIM -w -o pan pan.c
    ./pan -m10000


## What is SPIN?

See: http://spinroot.com/spin/whatispin.html
