# SPIN version of problem 3: Lock-free Log-based Set Algorithm

To simulate a run:
```
  spin lock-free-log-based-set.pml
```

Verification:
```
  spin -a  lock-free-log-based-set.pml
  gcc -DMEMLIM=1024 -O2 -DXUSAFE -DSAFETY -DNOCLAIM -DCOLLAPSE -w -o pan pan.c
  ./pan -m10000
```


## What is SPIN?

In short, SPIN is a model checker. It tests exhaustively all the
possible state of a concurrent system (written in C-like specification
language Promela), starting from the initial state.

For more details see:
  http://spinroot.com/spin/whatispin.html

## Verification of memory-safety property

At all points where a thread access the `log`, we check with an
assertion that the `log` index is above `gc`.

No error are found after exhaustive (i.e. all possible states)
verification with 2 threads on a log of 3 entries.

## Specificities of our model or specificities of SPIN influencing the model

**Processes.** There is a process per thread (of name `thread()`) plus
one for the environment. They are all launched by the `init` process
after initialization step.

Each `thread()` process can do indeterministically (i.e. in any order)
`update()` (to add or remote set element `1`), `lookup()` and
`collect()`.

**All Promela statements can block a process.** At any point in a
process, each time a statement is seen, it can block the current process
if it evaluates to false. For example a statement `val = v` can block
the process if `val != v` in the current state.

Our model avoids such behaviour, except in `if` and `do` statement and
in a particular case when we write `0 == 1` to block the process in a
known end state.

**When end of log is reached (`hd + 1 == SIZE`), the `update()`
operation becomes a no-op.**

**Absence of function in Promela** As there is no real function in
Promela, only macro like `inline` declaration, we used a convulated way
to emulate a function call. For example for `abs`, a variable `abs_res`
should be declared at the call point using `abs` inline. Within `abs`
inline, the variable `abs_res` is assigned to simulate value return.

**Both `d_step` and `atomic` are atomic statements.**

**Acceptable end state.** By default, end of a process is an acceptable
end state. One can add new ones by putting a label starting with `end`.

