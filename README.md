# k-vs-coq-language-frameworks

This repository provides a simple verification example through which the [K framework](http://www.kframework.org) 
and [Coq](https://coq.inria.fr) are compared as language specification and verification frameworks. This a 
companion resource for the article/sequence of posts linked below:

[posts](#)

In this example, we show how the correctness property of computing the sum of numbers 
from 1 to N, with N a non-negative integer, is specified and verified in each framework for 
a program SUM written in a simple imperative lagnauge IMP.

## Repository Structure

There are two subdirectories:

- `k`: which contains the specification of the example and verification tasks in K.
- `coq`: which contains the specification of the example and verification tasks in Coq. 

The example consists primarily of the specification of the language IMP and its 
semantics, the specification of the program SUM and the specification of the correctness
property to be verified, in each language framework. More details can be found in the
individual subdirectories.

## Pre-requisites

In order to compile and run the examples, you need to have both K and Coq properly installed in
your system. Refer to ... and ... for installation instructions.

Once installed, make sure that you update the Make file of the K specification located at
`k/Makefile` so that `$K_HOME` is set to point to the home folder of where K is installed in
your system.

## Running the Verification Tasks

Once you have K and Coq installed, and `$K_HOME` is properly set, you may compile all the 
example's files  and run the verification tasks by issuing the following command at the root
of this repository:

```
make all
```

This first compiles the K version of the example and then verifies the
specification of SUM. Then, it compiles the Coq version of the example, which includes
proving that SUM satisfies its specification.

If you wish to re-run these tasks, do a `make clean` to start afresh before running `make all` again.


