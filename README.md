# K vs. Coq Example

This repository provides a simple verification example through which the 
[K framework](http://www.kframework.org) and [Coq](https://coq.inria.fr) are compared as
language specification and verification frameworks. This is a companion resource for the 
article/sequence of posts [TBA](#)

In this example, we illustrate how the correctness property of computing the sum of numbers 
from 1 to N (with N a non-negative integer) is specified and verified in each framework for 
a program SUM written in a simple imperative lagnauge IMP.

## Repository Structure

There are two subdirectories:

- `k`: which contains the specification of the example and verification tasks in K.
- `coq`: which contains the specification of the example and verification tasks in Coq. 

The example consists primarily of the specification of the language IMP and its 
semantics, the specification of the program SUM and the specification of the correctness
property to be verified, in each language framework. More details can be found in the
individual subdirectories.

## Prerequisites

In order to compile and run the examples, you need to have both K and Coq properly installed in
your system. Refer to the [K project repository](https://github.com/kframework/k) and 
[Coq's documentation](https://coq.inria.fr/opam-using.html) for installation instructions.

Once installed, make sure that you update the Make file of the K specification located at
`k/Makefile` so that `$K_HOME` is set to point to the directory where K is installed in
your system. For example, if you downloaded K to `~/tools/k`, update the line
in `k/Makefile` that begins with `$K_HOME` so that its value is exactly `~/tools/k`. 

## Running the Verification Tasks

Once you have K and Coq installed, and assuming `$K_HOME` is properly set, you may compile all
the example's files  and run the verification tasks by issuing the following command at the
root of the repository (the directory of this README):

```
make all
```

This first compiles the K version of the example and then verifies the specification of SUM 
against it. Make will then compile the Coq version of the example, which includes proving in
Coq that SUM satisfies its specification.

See the individual sub-directories for further options for running these tasks.

## Help and Feedback

Feel free to report GitHub issues or to contact us at: 
[contact@runtimeverification.com](mailto:contact@runtimeverification.com).

