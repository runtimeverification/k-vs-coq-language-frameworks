
## Verification Example in Coq

The example gives a specification of the language IMP, the program SUM and the correctness
property in [Coq](https://coq.inria.fr). This example is an adaptation of the IMP example
in [Program Verification by Coinduction](https://github.com/Formal-Systems-Laboratory/coinduction).

The specification files are as follows:

- `proof_system.v`: The main soundness theorem allowing the reachability logic proof strategy.
- `imp.v`: The specification of IMP, SUM and the correctness property in Coq, along with the
   correctness proof.
- `execution.v`: Test executions as theorems.

## Running the Example

Assuming Coq has been downloaded and installed (see the
[Coq documentation](https://coq.inria.fr/opam-using.html)), the specification may be compiled
and run simply by issuing the command:

```
make all
```

The command compiles the specification files and then runs the correctness proofs on SUM.

`make clean` removes all binaries built during this process.

## Help and Feedback

Feel free to report GitHub issues or to contact us at:
[contact@runtimeverification.com](mailto:contact@runtimeverification.com).
