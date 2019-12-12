
## Verification Example in K

The example gives a specification of the language IMP, the program SUM and the correctness
property in the [K framework](http://www.kframework.org). This example is based on the IMP
example of the [K Tutorial](https://github.com/kframework/k/tree/master/k-distribution/tutorial).

The specification files are as follows:

- `imp.k`: The formal specification L of the syntax and semantics of IMP in K.
- `sum/sum.imp`: The program (specification) P of SUM.
- `sum/sum-spec.k`: The specification S of the correctness property to be verified.

## Running the Example

First, assuming [K](https://github.com/kframework/k) is downloaded and compiled, modify the 
line beginning with `$K_HOME` in the make file `Makefile` so that `$K_HOME` is set to point 
to the home directory of K in your system. For example, if you downloaded K to `~/tools/k`, 
update the line in `k/Makefile` that begins with `$K_HOME` so that it reads:

```
$K_HOME:=~/tools/k
```

Then, you may build the K program tools for IMP using the command:

```
make build
```

Now, you can execute the program SUM using the command:

```
make run-sum
```

Or you may proceed to proving correctness of SUM against its specification using the command:

```
make verify-sum
```

`make clean` removes all binaries built during this process.

## Help and Feedback

Feel free to report GitHub issues or to contact us at:
[contact@runtimeverification.com](mailto:contact@runtimeverification.com).

