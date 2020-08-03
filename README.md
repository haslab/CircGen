# CircGen - Circuit Description Generation tool

This is a prototype of the **CircGen** tool. It is based
on *CompCert - a certified compiler for C*
(http://compcert.inria.fr). Please consult the original CompCert's
[README](README) and its [manual](http://compcert.inria.fr/man/) for
addition information on CompCert on its copyright/usage instructions.

The current prototype translates source C programs into a
representation of combinatory boolean circuits in a format accepted by
most secure computation engines (the [Bristrol SMC circuit
syntax](https://www.cs.bris.ac.uk/Research/CryptographySecurity/MPC/)).
The tool is fully functional but is still under active development. It
still lacks support for specific features (such as division and moduli
operations, floating-point types, etc.). Please refer to the paper
[A Fast and Verified Software Stack for Secure Function Evaluation](https://dl.acm.org/citation.cfm?id=3134017) for further details.


## Instalation

This repository includes, as a submodule, the original CompCert distribution
(v2.5).

### Dependencies

In order to compiler to prototype, the following dependencies are
needed:

 * [Python3](http://python.org)
 * [Ocaml](https://ocaml.org) functional language (version 4.00 or higher)
 * [Coq](https://coq.inria.fr) proof assistant (version 8.4.6)
 * [Menhir](http://gallium.inria.fr/~fpottier/menhir/) parser
   generator (version 20171222)
 * [SsReflect](http://ssr.msr-inria.inria.fr) Ssreflect/MathComp (version 1.6.1)

All the above packages are available through the
[OPAM](https://opam.ocaml.org) (Ocaml Package Manager).

```
opam install coq.8.4.6
opam install menhir.20171222
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-algebra.1.6.1
```

### Clone the repository

The `circgen` tool reposity includes the CompCert repository as a submodule.
In order to clone it (including CompCert's repo) please perform:

```bash
$ git clone --recursive https://github.com/haslab/CircGen.git
$ cd circgen
```

### Preparing the `build` directory

The tool is compiled in a dedicated `build` directory that only has
links to both CompCert's and CircGen's source files. The toplevel `Makefile`
includes a target to setup the `build` directory.

```bash
$ make clean_setup_build_dir
$ cd build
```

### Compilation

To compile the tool, please execute ($OS is either `macosx` or `linux`):

```bash
$ ./configure bool-circ-$OS
$ make depend
$ make
```

## Examples

Directory `./tests/bcircuits` includes several examples on the usage of
the tool. These examples include standard SMC test circuits, such as
the AES symmetric cipher or the SHA-256 compression function.
