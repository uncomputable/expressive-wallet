# Coq Project

Formal specification and correctness proofs about expressive wallets.

## Develop the project

Enter a nix shell.

```bash
nix-shell -p coq
```

To use CoqIDE, add its nix package to the nix shell.

```bash
nix-shell -p coq coqPackages.coqide
```

## Build the project

First, enter the development environment (see above).

Then generate and execute the Coq makefile.

```bash
coq_makefile -f _CoqProject -o CoqMakefile
make -f CoqMakeFile
```
