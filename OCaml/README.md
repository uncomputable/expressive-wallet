# OCaml Project

Interactive tool that uses formally verified algorithms to generate expressive wallets.

## Develop the project

Enter a nix shell with OCaml support.

```bash
nix-shell -p ocaml
```

## Build the project

First, you need to build the [Coq project](https://github.com/uncomputable/expressive-wallet/blob/master/Coq).

Copy the generated OCaml files into the OCaml directory.

```bash
cp ../Coq/*.{ml,mli} .
```

Enter the development environment (see above).

Then run the OCaml compiler.

```bash
ocamlopt -c strategy.mli
ocamlopt -o wallet strategy.ml main.ml
```
