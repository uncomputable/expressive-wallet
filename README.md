# Expressive Wallet Problem

Trigger warning: math ⚠️

"Given a set of coin denominations, what is a minimal wallet that can express all amounts up to a target amount?"

This math problem actually has some use in daily life! Always pay the bill exactly ✅

## Example: Euro cents 1, 2, 5, 10, 20, 50

Here are minimal wallets for targets 0 to 100.

It is surprising how slowly the wallet grows with respect to the target. I can't help but see a skyscraper.

| Target | Minimal Wallet               |
|--------|------------------------------|
| 0      | []                           |
| 1      | [1]                          |
| 2      | [1, 2]                       |
| 3      | [1, 2]                       |
| 4      | [1, 2, 2]                    |
| 5      | [1, 2, 2]                    |
| 6      | [1, 2, 2, 5]                 |
| 7      | [1, 2, 2, 5]                 |
| 8      | [1, 2, 2, 5]                 |
| 9      | [1, 2, 2, 5]                 |
| 10     | [1, 2, 2, 5]                 |
| 11     | [1, 2, 2, 5, 10]             |
| 12     | [1, 2, 2, 5, 10]             |
| 13     | [1, 2, 2, 5, 10]             |
| 14     | [1, 2, 2, 5, 10]             |
| 15     | [1, 2, 2, 5, 10]             |
| 16     | [1, 2, 2, 5, 10]             |
| 17     | [1, 2, 2, 5, 10]             |
| 18     | [1, 2, 2, 5, 10]             |
| 19     | [1, 2, 2, 5, 10]             |
| 20     | [1, 2, 2, 5, 10]             |
| 21     | [1, 2, 2, 5, 10, 20]         |
| 22     | [1, 2, 2, 5, 10, 20]         |
| 23     | [1, 2, 2, 5, 10, 20]         |
| 24     | [1, 2, 2, 5, 10, 20]         |
| 25     | [1, 2, 2, 5, 10, 20]         |
| 26     | [1, 2, 2, 5, 10, 20]         |
| 27     | [1, 2, 2, 5, 10, 20]         |
| 28     | [1, 2, 2, 5, 10, 20]         |
| 29     | [1, 2, 2, 5, 10, 20]         |
| 30     | [1, 2, 2, 5, 10, 20]         |
| 31     | [1, 2, 2, 5, 10, 20]         |
| 32     | [1, 2, 2, 5, 10, 20]         |
| 33     | [1, 2, 2, 5, 10, 20]         |
| 34     | [1, 2, 2, 5, 10, 20]         |
| 35     | [1, 2, 2, 5, 10, 20]         |
| 36     | [1, 2, 2, 5, 10, 20]         |
| 37     | [1, 2, 2, 5, 10, 20]         |
| 38     | [1, 2, 2, 5, 10, 20]         |
| 39     | [1, 2, 2, 5, 10, 20]         |
| 40     | [1, 2, 2, 5, 10, 20]         |
| 41     | [1, 2, 2, 5, 10, 20, 20]     |
| ...    | ...                          |
| 60     | [1, 2, 2, 5, 10, 20, 20]     |
| 61     | [1, 2, 2, 5, 10, 20, 20, 50] |
| ...    | ...                          |
| 100    | [1, 2, 2, 5, 10, 20, 20, 50] |

## Develop the project

Enter a nix shell to obtain Coq.

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
