From Coq Require Extraction.
Require Import Expressive.Wallet.

Extraction Language OCaml.

(* Extract Coq's bool as OCaml's bool *)
Extract Inductive bool => "bool" [ "true" "false" ].
(* Extract Coq's list as OCaml's list *)
Extract Inductive list => "list" [ "[]" "(::)" ].
(* Extract Coq's nat as OCaml's int *)
(* XXX: OCaml's int is bounded *)
(* Theorems about large numbers might break *)
Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n -> if n=0 then zero () else succ (n-1))".

Extraction "strategy" strategy.
