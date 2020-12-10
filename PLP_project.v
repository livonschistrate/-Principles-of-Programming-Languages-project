Inductive Var := n | i | x | sum.
Scheme Equality for Var.

Compute (Var_eq_dec n n).
Compute (Var_eq_dec n i).

(* Environment *)
Definition Env := Var -> nat.
Definition env1 : Env :=
  fun x =>
    if (Var_eq_dec x n)
    then 10
    else 0.
Check env1.

Definition update (env : Env)
           (x : Var) (v : nat) : Env :=
  fun y =>
    if (Var_eq_dec y x)
    then v
    else (env y).

Notation "S [ V /' X ]" := (update S X V) (at level 0).

Inductive AExp :=
| avar : Var -> AExp
| anum : nat -> AExp
| aplus : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| amin : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp.

Notation "A +' B" := (aplus A B) (at level 48).
Notation "A *' B" := (amul A B) (at level 46).
Notation "A -' B" := (amin A B) (at level 48).
Notation "A /' B" := (adiv A B) (at level 46).
Notation "A %' B" := (amod A B) (at level 46).
Coercion anum : nat >-> AExp.
Coercion avar : Var >-> AExp.

Fixpoint aeval_fun (a: AExp) (env : Env) : nat :=
  match a with
  | avar var => env var
  | anum n' => n'
  | aplus a1 a2 => (aeval_fun a1 env) + (aeval_fun a2 env)
  | amin a1 a2 => (aeval_fun a1 env) - (aeval_fun a2 env)
  | amul a1 a2 => (aeval_fun a1 env) * (aeval_fun a2 env)
  | amod a1 a2 => Nat.modulo (aeval_fun a1 env) (aeval_fun a2 env)
  | adiv a1 a2 => Nat.div (aeval_fun a1 env) (aeval_fun a2 env)
  end.

Reserved Notation "A =[ S ]=> N" (at level 60).

Inductive aeval : AExp -> Env -> nat -> Prop :=
| const : forall n sigma, anum n =[ sigma ]=> n (* <n,sigma> => <n> *) 
| var : forall v sigma, avar v =[ sigma ]=> (sigma v) (* <v,sigma> => sigma(x) *)
| add : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 + i2 ->
    a1 +' a2 =[sigma]=> n
| multiply : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 * i2 ->
    a1 *' a2 =[sigma]=> n
| reduce : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 - i2 ->
    a1 -' a2 =[sigma]=> n
| divide : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    i2 > 0 ->
    n = Nat.div i1 i2 -> 
    a1 /' a2 =[sigma]=> n
| modulo : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    i2 > 0 ->
    n = Nat.modulo i1 i2 ->
    a1 %' a2 =[sigma]=> n
where "a =[ sigma ]=> n" := (aeval a sigma n).

Hint Constructors aeval.

Require Import Omega.
Example ex1 : 2 +' 2 =[ env1 ]=> 4.
Proof.
  eapply add.
  - apply const.
  - apply const.
  - omega.
Qed.

Example ex2 : 2 *' 2 =[ env1 ]=> 4.
Proof.
    eapply multiply.
    - apply const.
    - apply const.
    - omega.
Qed.

Example ex3 : 5 -' 2 =[ env1 ]=> 3.
Proof.
    eapply reduce.
    - apply const.
    - apply const.
    - omega.
Qed.

Example ex4: 16 /' 2 =[ env1 ]=> 8.
Proof.
    eapply divide.
    - apply const.
    - apply const.
    - auto.
    - auto.
Qed.

Example ex5: 27 %' 5 =[ env1 ]=> 2.
Proof.
    eapply modulo.
    - apply const.
    - apply const.
    - omega.
    - auto.
Qed.
