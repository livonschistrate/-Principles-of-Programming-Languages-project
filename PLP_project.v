(* string requirements *)
Require Import Strings.String.
Scheme Equality for string.
Open Scope string_scope.
Require Export Coq.Strings.String.

(* integral requirements *)
Require Import Coq.ZArith.BinInt.
Local Open Scope Z_scope.

(* requirements for cases and arrays *)
Require Import Coq.Lists.List.
Local Open Scope list_scope.

Inductive ErrorZ :=
| error_Z : ErrorZ
| number : Z -> ErrorZ.

Coercion number : Z >-> ErrorZ.

Inductive ErrorBool :=
| error_bool : ErrorBool
| boolean : bool -> ErrorBool.

Coercion boolean : bool >-> ErrorBool.

Inductive ErrorString :=
| error_string : ErrorString
| vstring : string -> ErrorString.

Coercion vstring : string >-> ErrorString.

Definition Var := string.

Inductive realVar : Type :=
| var_notdecl : realVar
| undecl_noob : realVar
| error_equal : realVar
| default : realVar
| numbr_e : ErrorZ -> realVar
| troof_e : ErrorBool -> realVar
| strng_e : ErrorString -> realVar.

Scheme Equality for realVar.

Definition Env := Var -> realVar.
Definition env_undecl : Env :=
    fun v => undecl_noob.

Definition update (env : Env) (v : string) (value : realVar) : Env :=
  fun x => if (eqb x v) then value else env x.

Inductive AExp :=
(* arithmetic expressions *)
| aconstant : ErrorZ -> AExp
| aident : Var -> AExp
| plus : AExp -> AExp -> AExp
| minus : AExp -> AExp -> AExp
| multiply : AExp -> AExp -> AExp
| divide : AExp -> AExp -> AExp
| modulo : AExp -> AExp -> AExp
| increment : AExp -> AExp
| decrement : AExp -> AExp
| maximum : AExp -> AExp -> AExp
| minimum : AExp -> AExp -> AExp
| swap : AExp -> AExp -> AExp.

Coercion aconstant : ErrorZ >-> AExp.
Coercion aident : Var >-> AExp.

(* notations for arithmetic expressions*)
Notation "'SUM' 'OF' a 'AN' b" := (plus a b) (at level 48).
Notation "'DIFF' 'OF' a 'AN' b" := (minus a b) (at level 48).
Notation "'PRODUKT' 'OF' a 'AN' b" := (multiply a b) (at level 46).
Notation "'QUOSHUNT' 'OF' a 'AN' b" := (divide a b) (at level 46).
Notation "'MOD' 'OF' a 'AN' b" := (modulo a b) (at level 46).
Notation "'BIGGR' 'OF' a 'AN' b" := (maximum a b) (at level 49).
Notation "'SMALLR' 'OF' a 'AN' b" := (minimum a b) (at level 49).
Notation "'BUFF' n" := (increment n) (at level 48).
Notation "'NERF' n" := (decrement n) (at level 48).
Notation "'FWAP' a 'WIT' b" := (swap a b) (at level 48).

(* simulating arithmetic calculus errors *)
Definition plus_err (n1 n2 : ErrorZ) : ErrorZ :=
  match n1, n2 with
  | error_Z, _ => error_Z
  | _, error_Z => error_Z
  | number n1 , number n2 => number (n1 + n2)
  end.

Definition minus_err (n1 n2 : ErrorZ) : ErrorZ :=
  match n1, n2 with
  | error_Z, _ => error_Z
  | _, error_Z => error_Z
  | number n1 , number n2 => if Z.ltb n1 n2
                       then error_Z
                       else number (n1 - n2)
  end.

Definition multiply_err (n1 n2 : ErrorZ) : ErrorZ :=
  match n1, n2 with
  | error_Z, _ => error_Z
  | _, error_Z => error_Z
  | number n1 , number n2 => number (n1 * n2)
  end.

Definition divide_err (n1 n2 : ErrorZ) : ErrorZ :=
  match n1, n2 with
  | error_Z, _ => error_Z
  | _, error_Z => error_Z
  | _, number 0 => error_Z
  | number n1 , number n2 => number (Z.div n1 n2)
  end.

Definition modulo_err (n1 n2 : ErrorZ) : ErrorZ :=
  match n1, n2 with
  | error_Z, _ => error_Z
  | _, error_Z => error_Z
  | _, number 0 => error_Z
  | number n1 , number n2 => number (Z.modulo n1 n2)
  end.

Definition incr_err (n : ErrorZ) : ErrorZ :=
  match n with
  | error_Z => error_Z
  | number n => number (n + 1)
  end.

Definition decr_err (n : ErrorZ) : ErrorZ :=
  match n with
  | error_Z => error_Z
  | number n => number (n - 1)
  end.

Definition max_err (n1 n2 : ErrorZ) : ErrorZ :=
  match n1, n2 with
  | error_Z, _ => error_Z
  | _, error_Z => error_Z
  | number n1 , number n2 => if Z.ltb n1 n2
                       then n2
                       else n1
  end.

Definition min_err (n1 n2 : ErrorZ) : ErrorZ :=
  match n1, n2 with
  | error_Z, _ => error_Z
  | _, error_Z => error_Z
  | number n1 , number n2 => if Z.ltb n1 n2
                       then n1
                       else n2
  end.

(* Definition swap_err (n1 n2 : ErrorZ) : ErrorZ :=
  match n1, n2 with
  | error_Z, _ => error_Z
  | _, error_Z => error_Z
  | number n1 , number n2 => number (SWAP n1 WIT n2)
  end. *)

(* classic semantics for arithmetic expressions - in works *)
(* Fixpoint afunct (a : AExp) (env : Env) : Z :=
  match a with
  | aident id => (env id)
  | aconstant n => n
  | plus a1 a2 => (afunct a1 env) + (afunct a2 env)
  | minus a1 a2 => (afunct a1 env) - (afunct a2 env)
  | multiply a1 a2 => (afunct a1 env) * (afunct a2 env)
  | divide a1 a2 => Z.div (afunct a1 env) (afunct a2 env)
  | modulo a1 a2 => Z.modulo (afunct a1 env) (afunct a2 env)
  | increment bf => (afunct bf env) + 1
  | decrement nf => (afunct nf env) - 1
  | maximum m1 m2 => if Z.leb (afunct m1 env) (afunct m2 env)
                     then (afunct m2 env) else (afunct m1 env)
  | minimum m1 m2 => if Z.leb (afunct m1 env) (afunct m2 env)
                     then (afunct m1 env) else (afunct m2 env)
  end. *)

(* Big-Step semantics for arithmetic expressions - in works *)
Reserved Notation "A =[ S ]=> N" (at level 60).
(*Inductive aritBS : AExp -> Env -> ErrorZ -> Prop :=
| constantBS : forall n sg, aconstant n =[ sg ]=> n
| identBS : forall id sg, aident id =[ sg ]=> (sg id)
| plusBS : forall a1 a2 i1 i2 sg n,
    a1 =[ sg ]=> i1 ->
    a2 =[ sg ]=> i2 ->
    n = i1 + i2 ->
    plus a1 a2 =[ sg ]=> n
| minusBS : forall a1 a2 i1 i2 sg n,
    a1 =[ sg ]=> i1 ->
    a2 =[ sg ]=> i2 ->
    n = i1 - i2 ->
    minus a1 a2 =[ sg ]=> n
| multBS : forall a1 a2 i1 i2 sg n,
    a1 =[ sg ]=> i1 ->
    a2 =[ sg ]=> i2 ->
    n = i1 * i2 ->
    multiply a1 a2 =[ sg ]=> n
| divBS : forall a1 a2 i1 i2 sg n,
    a1 =[ sg ]=> i1 ->
    a2 =[ sg ]=> i2 ->
    i2 > 0 ->
    n = Z.div i1 i2 ->
    divide a1 a2 =[ sg ]=> n
| modBS : forall a1 a2 i1 i2 sg n,
    a1 =[ sg ]=> i1 ->
    a2 =[ sg ]=> i2 ->
    i2 > 0 ->
    n = Z.modulo i1 i2 ->
    modulo a1 a2 =[ sg ]=> n
| incrBS : forall a i sg n,
    a =[ sg ]=> i ->
    n = i + 1 ->
    increment a =[ sg ]=> n
| decrBS : forall a i sg n,
    a =[ sg ]=> i ->
    n = i - 1 ->
    decrement a =[ sg ]=> n
(* | maxBS : forall a1 a2 i1 i2 sg n b,
    a1 =[ sg ]=> i1 ->
    a2 =[ sg ]=> i2 ->
    b = if Nat.leb i1 i2 
        then i2 else i1 ->
    maximum a1 a2 =[ sg ]=> b
| minBS : forall a1 a2 i1 i2 sg n,
    a1 =[ sg ]=> i1 ->
    a2 =[ sg ]=> i2 ->
    minimum a1 a2 =[ sg ]=> if Nat.leb i1 i2 
                            then i1 else i2  *)
where "a =[ sg ]=> n" := (aritBS a sg n). *)

(* boolean expressions *)
Inductive BExp :=
| berror : BExp
| bconst : ErrorBool -> BExp
| bident : Var -> BExp
| right : BExp
| wrong : BExp
| non : BExp -> BExp
| and : BExp -> BExp -> BExp
| or : BExp -> BExp -> BExp
| xor : BExp -> BExp -> BExp
| same : AExp -> AExp -> BExp
| diff : AExp -> AExp -> BExp
| lt : AExp -> AExp -> BExp
| gt : AExp -> AExp -> BExp
| leq : AExp -> AExp -> BExp
| geq : AExp -> AExp -> BExp.

Coercion bconst : ErrorBool >-> BExp.
Coercion bident : Var >-> BExp. 

(* notations for boolean expressions *)
Notation "'BOTH' 'OF' a 'AN' b" := (and a b) (at level 60).
Notation "'EITHER' 'OF' a 'AN' b" := (or a b) (at level 60).
Notation "'WON' 'OF' a 'AN' b" := (xor a b) (at level 60).
Notation "'NOT' n" := (non n) (at level 59).
Notation "'BOTH' 'SAEM' a 'AN' b" := (same a b) (at level 60).
Notation "'DIFFRINT' a 'AN' b" := (diff a b) (at level 60).
Notation "'DIFFRINT' 'AN' 'BIGGR' 'OF' a 'AN' b" := (lt a b) (at level 53).
Notation "'DIFFRINT' 'AN' 'SMALLR' 'OF' a 'AN' b" := (gt a b) (at level 53).
Notation "'BOTH' 'SAEM' 'AN' 'BIGGR' 'OF' a 'AN' b" := (geq a b) (at level 53).
Notation "'BOTH' 'SAEM' 'AN' 'SMALLR' 'OF' a 'AN' b" := (leq a b) (at level 53).

Definition non_err (n : ErrorBool) : ErrorBool :=
  match n with
  | error_bool => error_bool
  | boolean n => negb (n)
  end.

Definition and_err (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
  | error_bool, _ => error_bool
  | _, error_bool => error_bool
  | boolean n1 , boolean n2 => boolean (andb n1 n2)
  end.

Definition or_err (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
  | error_bool, _ => error_bool
  | _, error_bool => error_bool
  | boolean n1 , boolean n2 => boolean (orb n1 n2)
  end.

Definition xor_err (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
  | error_bool, _ => error_bool
  | _, error_bool => error_bool
  | boolean n1 , boolean n2 => boolean (xorb n1 n2)
  end.

Definition same_err (n1 n2 : ErrorZ) : ErrorBool :=
  match n1, n2 with
  | error_Z, _ => error_bool
  | _, error_Z => error_bool
  | number n1 , number n2 => boolean (Z.eqb n1 n2)
  end.

Definition lt_err (n1 n2 : ErrorZ) : ErrorBool :=
  match n1, n2 with
  | error_Z, _ => error_bool
  | _, error_Z => error_bool
  | number n1 , number n2 => boolean (Z.leb n1 n2)
  end.

(* Big-Step semantics for boolean expressions - in works *)
(* Reserved Notation "B ={ S }=> B'" (at level 70).
Inductive boolBS : BExp -> Env -> BExp -> Prop :=
| itz_tru : forall sg, right ={ sg }=> true
| itz_fls : forall sg, wrong ={ sg }=> false
| ttof : forall b sg,
    b ={ sg }=> true ->
    non b ={ sg }=> false 
| ftot : forall b sg,
    b ={ sg }=> false ->
    non b ={ sg }=> true
| tand : forall b1 b2 sg r,
    b1 ={ sg }=> true ->
    b2 ={ sg }=> r ->
    and b1 b2 ={ sg }=> r
| fand : forall b1 b2 sg,
    b1 ={ sg }=> false ->
    and b1 b2 ={ sg }=> false
| tor : forall b1 b2 sg,
    b1 ={ sg }=> true ->
    or b1 b2 ={ sg }=> true
| wfor : forall b1 b2 sg r,
    b1 ={ sg }=> false ->
    b2 ={ sg }=> r ->
    or b1 b2 ={ sg }=> r
| fxor : forall b1 b2 sg r,
    b1 ={ sg }=> r ->
    b2 ={ sg }=> r ->
    xor b1 b2 ={ sg }=> false
| txor : forall b1 b2 sg r1 r2,
    b1 ={ sg }=> r1 ->
    b2 ={ sg }=> r2 ->
    xor b1 b2 ={ sg }=> true 
| lessthan : forall a1 a2 i1 i2 sg r,
    a1 =[ sg ]=> i1 ->
    a2 =[ sg ]=> i2 ->
    r = Z.leb i1 i2 ->
    lt a1 a2 ={ sg }=> r
where "B ={ S }=> B'" := (boolBS B S B'). *)

(* string expressions *)
Inductive StExp :=
| serror : StExp
| sconstant : ErrorString -> StExp
| sident : Var -> StExp
| sconcat : ErrorString -> ErrorString -> StExp
| slength : StExp -> StExp -> StExp
| scomp : StExp -> StExp -> StExp.

Coercion sconstant : ErrorString >-> StExp.
Coercion sident : Var >-> StExp.


(* Definition err_len (s : ErrorString) : ErrorZ :=
  match s with
  | error_string => error_Z
  | vstring s => length s
  end. *)

Definition err_cat (s1 s2 : ErrorString) : ErrorString :=
  match s1, s2 with
  | error_string, _ => error_string
  | _, error_string => error_string
  | vstring s1, vstring s2 => vstring (s1 ++ s2)
  end. 

Inductive VExp :=
| error_vector : VExp
| vector_int : Var -> Z -> list Z -> VExp
| vector_bool : Var -> bool -> list bool -> VExp
| vecotr_str : Var -> string -> list string -> VExp.

Notation "a '[' n ']' ":=(vector_int a n) (at level 50).
Notation "a '|' n '|' ":=(vector_bool a n) (at level 50).
(* Notation "a '/' n '\' ":=(vector_str a n) (at level 50). *)

(* flow controls + assignment + sequence *)
Inductive Stmt :=
| decl_equals_Z : Var -> AExp -> Stmt
| decl_equals_bool : Var -> BExp -> Stmt
| decl_equals_string : Var -> StExp -> Stmt
| decl_equals_vectZ : Var -> Stmt -> VExp -> Stmt
| decl_equals_vectbool : Var -> Stmt -> VExp -> Stmt
| decl_equals_vectstring : Var -> Stmt -> VExp -> Stmt
| decl : Var -> Stmt
| equals : Var -> AExp -> Stmt
| seqinflow : Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| forsq_any : Stmt -> Stmt -> BExp -> Stmt -> Stmt
| break : Stmt
| continue : Stmt
| forsq_buff : Stmt -> BExp -> Stmt -> Stmt
| forsq_nerf : Stmt -> BExp -> Stmt -> Stmt
| switch : AExp -> list Cases -> Stmt
with Cases :=
    | case_nr : AExp -> Stmt -> Cases
    | default_case : Stmt -> Cases.

(* notations for flow controls *)
Notation " 'I' 'HAS' 'A' 'NUMBR' a 'ITZ' b" := (decl_equals_Z a b) (at level 50).
Notation " 'I' 'HAS' 'A' 'ANUMBR' a 'ITZ' b" := (decl_equals_vectZ a b) (at level 50).
Notation " 'I' 'HAS' 'A' 'TROOF' a 'ITZ' b" := (decl_equals_bool a b) (at level 50).
Notation " 'I' 'HAS' 'A' 'ATROOF' a 'ITZ' b" := (decl_equals_vectbool a b) (at level 50).
Notation " 'I' 'HAS' 'A' 'YARN' a 'ITZ' b" := (decl_equals_string a b) (at level 50).
Notation " 'I' 'HAS' 'A' 'AYARN' a 'ITZ' b" := (decl_equals_vectstring a b) (at level 50).
Notation " 'I' 'HAS' 'A' a" := (decl a) (at level 50).
Notation "a 'AN' b" := (seqinflow a b)(at level 90).
Notation "a 'R' b" := (equals a b) (at level 50).
Notation " cond 'O' 'RLY?' 'YA' 'RLY' s1 'NO' 'WAI' s2 'OIC'" := (ifthenelse cond s1 s2) (at level 95).
Notation " cond 'O' 'RLY?' 'YA' 'RLY' s 'OIC'" := (ifthen cond s) (at level 95).
Notation " 'IM' 'IN' 'YR' 'LOOP' 'WHILE' cond s 'IM' 'OUTTA' 'YR' 'LOOP'" := (while cond s) (at level 95).
Notation " 'IM' 'IN' 'YR' 'LOOP' 'BUFFIN' 'YR' a 'TIL' cond s 'IM' 'OUTTA' 'YR' 'LOOP'" := (forsq_buff a cond s) (at level 95).
Notation " 'IM' 'IN' 'YR' 'LOOP' 'NERFIN' 'YR' a 'TIL' cond s 'IM' 'OUTTA' 'YR' 'LOOP'" := (forsq_nerf a cond s) (at level 95).
Notation " 'IM' 'IN' 'YR' 'LOOP' oper 'YR' a 'TIL' cond s 'IM' 'OUTTA' 'YR' 'LOOP'" := (forsq_any oper a cond s) (at level 95).
Notation "'ENUF'" := (break) (at level 90).
Notation "'GOON'" := (continue) (at level 90).

(* notatii pentru functia switch() *)
Notation "var ', WTF?' C1 .. Cn 'OIC'" := (switch var (cons C1 .. (cons Cn nil) .. )) (at level 97).
Notation "'OMG' val seq" := (case_nr val seq) (at level 97).
Notation "'OMGWTF' seq" := (default_case seq) (at level 97).

(* input-output functions *)
Inductive InAndOut :=
| scan : Var -> InAndOut
| write : string -> InAndOut.

Notation "'GIMMEH' var" := (scan var)(at level 91).
Notation "'VISIBLE' var" := (write var)(at level 91).

Inductive Code :=
| seqwhole : Code -> Code -> Code
| mainf : Code -> Code.

Notation "'HAI 1.2' seq 'KTHXBYE'" := (mainf seq) (at level 94).
Notation "a ; b" := (seqwhole a b) (at level 90).







