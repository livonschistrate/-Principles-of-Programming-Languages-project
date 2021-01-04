(* string requirements *)
Require Import Strings.String.
Local Open Scope string_scope.
Scheme Equality for string.

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

(* Inductive Var := 
| id : string -> Var.
Coercion id : string >-> Var. *)

Inductive realVar :=
| var_notdecl : realVar
| undecl_noob : realVar
| error_equal : realVar
| default : realVar
| numbr_e : ErrorZ -> realVar
| troof_e : ErrorBool -> realVar
| strng_e : ErrorString -> realVar.

Scheme Equality for realVar.

Definition Env := string -> realVar.
Definition env_notdecl : Env :=
    fun v => var_notdecl.

Definition CheckVar (a : realVar) (b : realVar) : bool :=
  match a with
  | var_notdecl => match b with
                   | var_notdecl => true
                   | _ => false
                   end
  | undecl_noob => match b with
                   | undecl_noob => true
                   | _ => false
                   end
  | error_equal => match b with
                   | error_equal => true
                   | _ => false
                   end
  | numbr_e n1 => match b with
                   | numbr_e n2 => true
                   | _ => false
                   end
  | troof_e b1 => match b with
                   | troof_e b2 => true
                   | _ => false
                   end
  | strng_e s1 => match b with
                   | strng_e s2 => true
                   | _ => false
                   end
  | default => match b with
                   | default => true
                   | _ => false
                   end
end.

Definition update (env : Env) (s : string) (x : realVar) : Env :=
  fun y => if (eqb y s)
              then 
              if (andb (CheckVar (var_notdecl) (env y)) (negb(CheckVar (default) (x))))
              then var_notdecl
              else
                if (andb (CheckVar (var_notdecl) (env y)) (CheckVar (default) (x)))
                then default
                else
                  if (orb (CheckVar (default) (env y)) (CheckVar (x) (env y)))
                  then x
                  else error_equal
            else env y.


(* Definition update (env : Env) (v : string) (value : realVar) : Env :=
  fun x => if (eqb x v) then value else env x. *)

Inductive AExp :=
(* arithmetic expressions *)
| aconstant : ErrorZ -> AExp
| aident : string -> AExp
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
Coercion aident : string >-> AExp.

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

Check (SUM OF 3 AN 4).
Check (DIFF OF "a" AN 2).
Check (BUFF 15).
Check (NERF "i").


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
(* Fixpoint afunct (a : AExp) (env : Env) : ErrorZ :=
  match a with
  | aident aid => match (env aid) with
                 | numbr_e n => n
                 | _ => error_Z
                 end
  | aconstant n => n
  | plus a1 a2 => plus_err(afunct a1 env) (afunct a2 env)
  | minus a1 a2 => minus_err(afunct a1 env) (afunct a2 env)
  | multiply a1 a2 => multiply_err(afunct a1 env) (afunct a2 env)
  | divide a1 a2 => divide_err(afunct a1 env) (afunct a2 env)
  | modulo a1 a2 => modulo_err (afunct a1 env) (afunct a2 env)
  | increment bf => incr_err (afunct bf env)
  | decrement nf => decr_err (afunct nf env)
  | maximum m1 m2 => max_err (afunct m1 env) (afunct m2 env)
                     
  | minimum m1 m2 => min_err (afunct m1 env) (afunct m2 env)
                    
  end. *)

(* Big-Step semantics for arithmetic expressions - in works *)
Reserved Notation "A =[ S ]=> N" (at level 60).
Inductive aritBS : AExp -> Env -> ErrorZ -> Prop :=
| constantBS : forall n sg, aconstant n =[ sg ]=> n
| identBS : forall aid sg, aident aid =[ sg ]=> match (sg aid) with
                                              | numbr_e aid => aid
                                              | _ => 0
                                              end
| plusBS : forall a1 a2 i1 i2 sg n,
    a1 =[ sg ]=> i1 ->
    a2 =[ sg ]=> i2 ->
    n = plus_err i1 i2 ->
    plus a1 a2 =[ sg ]=> n
| minusBS : forall a1 a2 i1 i2 sg n,
    a1 =[ sg ]=> i1 ->
    a2 =[ sg ]=> i2 ->
    n = minus_err i1 i2 ->
    minus a1 a2 =[ sg ]=> n
| multBS : forall a1 a2 i1 i2 sg n,
    a1 =[ sg ]=> i1 ->
    a2 =[ sg ]=> i2 ->
    n = multiply_err i1 i2 ->
    multiply a1 a2 =[ sg ]=> n
| divBS : forall a1 a2 i1 i2 sg n,
    a1 =[ sg ]=> i1 ->
    a2 =[ sg ]=> i2 ->
    n = divide_err i1 i2 ->
    divide a1 a2 =[ sg ]=> n
| modBS : forall a1 a2 i1 i2 sg n,
    a1 =[ sg ]=> i1 ->
    a2 =[ sg ]=> i2 ->
    n = modulo_err i1 i2 ->
    modulo a1 a2 =[ sg ]=> n
| incrBS : forall a i sg n,
    a =[ sg ]=> i ->
    n = incr_err i ->
    increment a =[ sg ]=> n
| decrBS : forall a i sg n,
    a =[ sg ]=> i ->
    n = decr_err i ->
    decrement a =[ sg ]=> n
| maxBS : forall a1 a2 i1 i2 sg b,
    a1 =[ sg ]=> i1 ->
    a2 =[ sg ]=> i2 ->
    b = max_err i1 i2 ->
    maximum a1 a2 =[ sg ]=> b
| minBS : forall a1 a2 i1 i2 sg b,
    a1 =[ sg ]=> i1 ->
    a2 =[ sg ]=> i2 ->
    b = min_err i1 i2 ->
    minimum a1 a2 =[ sg ]=> b
where "a =[ sg ]=> n" := (aritBS a sg n).

(* string expressions *)
Inductive StExp :=
| sconstant : ErrorString -> StExp
| sident : string -> StExp
| sconcat : StExp -> StExp -> StExp
| slen : StExp -> StExp -> StExp.

Coercion sconstant : ErrorString >-> StExp.
Coercion sident : string >-> StExp.

(* Notation "'COMP' a 'WIT' b" := (scomp a b)(at level 50). *)
(* Notation "'CONCAT' a 'WIT' b" := (sconcat a b) (at level 50). *)

(* Check length("long"). *)

Definition err_cat (s1 s2 : ErrorString) : ErrorString :=
  match s1, s2 with
  | error_string, _ => error_string
  | _, error_string => error_string
  | vstring s1, vstring s2 => vstring (s1 ++ s2)
  end. 

(* Definition err_len (s : ErrorString) := 
  match s with
  | nostring => Z0
  | estring c s' => 1 + lenh s'
  end. *)

(* Definition comp_err (s1 s2 : ErrorString) : ErrorZ :=
  match s1, s2 with
  | error_string, _ => error_Z
  | _, error_string => error_Z
  | vstring s1 , vstring s2 => if boolean (Z.ltb (length(s1) length(s2)))
                       then -1
                       else if boolean (Z.eq (length(s1) length(s2)))
                            then 0
                            else 1
  end.
 *)

(* boolean expressions *)
Inductive BExp :=
| bconstant : ErrorBool -> BExp
| bident : string -> BExp
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
| geq : AExp -> AExp -> BExp
| scomp : StExp -> StExp -> BExp.

Coercion bconstant : ErrorBool >-> BExp.
Coercion bident : string >-> BExp. 

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

Check (NOT "x").
Check (NOT true).
Check (BOTH SAEM "a" AN BIGGR OF "a" AN "b").

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

Definition diff_err (n1 n2 : ErrorZ) : ErrorBool :=
  match n1, n2 with
  | error_Z, _ => error_bool
  | _, error_Z => error_bool
  | number n1 , number n2 => boolean (negb(Z.eqb n1 n2))
  end.

Definition lt_err (n1 n2 : ErrorZ) : ErrorBool :=
  match n1, n2 with
  | error_Z, _ => error_bool
  | _, error_Z => error_bool
  | number n1 , number n2 => boolean (Z.ltb n1 n2)
  end.

Definition gt_err (n1 n2 : ErrorZ) : ErrorBool :=
  match n1, n2 with
  | error_Z, _ => error_bool
  | _, error_Z => error_bool
  | number n1 , number n2 => boolean (Z.ltb n2 n1)
  end.

Definition leq_err (n1 n2 : ErrorZ) : ErrorBool :=
  match n1, n2 with
  | error_Z, _ => error_bool
  | _, error_Z => error_bool
  | number n1 , number n2 => boolean (Z.leb n1 n2)
  end.

Definition geq_err (n1 n2 : ErrorZ) : ErrorBool :=
  match n1, n2 with
  | error_Z, _ => error_bool
  | _, error_Z => error_bool
  | number n1 , number n2 => boolean (Z.leb n2 n1)
  end.

(* Definition scmp (s1 s2 : ErrorString) : ErrorString :=
  fun  *)


(* Big-Step semantics for boolean expressions - in works *)
Reserved Notation "B ={ S }=> B'" (at level 70).
Inductive boolBS : BExp -> Env -> ErrorBool -> Prop :=
| itz_tru : forall sg, right ={ sg }=> true
| itz_fls : forall sg, wrong ={ sg }=> false
| bconstantBS : forall b sg, bconstant b ={ sg }=> b
| bidentBS : forall bid sg, bident bid ={ sg }=> match (sg bid) with
                                              | troof_e bid => bid
                                              | _ => false
                                              end
(* | ttof : forall b sg,
    b ={ sg }=> true ->
    non b ={ sg }=> false 
| ftot : forall b sg,
    b ={ sg }=> false ->
    non b ={ sg }=> true *)
| notBS : forall sg b b' i1,
    b ={ sg }=> i1 ->
    b' = (non_err i1) ->
    (non b) ={ sg }=> b'
(* | tand : forall b1 b2 sg r,
    b1 ={ sg }=> true ->
    b2 ={ sg }=> r ->
    and b1 b2 ={ sg }=> r
| fand : forall b1 b2 sg,
    b1 ={ sg }=> false ->
    and b1 b2 ={ sg }=> false *)
| andBS : forall sg b1 b2 i1 i2 b,
    b1 ={ sg }=> i1 ->
    b2 ={ sg }=> i2 ->
    b = (and_err i1 i2) ->
    and b1 b2 ={ sg }=> b
(* | tor : forall b1 b2 sg,
    b1 ={ sg }=> true ->
    or b1 b2 ={ sg }=> true
| wfor : forall b1 b2 sg r,
    b1 ={ sg }=> false ->
    b2 ={ sg }=> r ->
    or b1 b2 ={ sg }=> r *)
| orBS : forall sg b1 b2 i1 i2 b,
    b1 ={ sg }=> i1 ->
    b2 ={ sg }=> i2 ->
    b = (or_err i1 i2) ->
    or b1 b2 ={ sg }=> b
(* | fxor : forall b1 b2 sg r,
    b1 ={ sg }=> r ->
    b2 ={ sg }=> r ->
    xor b1 b2 ={ sg }=> false
| txor : forall b1 b2 sg r1 r2,
    b1 ={ sg }=> r1 ->
    b2 ={ sg }=> r2 ->
    xor b1 b2 ={ sg }=> true  *)
| xorBS : forall sg b1 b2 i1 i2 b,
    b1 ={ sg }=> i1 ->
    b2 ={ sg }=> i2 ->
    b = (xor_err i1 i2) ->
    xor b1 b2 ={ sg }=> b
| lessthanBS : forall a1 a2 i1 i2 sg r,
    a1 =[ sg ]=> i1 ->
    a2 =[ sg ]=> i2 ->
    r = lt_err i1 i2 ->
    lt a1 a2 ={ sg }=> r
| greaterthanBS : forall a1 a2 i1 i2 sg r,
    a1 =[ sg ]=> i1 ->
    a2 =[ sg ]=> i2 ->
    r = gt_err i1 i2 ->
    gt a1 a2 ={ sg }=> r
| lesseqBS : forall a1 a2 i1 i2 sg r,
    a1 =[ sg ]=> i1 ->
    a2 =[ sg ]=> i2 ->
    r = leq_err i1 i2 ->
    lt a1 a2 ={ sg }=> r
| greatereqBS : forall a1 a2 i1 i2 sg r,
    a1 =[ sg ]=> i1 ->
    a2 =[ sg ]=> i2 ->
    r = geq_err i1 i2 ->
    geq a1 a2 ={ sg }=> r
where "B ={ S }=> B'" := (boolBS B S B').


Inductive VExp :=
| error_vector : VExp
| vector_int : Z -> list Z -> VExp
| vector_bool : bool -> list bool -> VExp.

(* Notation "a '[' n ']' ":=(vector_int a n) (at level 50).
Notation "a '|' n '|' ":=(vector_bool a n) (at level 50). *)

(* flow controls + assignment + sequence *)

Inductive Stmt :=
| equals_Z : string -> AExp -> Stmt
| equals_bool : string -> BExp -> Stmt
| equals_string : string -> StExp -> Stmt
| decl_vectZ : string -> AExp -> VExp -> Stmt
| decl_vectbool : string -> Stmt -> VExp -> Stmt
| decl_Z : string -> Stmt
| decl_bool : string -> Stmt
| decl_string : string -> Stmt
| equals : string -> AExp -> Stmt
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
Notation " a 'ITZ' b" := (equals_Z a b) (at level 50).
Notation " a 'ITZB' b" := (equals_bool a b) (at level 50).
Notation " a 'ITS' b" := (equals_string a b) (at level 50).
Notation " 'I' 'HAS' 'A' 'ANUMBR' a [ n ] " := (decl_vectZ a (number n)) (at level 50).
Notation " 'I' 'HAS' 'A' 'ATROOF' a { n }" := (decl_vectbool a (number n)) (at level 50).
Notation " 'I' 'HAS' 'A' 'NUMBR' a" := (decl_Z a) (at level 50).
Notation " 'I' 'HAS' 'A' 'TROOF' a" := (decl_bool a) (at level 50).
Notation " 'I' 'HAS' 'A' 'YARN' a" := (decl_string a) (at level 50).

Notation "a 'AN' b" := (seqinflow a b)(at level 90). (*pentru secventele folosite in partea de conditional*)
Notation "a ; b" := (seqinflow a b) (at level 90).
Notation "a 'R' b" := (equals a b) (at level 50).

Notation " cond 'O' 'RLY?' 'YA' 'RLY' s1 'NO' 'WAI' s2 'OIC'" := (ifthenelse cond s1 s2) (at level 95).
Notation " cond 'O' 'RLY?' 'YA' 'RLY' s 'OIC'" := (ifthen cond s) (at level 95).
Notation " 'IM' 'IN' 'YR' 'LOOP' 'WHILE' cond s 'IM' 'OUTTA' 'YR' 'LOOP'" := (while cond s) (at level 95).
(* Notation " 'IM' 'IN' 'YR' 'LOOP' 'BUFFIN' 'YR' a 'TIL' cond s 'IM' 'OUTTA' 'YR' 'LOOP'" := (forsq_buff a cond s) (at level 95).
Notation " 'IM' 'IN' 'YR' 'LOOP' 'NERFIN' 'YR' a 'TIL' cond s 'IM' 'OUTTA' 'YR' 'LOOP'" := (forsq_nerf a cond s) (at level 95). *)
Notation " 'IM' 'IN' 'YR' 'LOOP' oper 'YR' a 'TIL' cond s 'IM' 'OUTTA' 'YR' 'LOOP'" := (forsq_any oper a cond s) (at level 95).
Notation "'ENUF'" := (break) (at level 90).
Notation "'GOON'" := (continue) (at level 90).

Check (I HAS A NUMBR "a" ; "a" R 12).
Check (I HAS A ANUMBR "a" [ 30 ]).
Check (I HAS A NUMBR "b" ; "b" ITZ 10).

(* notatii pentru functia switch() *)
Notation "var ', WTF?' C1 .. Cn 'OIC'" := (switch var (cons C1 .. (cons Cn nil) .. )) (at level 97).
Notation "'OMG' val seq" := (case_nr val seq) (at level 97).
Notation "'OMGWTF' seq" := (default_case seq) (at level 97).

(* input-output functions *)
Inductive InAndOut :=
| scan : string -> InAndOut
| write : string -> InAndOut.

Notation "'GIMMEH' var" := (scan var)(at level 91).
Notation "'VISIBLE' var" := (write var)(at level 91).

Inductive Code :=
| seqwhole : Code -> Code -> Code
| mainf : Stmt -> Code.

Notation "'HAI 1.2' seq 'KTHXBYE'" := (mainf seq) (at level 94).

Reserved Notation "S -{ sg }-> sg'" (at level 60).
Inductive strBS : Stmt -> Env -> Env -> Prop :=
| decl_ZBS : forall i x sg sg',
    sg' = (update sg x (numbr_e i)) ->
    decl_Z x -{ sg }-> sg'
| decl_BoolBS : forall i x sg sg',
    sg' = (update sg x (troof_e i)) ->
    decl_bool x -{ sg }-> sg'
| decl_StringBS : forall i x sg sg',
    sg' = (update sg x (strng_e i)) ->
    decl_string x -{ sg }-> sg'
| equal_ZBS : forall a i x sg sg',
    a =[ sg ]=> i ->
    sg' = (update sg x (numbr_e i)) ->
    equals_Z x a -{ sg }-> sg'
| equal_boolBS : forall a i x sg sg',
    a ={ sg }=> i ->
    sg' = (update sg x (troof_e i)) ->
    equals_bool x a -{ sg }-> sg'
| equalZBS : forall a i x sg sg',
    sg' = (update sg x (strng_e i)) ->
    equals_string x a -{ sg }-> sg'
| seqBS : forall s1 s2 sg sg1 sg2,
    s1 -{ sg }-> sg1 ->
    s2 -{ sg1 }-> sg2 ->
    seqinflow s1 s2 -{ sg }-> sg2
| ifelse_falseBS : forall cond s1 s2 sg sg',
    cond ={ sg }=> false ->
    s2 -{ sg }-> sg' ->
    ifthenelse cond s1 s2 -{ sg }-> sg'
| ifelse_trueBS : forall cond s1 s2 sg sg',
    cond ={ sg }=> true ->
    s1 -{ sg }-> sg' ->
    ifthenelse cond s1 s2 -{ sg }-> sg'
| iftrueBS : forall cond s sg sg',
    cond ={ sg }=> true ->
    s -{ sg }-> sg' ->
    ifthen cond s -{ sg }-> sg'
| iffalseBS : forall cond s sg sg',
    cond ={ sg }=> false ->
    ifthen cond s -{ sg }-> sg'
| whilefalseBS : forall b s sg,
    b ={ sg }=> false ->
    while b s -{ sg }-> sg
| whiletrueBS : forall b s sg sg',
    b ={ sg }=> true ->
    (s ; while b s) -{ sg }-> sg' ->
    while b s -{ sg }-> sg'
| forany_trueBS : forall init cond op s sg sg',
    cond ={ sg }=> true ->
    ( init ; while cond (s ; op) ) -{ sg }-> sg' ->
    forsq_any op init cond s -{ sg }-> sg'
| forany_falseBS : forall init cond op s sg sg',
    cond ={ sg }=> false ->
    forsq_any op init cond s -{ sg }-> sg'
(* | forbuff_trueBS : forall init cond s bf sg sg',
    cond ={ sg }=> true ->
    ( init ; while cond (s ; bf) ) -{ sg }-> sg' ->
    forsq_buff init cond s -{ sg }-> sg'
| forbuff_falseBS : forall init cond s sg sg',
    cond ={ sg }=> false ->
    forsq_buff init cond s -{ sg }-> sg'
| fornerf_trueBS : forall init cond s nf sg sg',
    cond ={ sg }=> true ->
    ( init ; while cond (s ; nf) ) -{ sg }-> sg' ->
    forsq_nerf init cond s -{ sg }-> sg'
| fornerf_falseBS : forall init cond s sg sg',
    cond ={ sg }=> false ->
    forsq_nerf init cond s -{ sg }-> sg' *)
| breakBS : forall s sg,
    s -{ sg }-> sg
| continueBS : forall s sg,
    s -{ sg }-> sg
where "s -{ sg }-> sg'" := (strBS s sg sg').




