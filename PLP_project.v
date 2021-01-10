(* string requirements *)
Require Import Strings.String.
Local Open Scope string_scope.
Scheme Equality for string.
Require Import Ascii.

(* integral requirements *)
Require Import Coq.ZArith.BinInt.
Local Open Scope Z_scope.

(* requirements for cases and arrays *)
Local Open Scope list_scope.

Inductive ErrorZ : Type := (* variabila int = NUMBR *)
| error_Z : ErrorZ
| number : Z -> ErrorZ.
Coercion number : Z >-> ErrorZ.

Inductive ErrorBool : Type := (* variabila bool = TROOF *)
| error_bool : ErrorBool
| boolean : bool -> ErrorBool.
Coercion boolean : bool >-> ErrorBool.

Inductive ErrorString : Type := (* variabila string = YARN *)
| error_string : ErrorString
| vstring : string -> ErrorString.
Coercion vstring : string >-> ErrorString.

Inductive realVar :=
| var_notdecl : realVar
| error_equal : realVar
| default : realVar
| numbr_e : ErrorZ -> realVar
| troof_e : ErrorBool -> realVar
| strng_e : ErrorString -> realVar.

Check numbr_e. Check ErrorZ.

Scheme Equality for realVar.

Definition Env := string -> realVar.
Definition env_notdecl : Env :=
    fun v => var_notdecl.

Definition CheckVar (a : realVar) (b : realVar) : bool := (* se verifica daca acea variabila exista *)
  match a with
  | var_notdecl => match b with
                   | var_notdecl => true
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
  fun y => if (string_beq y s)
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



(* string expressions *)
Inductive StExp :=
| sconstant : ErrorString -> StExp
| sident : string -> StExp
| sconcat : StExp -> StExp -> StExp.

Coercion sconstant : ErrorString >-> StExp.

Definition convert_string (s: ErrorString) : string := 
  match s with
  | error_string => ""
  | vstring s' => s'
  end.

Notation "'CONCAT' a 'WIT' b" := (sconcat a b) (at level 50).

(* Check length(convert_string "long"). *)

Definition err_cat (s1 s2 : ErrorString) : ErrorString :=
  match s1, s2 with
  | error_string, _ => error_string
  | _, error_string => error_string
  | vstring s1, vstring s2 => vstring (s1 ++ s2)
  end. 

(* Big-Step semantics for string expressions *)
Reserved Notation "st -[ S ]-> st'" (at level 50).
Inductive stringBS : StExp -> Env -> ErrorString -> Prop :=
| sconstantBS : forall s sg, sconstant s -[ sg ]-> s
| sidentBS : forall sid sg, sident sid -[ sg ]-> match (sg sid) with
                                              | strng_e sid => sid
                                              | _ => ""
                                              end
| scatBS : forall s1 s2 r i1 i2 sg,
    s1 -[ sg ]-> i1 ->
    s2 -[ sg ]-> i2 ->
    r = err_cat i1 i2 ->
    sconcat s1 s2 -[ sg ]-> r
where "st -[ S ]-> st'" := (stringBS st S st').

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
| swap : AExp -> AExp -> AExp
| len : StExp -> AExp.

Coercion aconstant : ErrorZ >-> AExp.
Coercion aident : string >-> AExp.

(* notations for arithmetic expressions*)
Notation "'SUM' 'OF' a 'AN' b" := (plus a b) (at level 20).
Notation "'DIFF' 'OF' a 'AN' b" := (minus a b) (at level 20).
Notation "'PRODUKT' 'OF' a 'AN' b" := (multiply a b) (at level 24).
Notation "'QUOSHUNT' 'OF' a 'AN' b" := (divide a b) (at level 24).
Notation "'MOD' 'OF' a 'AN' b" := (modulo a b) (at level 24).
Notation "'BIGGR' 'OF' a 'AN' b" := (maximum a b) (at level 40).
Notation "'SMALLR' 'OF' a 'AN' b" := (minimum a b) (at level 40).
Notation "'BUFF' n" := (increment n) (at level 20).
Notation "'NERF' n" := (decrement n) (at level 20).
Notation "'FWAP' a 'WIT' b" := (swap a b) (at level 45).
Notation "'LANG' 'OF' a" := (len a) (at level 46).

Check (SUM OF 3 AN 4).
Check (DIFF OF "a" AN 2).
Check (BUFF 15).
Check (NERF "i").
Check (LANG OF "b").


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
  | number n1 , number n2 => match n1, n2 with
                             | number n1 => n2
                             | number n2 => n1
                             end
  end. 

  aici n-am inteles cum sa-l implementez *)

(* Big-Step semantics for arithmetic expressions *)
Reserved Notation "A =[ S ]=> N" (at level 60).
Inductive aritBS : AExp -> Env -> ErrorZ -> Prop :=
| constantBS : forall n sg, aconstant n =[ sg ]=> n
| identBS : forall aid sg, aident aid =[ sg ]=> match (sg aid) with
                                              | numbr_e aid => aid
                                              | _ => error_Z
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
(* | lenBS : forall s i sg r,
    s -[ sg ]-> i ->
    r = numbr_e (length (convert_string s)) ->
    len s =[ sg ]=> r *)
(* | swapBS : forall a1 a2 i1 i2 aux sg,
    a1 =[ sg ]=> i1 ->
    a2 =[ sg ]=> i2 ->
    aux = i1 ->
    a1 = i2 ->
    a2 = aux ->
    swap a1 a2 =[ sg ]=> *)
where "a =[ sg ]=> n" := (aritBS a sg n).

Compute (env_notdecl "a").
Example ex1 : SUM OF 3 AN 4 =[ env_notdecl ]=> 7.
Proof.
  eapply plusBS.
  eapply constantBS.
  eapply constantBS. 
  simpl. reflexivity.
Qed.

Example ex2 : MOD OF 12 AN 0 =[ env_notdecl ]=> error_Z.
Proof.
  eapply modBS.
  eapply constantBS.
  eapply constantBS.
  simpl. reflexivity.
Qed.

Example ex3 : BUFF 10 =[ env_notdecl ]=> 11.
Proof.
  eapply incrBS.
  eapply constantBS.
  simpl. reflexivity.
Qed.

Example ex4 : BIGGR OF 8 AN 5 =[ env_notdecl ]=> 8.
Proof.
  eapply maxBS.
  eapply constantBS.
  eapply constantBS.
  simpl. reflexivity.
Qed.


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
Notation "'BOTH' 'OF' a 'AN' b" := (and a b) (at level 49).
Notation "'EITHER' 'OF' a 'AN' b" := (or a b) (at level 49).
Notation "'WON' 'OF' a 'AN' b" := (xor a b) (at level 49).
Notation "'NOT' n" := (non n) (at level 49).
Notation "'BOTH' 'SAEM' a 'AN' b" := (same a b) (at level 49).
Notation "'DIFFRINT' a 'AN' b" := (diff a b) (at level 49).
Notation "'DIFFRINT' 'AN' 'BIGGR' 'OF' a 'AN' b" := (lt a b) (at level 53).
Notation "'DIFFRINT' 'AN' 'SMALLR' 'OF' a 'AN' b" := (gt a b) (at level 53).
Notation "'BOTH' 'SAEM' 'AN' 'BIGGR' 'OF' a 'AN' b" := (geq a b) (at level 53).
Notation "'BOTH' 'SAEM' 'AN' 'SMALLR' 'OF' a 'AN' b" := (leq a b) (at level 53).
Notation "'COMP' a 'WIT' b" := (scomp a b)(at level 50).

Check (NOT "x").
Check (NOT true).
Check (BOTH SAEM "a" AN BIGGR OF "a" AN "b").
Check (COMP "a" WIT "x").

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

Definition equal_strings (s1 s2 : string ) : bool :=
  if(string_dec s1 s2) 
  then true 
  else false. (* folosit pentru egalitatea a doua stringuri *)

Definition scmp (s1 s2 : ErrorString) : ErrorBool :=
  match s1, s2 with
  | error_string, _ => error_bool
  | _, error_string => error_bool
  | vstring s1 , vstring s2 => equal_strings (convert_string s1) (convert_string s2)
  end.


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
| cmpBS : forall s1 s2 i1 i2 sg r,
    s1 -[ sg ]-> i1 ->
    s2 -[ sg ]-> i2 ->
    r = scmp i1 i2 ->
    scomp s1 s2 ={ sg }=> r
where "B ={ S }=> B'" := (boolBS B S B').

Example ex5 : NOT true ={ env_notdecl }=> false.
Proof.
  eapply notBS.
  eapply bconstantBS.
  simpl. reflexivity.
Qed.

Example ex6 : BOTH OF true AN false ={ env_notdecl }=> false.
Proof.
  eapply andBS.
  eapply bconstantBS.
  eapply bconstantBS.
  simpl. reflexivity.
Qed.

Example ex7 : DIFFRINT AN BIGGR OF 7 AN 10 ={ env_notdecl }=> true.
Proof.
  eapply lessthanBS.
  eapply constantBS.
  eapply constantBS.
  simpl. reflexivity.
Qed.

Example ex8 : COMP "sb" WIT "tf" ={ env_notdecl }=> true.
Proof.
  eapply cmpBS.
  eapply sconstantBS.
  eapply sconstantBS.
  simpl. 
Abort.


Inductive VExp :=
| error_vector : VExp
| vector_int : Z -> list Z -> VExp.


(* flow controls + assignment + sequence *)
Inductive Stmt :=
| equals_Z : string -> AExp -> Stmt
| equals_bool : string -> BExp -> Stmt
| equals_string : string -> StExp -> Stmt
| equalsvect_Z: string -> VExp -> Stmt
| decl_vectZ : string -> VExp -> Stmt
| decl_Z : string -> Stmt
| decl_bool : string -> Stmt
| decl_string : string -> Stmt
| seqinflow : Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| whileseq : BExp -> Stmt -> Stmt
| forsq_any : Stmt -> Stmt -> BExp -> Stmt -> Stmt
| break : Stmt
| continue : Stmt
| comment : string -> Stmt
| switch : AExp -> list Cases -> Stmt
with Cases :=
    | case_nr : AExp -> Stmt -> Cases
    | default_case : Stmt -> Cases.

(* notations for flow controls *)
Notation "a 'AND' b" := (seqinflow a b)(at level 90). (*pentru secventele folosite in partea de conditional*)
Notation "a ; b" := (seqinflow a b) (at level 90).
Notation "'BTW' comm" := (comment comm) (at level 90).
Notation "'OBTW' comm 'TLDR'" := (comment comm) (at level 90).


Notation " a 'ITZ' b" := (equals_Z a b) (at level 50).
Notation " a 'ITZB' b" := (equals_bool a b) (at level 50).
Notation " a 'ITS' b" := (equals_string a b) (at level 50).
Notation " 'I' 'HAS' 'A' 'ANUMBR' a [ n ] " := (decl_vectZ a (vector_int n nil)) (at level 80).
Notation " 'I' 'HAS' 'A' 'NUMBR' a" := (decl_Z a) (at level 80).
Notation " 'I' 'HAS' 'A' 'TROOF' a" := (decl_bool a) (at level 80).
Notation " 'I' 'HAS' 'A' 'YARN' a" := (decl_string a) (at level 80).



Notation " cond 'O_RLY?' 'YA_RLY' { s1 } 'NO_WAI' { s2 } 'OIC'" := (ifthenelse cond s1 s2) (at level 95).
Notation " cond 'O_RLY?' 'YA_RLY' { s } 'OIC'" := (ifthen cond s) (at level 95).
Notation " 'IM_IN_YR_WHILE' cond s 'IM_OUTTA_YR_WHILE'" := (whileseq cond s) (at level 95).
Notation " 'IM_IN_YR_LOOP' oper 'YR' a 'WILE' cond { s } 'IM_OUTTA_YR_LOOP'" := (forsq_any oper a cond s) (at level 95).
Notation "'ENUF'" := (break) (at level 80).
Notation "'GOON'" := (continue) (at level 80).

Check (I HAS A NUMBR "a" ; "a" ITZ 12).
Check (I HAS A ANUMBR "a" [30]).
Check (I HAS A TROOF "b" ; "b" ITZB false).
Check ( "c" ITS "ff").

(* notatii pentru functia switch() *)
Notation "var ',WTF?' C1 ;; C2 ;; .. ;; Cn 'OIC'" := (switch var (cons C1 (cons C2 .. (cons Cn nil) .. ))) (at level 99).
Notation "'OMG' val { seq }" := (case_nr val seq) (at level 99).
Notation "'OMGWTF' { seq }" := (default_case seq) (at level 99).

(* input-output functions *)
Inductive InAndOut :=
| scan : string -> InAndOut
| write : string -> InAndOut.

Notation "'GIMMEH' var" := (scan var)(at level 91).
Notation "'VISIBLE' var" := (write var)(at level 91).


Reserved Notation "S -{ sg }-> sg'" (at level 75).
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
| equal_stringBS : forall a i x sg sg',
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
    whileseq b s -{ sg }-> sg
| whiletrueBS : forall b s sg sg',
    b ={ sg }=> true ->
    (s ; whileseq b s) -{ sg }-> sg' ->
    whileseq b s -{ sg }-> sg'
| forany_trueBS : forall init cond op s sg sg',
    cond ={ sg }=> true ->
    ( init ; whileseq cond (s ; op) ) -{ sg }-> sg' ->
    forsq_any op init cond s -{ sg }-> sg'
| forany_falseBS : forall init cond op s sg sg',
    cond ={ sg }=> false ->
    forsq_any op init cond s -{ sg }-> sg'
| breakBS : forall s sg,
    s -{ sg }-> sg
| continueBS : forall s sg sg',
    s -{ sg }-> sg'
| switchBS : forall a i case b s sg sg',
    a =[ sg ]=> i ->
    b = same i case ->
    switch a s -{ sg }-> sg'
where "s -{ sg }-> sg'" := (strBS s sg sg').

Check (SUM OF "VAR" AN 1).

Check(same "ANIMAL" "CAT")
  O_RLY?
    YA_RLY 
    { "CAT" ITS "ok" }
  OIC.

Check I HAS A NUMBR "A"; "A" ITZ 0 ; 
  whileseq (BOTH SAEM "A" AN 8)  
  ("A" ITZ SUM OF "A" AN 2 ) .

Check I HAS A NUMBR "B" ; "B" ITZ 1 ;
  forsq_any ("i" ITZ SUM OF "i" AN 1) ("i" ITZ 1) (BOTH SAEM "i" AN 4)
  ("B" ITZ PRODUKT OF "B" AN 2).

Check BTW "notatie".
Check OBTW "alta notatie" TLDR.

(* Check switch "var"
      case_nr 3 "a" ITZ 0
      case_nr 2 "a" ITZ 1
      .
 *)

Compute (I HAS A NUMBR "n" ; "n" ITZ 4).

Example ex8 : exists sg', ("n" ITZ 4 ; "n" ITZ 9) -{ env_notdecl }-> sg' /\ sg' "n" = numbr_e 9.
Proof.
  eexists.
  split.
  - eapply seqBS.
    eapply equal_ZBS. eapply constantBS. reflexivity.
    eapply equal_ZBS. eapply constantBS. reflexivity.
  - unfold update. simpl. (* reflexivity. *)      
Admitted.       
    




