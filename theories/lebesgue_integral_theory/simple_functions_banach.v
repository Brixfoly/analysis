From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum ssrint interval.
From mathcomp Require Import interval_inference archimedean finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality reals fsbigop ereal topology tvs.
From mathcomp Require Import normedtype sequences real_interval esum measure.
From mathcomp Require Import lebesgue_measure numfun realfun measurable_realfun.
From mathcomp Require Import normed_module measurable_structure.

Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope measure_display_scope.

Reserved Notation "{ 'nnfun' aT >-> T }"
  (at level 0, format "{ 'nnfun'  aT  >->  T }").
Reserved Notation "[ 'nnfun' 'of' f ]"
  (at level 0, format "[ 'nnfun'  'of'  f ]").
Reserved Notation "{ 'nnsfun' aT >-> T }"
  (at level 0, format "{ 'nnsfun'  aT  >->  T }").
Reserved Notation "[ 'nnsfun' 'of' f ]"
  (at level 0, format "[ 'nnsfun'  'of'  f ]").
Reserved Notation "{ 'sfun' aT >-> T }"
  (at level 0, format "{ 'sfun'  aT  >->  T }").
Reserved Notation "[ 'sfun' 'of' f ]"
  (at level 0, format "[ 'sfun'  'of'  f ]").
  
Module HBSimple.
Import HBTopMeas.

HB.structure Definition SimpleFun d (aT : sigmaRingType d) 
(T : topologicalType) :=
  {f of @isMeasurableFun d _ aT T f & @FiniteImage aT T f}.

End HBSimple.

Notation "{ 'sfun' aT >-> T }" := (@HBSimple.SimpleFun.type _ aT T) : form_scope.
Notation "[ 'sfun' 'of' f ]" := [the {sfun _ >-> _} of f] : form_scope.

Module HBNNSimple.
Import HBSimple.

HB.structure Definition NonNegSimpleFun
    d (aT : sigmaRingType d) (rT : realType) :=
  {f of @SimpleFun d _ _ f & @NonNegFun aT rT f}.

End HBNNSimple.

Notation "{ 'nnsfun' aT >-> T }" := (@HBNNSimple.NonNegSimpleFun.type _ aT%type T) : form_scope.
Notation "[ 'nnsfun' 'of' f ]" := [the {nnsfun _ >-> _} of f] : form_scope.

Section sfun_pred.
Context {d} {aT : sigmaRingType d} {T: topologicalType}.
Import HBTopMeas.
Definition sfun : {pred _ -> _} := [predI @mfun _ _ aT T & fimfun].
Definition sfun_key : pred_key sfun. Proof. exact. Qed.
Canonical sfun_keyed := KeyedPred sfun_key.
Lemma sub_sfun_mfun : {subset sfun <= mfun}. Proof. by move=> x /andP[]. Qed.
Lemma sub_sfun_fimfun : {subset sfun <= fimfun}. Proof. by move=> x /andP[]. Qed.
End sfun_pred.

Section sfun.
Context {d} {aT : measurableType d} {T : topologicalType}.
Import HBTopMeas.
Notation Sf := {sfun aT >-> T}.
Notation sfun := (@sfun _ aT T).
Section Sub.
Context (f : aT -> T) (fP : f \in sfun).
Definition sfun_Sub1_subproof :=
  @isMeasurableFun.Build d _ aT T f (set_mem (sub_sfun_mfun fP)).
#[local] HB.instance Definition _ := sfun_Sub1_subproof.
Definition sfun_Sub2_subproof :=
  @FiniteImage.Build aT T f (set_mem (sub_sfun_fimfun fP)).

Import HBSimple.

#[local] HB.instance Definition _ := sfun_Sub2_subproof.
Definition sfun_Sub := [sfun of f].
End Sub.

Lemma sfun_rect (K : Sf -> Type) :
  (forall f (Pf : f \in sfun), K (sfun_Sub Pf)) -> forall u : Sf, K u.
Proof.
move=> Ksub [f [[Pf1] [Pf2]]]; have Pf : f \in sfun by apply/andP; rewrite ?inE.
have -> : Pf1 = set_mem (sub_sfun_mfun Pf) by [].
have -> : Pf2 = set_mem (sub_sfun_fimfun Pf) by [].
exact: Ksub.
Qed.

Import HBSimple.

Lemma sfun_valP f (Pf : f \in sfun) : sfun_Sub Pf = f :> (_ -> _).
Proof. by []. Qed.

HB.instance Definition _ := isSub.Build _ _ Sf sfun_rect sfun_valP.

Lemma sfuneqP (f g : {sfun aT >-> T}) : f = g <-> f =1 g.
Proof. by split=> [->//|fg]; apply/val_inj/funext. Qed.

HB.instance Definition _ := [Choice of {sfun aT >-> T} by <:].

(* NB: already in cardinality.v *)
HB.instance Definition _ x : @FImFun aT T (cst x) := FImFun.on (cst x).

Definition cst_sfun x : {sfun aT >-> T} := cst x.

Lemma cst_sfunE x : @cst_sfun x =1 cst x. Proof. by []. Qed.

End sfun.

(* a better way to refactor function stuffs *)
Lemma fctD (T : Type) (K : pzRingType) (L : lmodType K) (f g : T -> L) : f + g = f \+ g.
Proof. by []. Qed.
Lemma fctN (T : Type) (K : pzRingType) (L : lmodType K) (f : T -> L) : - f = \- f.
Proof. by []. Qed.
Lemma fctM (T : Type) (K : pzRingType) (f g : T -> K) : f * g = f \* g.
Proof. by []. Qed.
Lemma fctZ (T : Type) (K : pzRingType) (L : lmodType K) k (f : T -> L) :
   k *: f = k \*: f.
Proof. by []. Qed.
Arguments cst _ _ _ _ /.
Definition fctWE := (fctD, fctN, fctM, fctZ).

Section composition.
Context d (aT : measurableType d) (rT : realType) (T1 T2 T3 : normedModType rT).
Import HBTopMeas.
Import HBSimple.

Lemma measurable1 {T : topologicalType} (x:T) : measurable [set x]. Admitted.

(* No choice but to do it all at the same time: 
B(X x Y) != B(X) \otimes B(Y) in the general case.
TODO*)

Lemma sfun_op (f: {sfun aT >-> T1}) (g: {sfun aT >-> T2}) (h: T1*T2 -> T3) : (fun x:aT => h (f x, g x)) \in sfun.
Proof.
  rewrite inE. apply/andP; split. all: rewrite in_setE /=.
    move=> maT W mW. rewrite /preimage/= [X in measurable X] (_:_ = \bigcup_( a in range f) \bigcup_(b in range g) 
    [set t | f t = a /\ g t = b /\ W (h (a, b))]) /bigcup.
      apply: eq_set=>t. rewrite exists2E propeqE; split=>[[_ hfgt]|exa]. exists (f t). split=> [//|/=]. 
      exists (g t). by exists t. by[]. case: exa=> a [rfa] /=. rewrite exists2E. case=> b. 
      rewrite exists2E. move=> [_ [fta [gtb habW]]]. by rewrite fta gtb.
    apply: fin_bigcup_measurable=> [//| a rfa]. apply: fin_bigcup_measurable=>[//|b rgb].
    rewrite [X in measurable X] (_:_ = (f@^-1`[set a])`&`(g@^-1`[set b]) `&`[set t | W (h(a,b)) ]).
    apply: eq_set=> x//=. by rewrite andA. apply: measurableI. apply: measurableI. 
      rewrite -(setTI (_ @^-1` [set _])); have := measurable1 a; have : measurable_fun [set:aT] f by[]; 
      by rewrite /measurable_fun=> /(_ maT [set a]).
      rewrite -(setTI (_ @^-1` [set _])); have := measurable1 b; have : measurable_fun [set:aT] g by[]; 
      by rewrite /measurable_fun=> /(_ maT [set b]).
    rewrite -(in_setE W). have[_|_] := boolP (h (a,b) \in W). by rewrite trueE. 
    rewrite falseE. rewrite [[set _ | False]] (_:_ = set0)=>//.
  
  rewrite -image_comp. apply: finite_image. 
  apply: (@sub_finite_set _ _ [set (a,b)|a in range f & b in range g]). move=> [x y] /=. 
  rewrite exists2E. case=> t [_ [ftx gty]]. exists x. by exists t. exists y. by exists t. by[].
  rewrite [X in finite_set X] (_:_ = \bigcup_(b in range g) [set (a,b) | a in range f]).
  apply: eq_set=> [[x y]]/=. rewrite ?exists2E. apply: propext; 
  split=> [[a [[x0 _] fx0a]] [b [x1 _] gx1b] axby | [b [[x0 _] gx0b]] [a [x1 _] fx1a axby]].
  exists b; split. by exists x1. exists a. by exists x0. by[].
  exists a; split. by exists x1. exists b. by exists x0. by[].
  apply: bigcup_finite=>[//| b _]. by apply: finite_image.
Qed.

End composition.

Section module.
Context d (aT : measurableType d) (rT : realType) (nT : normedModType rT).
Import HBTopMeas.
Import HBSimple.

Lemma sfun_submod_closed : submod_closed (@sfun d aT nT).
Proof.
split=> [|k f g sf sg]. exact: (valP (cst_sfun (0:nT))).
  apply: (sfun_op (sfun_Sub sf) (sfun_Sub sg) (fun t=>k*:t.1 + t.2)).
Qed.

HB.instance Definition _ := GRing.isSubmodClosed.Build _ _ sfun
  sfun_submod_closed.

HB.instance Definition _ := [SubChoice_isSubLmodule  of {sfun aT >-> nT} by <:].

Implicit Types (f g : {sfun aT >-> nT}).

Lemma sfun0 : (0 : {sfun aT >-> nT}) =1 cst 0. Proof. by []. Qed.
Lemma sfunN f : - f =1 \- f. Proof. by []. Qed.
Lemma sfunD f g : f + g =1 f \+ g. Proof. by []. Qed.
Lemma sfunB f g : f - g =1 f \- g. Proof. by []. Qed.
Lemma sfunM k g : k*: g =1 k \*: g. Proof. by []. Qed.
Lemma sfun_sum I r (P : {pred I}) (f : I -> {sfun aT >-> nT}) (x : aT) :
  (\sum_(i <- r | P i) f i) x = \sum_(i <- r | P i) f i x.
Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed.
Lemma sfun_prod I r (P : {pred I}) (f : I -> {sfun aT >-> nT}) (x : aT) :
  (\sum_(i <- r | P i) f i) x = \sum_(i <- r | P i) f i x.
Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed.

HB.instance Definition _ f g := MeasurableFun.copy (f \+ g) (f + g).
HB.instance Definition _ f g := MeasurableFun.copy (\- f) (- f).
HB.instance Definition _ f g := MeasurableFun.copy (f \- g) (f - g).
HB.instance Definition _ (f: {sfun aT >-> rT}) g := MeasurableFun.copy (f \*: g) (f *: g).



(* Change from \1_A to forall u:nT, \1_A *: u *)
HB.instance Definition _ (D : set aT) (mD : measurable D) :
   @FImFun aT rT (mindic _ mD) := FImFun.on (mindic _ mD).
Definition indic_sfun (D : set aT) (mD : measurable D) : {sfun aT >-> rT} :=
  mindic rT mD.

HB.instance Definition _ k f := MeasurableFun.copy (k \o* f) (f * cst_sfun k).
Definition scale_sfun k f : {sfun aT >-> rT} := k \o* f.

End module.