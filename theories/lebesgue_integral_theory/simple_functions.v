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

(* Introducing the Borel sigma-algebra for topological spaces*)
(* Section Topological_measurable.
Variable T : topologicalType.

Let G := @open T.

Definition measurableTop : set (set T) :=
  G.-sigma.-measurable.

Definition measurableTypeTop := g_sigma_algebraType G.

Lemma measurable0T : measurableTop set0. Proof. exact: sigma_algebra0. Qed.
Lemma measurableCT : forall A, measurableTop A -> measurableTop (~` A). 
Proof. exact: sigma_algebraC. Qed.
Lemma measurable_bigcupT : forall F : (set T)^nat, (forall i, measurableTop (F i)) -> 
measurableTop (\bigcup_i (F i)). Proof. exact: sigma_algebra_bigcup. Qed.    

End Topological_measurable.

HB.instance Definition topological_isMeasurable (T : topologicalType) :
  isMeasurable default_measure_display T :=
  @isMeasurable.Build _ T (@measurableTop T)
    (@measurable0T T) (@measurableCT T) (@measurable_bigcupT T). *)

Module HBSimple.

HB.structure Definition SimpleFun d d' (aT : sigmaRingType d)
(bT : sigmaRingType d') :=
  {f of @isMeasurableFun _ _ aT bT f & @FiniteImage aT _ f}.

End HBSimple.

Notation "{ 'sfun' aT >-> T }" := (@HBSimple.SimpleFun.type _ _ aT T) : form_scope.
Notation "[ 'sfun' 'of' f ]" := [the {sfun _ >-> _} of f] : form_scope.

Module HBNNSimple.
Import HBSimple.

HB.structure Definition NonNegSimpleFun
    d (aT : sigmaRingType d) (rT : realType) :=
  {f of @SimpleFun d _ aT rT f & @NonNegFun aT rT f}.

End HBNNSimple.

Notation "{ 'nnsfun' aT >-> T }" := (@HBNNSimple.NonNegSimpleFun.type _ aT%type T) : form_scope.
Notation "[ 'nnsfun' 'of' f ]" := [the {nnsfun _ >-> _} of f] : form_scope.

Section sfun_pred.
Context {d d'} {aT : sigmaRingType d} {bT : sigmaRingType d'}.
Definition sfun : {pred _ -> _} := [predI (@mfun d d' aT bT) & @fimfun aT bT].
Definition sfun_key : pred_key sfun. Proof. exact. Qed.
Canonical sfun_keyed := KeyedPred sfun_key.
Lemma sub_sfun_mfun : {subset sfun <= mfun}. Proof. by move=> x /andP[]. Qed.
Lemma sub_sfun_fimfun : {subset sfun <= fimfun}. Proof. by move=> x /andP[]. Qed.

End sfun_pred.

Section sfun.
  (* maybe change aT to sigmaringType *)
Context {d d'} {aT : measurableType d} {bT : sigmaRingType d'}.
Notation Sf := {sfun aT >-> bT}.
Notation sfun := (@sfun _ _ aT bT).
Section Sub.
Context (f : aT -> bT) (fP : f \in sfun).
Definition sfun_Sub1_subproof :=
  @isMeasurableFun.Build d d' aT bT f (set_mem (sub_sfun_mfun fP)).
#[local] HB.instance Definition _ := sfun_Sub1_subproof.
Definition sfun_Sub2_subproof :=
  @FiniteImage.Build aT bT f (set_mem (sub_sfun_fimfun fP)).

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

Lemma sfuneqP (f g : {sfun aT >-> bT}) : f = g <-> f =1 g.
Proof. by split=> [->//|fg]; apply/val_inj/funext. Qed.

HB.instance Definition _ := [Choice of {sfun aT >-> bT} by <:].

(* NB: already in cardinality.v *)
HB.instance Definition _ x : @FImFun aT bT (cst x) := FImFun.on (cst x).

Definition cst_sfun x : {sfun aT >-> bT} := cst x.

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

Section ring.
Context d (aT : measurableType d) (rT : realType).

Lemma sfun_subring_closed : subring_closed (@sfun d _ aT rT).
Proof.
by split=> [|f g|f g]; rewrite ?inE/= ?rpred1//;
   move=> /andP[/= mf ff] /andP[/= mg fg]; rewrite !(rpredB, rpredM).
Qed.

HB.instance Definition _ := GRing.isSubringClosed.Build _ (@sfun d _ aT rT)
  sfun_subring_closed.
HB.instance Definition _ := [SubChoice_isSubComPzRing of {sfun aT >-> rT} by <:].

Implicit Types (f g : {sfun aT >-> rT}).

Import HBSimple.

Lemma sfun0 : (0 : {sfun aT >-> rT}) =1 cst 0. Proof. by []. Qed.
Lemma sfun1 : (1 : {sfun aT >-> rT}) =1 cst 1. Proof. by []. Qed.
Lemma sfunN f : - f =1 \- f. Proof. by []. Qed.
Lemma sfunD f g : f + g =1 f \+ g. Proof. by []. Qed.
Lemma sfunB f g : f - g =1 f \- g. Proof. by []. Qed.
Lemma sfunM f g : f * g =1 f \* g. Proof. by []. Qed.
Lemma sfun_sum I r (P : {pred I}) (f : I -> {sfun aT >-> rT}) (x : aT) :
  (\sum_(i <- r | P i) f i) x = \sum_(i <- r | P i) f i x.
Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed.
Lemma sfun_prod I r (P : {pred I}) (f : I -> {sfun aT >-> rT}) (x : aT) :
  (\sum_(i <- r | P i) f i) x = \sum_(i <- r | P i) f i x.
Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed.
Lemma sfunX f n : f ^+ n =1 (fun x => f x ^+ n).
Proof. by move=> x; elim: n => [|n IHn]//; rewrite !exprS sfunM/= IHn. Qed.

HB.instance Definition _ f g := MeasurableFun.copy (f \+ g) (f + g).
HB.instance Definition _ f g := MeasurableFun.copy (\- f) (- f).
HB.instance Definition _ f g := MeasurableFun.copy (f \- g) (f - g).
HB.instance Definition _ f g := MeasurableFun.copy (f \* g) (f * g).

Import HBSimple.

(* TODO: mv to `measurable_realfun.v`? *)
HB.instance Definition _ (D : set aT) (mD : measurable D) :
   @FImFun aT rT (mindic _ mD) := FImFun.on (mindic _ mD).
Definition indic_sfun (D : set aT) (mD : measurable D) : {sfun aT >-> rT} :=
  mindic rT mD.

HB.instance Definition _ k f := MeasurableFun.copy (k \o* f) (f * cst_sfun k).
Definition scale_sfun k f : {sfun aT >-> rT} := k \o* f.

End ring.
Arguments indic_sfun {d aT rT} _.

Lemma preimage_nnfun0 T (R : realDomainType) (f : {nnfun T >-> R}) t :
  t < 0 -> f @^-1` [set t] = set0.
Proof.
move=> t0.
by apply/preimage10 => -[x _]; apply: contraPnot t0 => <-; rewrite le_gtF.
Qed.

Lemma preimage_cstM T (R : realFieldType) (x y : R) (f : T -> R) :
  x != 0 -> (cst x \* f) @^-1` [set y] = f @^-1` [set y / x].
Proof.
move=> x0; apply/seteqP.
by split=> [z/= <-|z/= ->]; rewrite [x * _]mulrC (mulfK, divfK).
Qed.

Lemma preimage_add T (R : numDomainType) (f g : T -> R) z :
  (f \+ g) @^-1` [set z] = \bigcup_(a in f @` setT)
    ((f @^-1` [set a]) `&` (g @^-1` [set z - a])).
Proof.
apply/seteqP; split=> [x /= fgz|x [_ /= [y _ <-]] [fxfy gzf]]; last first.
  by rewrite gzf -fxfy addrC subrK.
exists (z - g x); first by exists x; rewrite // -fgz addrK.
by split; rewrite 1?subKr // -fgz addrK.
Qed.

Section simple_bounded.
Context d (T : sigmaRingType d) (R : realType).

Import HBSimple.

Lemma simple_bounded (f : {sfun T >-> R}) : bounded_fun f.
Proof.
have /finite_seqP[r fr] := fimfunP f.
exists (fine (\big[maxe/-oo%E]_(i <- r) `|i|%:E)).
split; rewrite ?num_real// => x mx z _; apply/ltW/(le_lt_trans _ mx).
have ? : f z \in r by have := imageT f z; rewrite fr.
rewrite -[leLHS]/(fine `|f z|%:E) fine_le//.
  (* TODO: generalize the statement of bigmaxe_fin_num *)
  have := @bigmaxe_fin_num _ (map normr r) `|f z|.
  by rewrite big_map => ->//; apply/mapP; exists (f z).
by rewrite (unstable.bigmax_sup_seq _ _ (lexx _)).
Qed.

End simple_bounded.

Section nnsfun_functions.
Context d (T : measurableType d) (R : realType).

Import HBNNSimple.

Lemma cst_nnfun_subproof (x : {nonneg R}) : forall t : T, 0 <= cst x%:num t.
Proof. by move=> /=. Qed.
HB.instance Definition _ x := @isNonNegFun.Build T R (cst x%:num)
  (cst_nnfun_subproof x).

Definition cst_nnsfun (r : {nonneg R}) : {nnsfun T >-> R} := cst r%:num.

Definition nnsfun0 : {nnsfun T >-> R} := cst_nnsfun 0%:nng.

Lemma indic_nnfun_subproof (D : set T) : forall x, 0 <= (\1_D) x :> R.
Proof. by []. Qed.

HB.instance Definition _ D := @isNonNegFun.Build T R \1_D
  (indic_nnfun_subproof D).

HB.instance Definition _ D (mD : measurable D) :
   @NonNegFun T R (mindic R mD) := NonNegFun.on (mindic R mD).

End nnsfun_functions.
Arguments nnsfun0 {d T R}.

Section nnfun_bin.
Variables (T : Type) (R : numDomainType) (f g : {nnfun T >-> R}).

Lemma add_nnfun_subproof : @isNonNegFun T R (f \+ g).
Proof. by split => x; rewrite addr_ge0//; apply/fun_ge0. Qed.
HB.instance Definition _ := add_nnfun_subproof.

Lemma mul_nnfun_subproof : @isNonNegFun T R (f \* g).
Proof. by split => x; rewrite mulr_ge0//; apply/fun_ge0. Qed.
HB.instance Definition _ := mul_nnfun_subproof.

Lemma max_nnfun_subproof : @isNonNegFun T R (f \max g).
Proof. by split => x /=; rewrite /maxr; case: ifPn => _; apply: fun_ge0. Qed.
HB.instance Definition _ := max_nnfun_subproof.

End nnfun_bin.

Section nnsfun_bin.
Context d (T : measurableType d) (R : realType).
Variables f g : {nnsfun T >-> R}.

Import HBNNSimple.

HB.instance Definition _ := MeasurableFun.on (f \+ g).
Definition add_nnsfun : {nnsfun T >-> R} := f \+ g.

HB.instance Definition _ := MeasurableFun.on (f \* g).
Definition mul_nnsfun : {nnsfun T >-> R} := f \* g.

HB.instance Definition _ := MeasurableFun.on (f \max g).
Definition max_nnsfun : {nnsfun T >-> R} := f \max g.

Definition indic_nnsfun A (mA : measurable A) : {nnsfun T >-> R} := mindic R mA.

End nnsfun_bin.
Arguments add_nnsfun {d T R} _ _.
Arguments mul_nnsfun {d T R} _ _.
Arguments max_nnsfun {d T R} _ _.

Definition scale_nnsfun d (T : measurableType d) (R : realType)
    (f : {nnsfun T >-> R}) (k : R) (k0 : 0 <= k) :=
  mul_nnsfun (cst_nnsfun T (NngNum k0)) f.

Definition proj_nnsfun d (T : measurableType d) (R : realType)
    (f : {nnsfun T >-> R}) (A : set T) (mA : measurable A) :=
  mul_nnsfun f (indic_nnsfun R mA).

Section mrestrict.
Import HBNNSimple.

Lemma mrestrict d (T : measurableType d) (R : realType) (f : {nnsfun T >-> R})
  A (mA : measurable A) : f \_ A = proj_nnsfun f mA.
Proof.
apply/funext => x /=; rewrite /patch mindicE.
by case: ifP; rewrite (mulr0, mulr1).
Qed.

End mrestrict.

Section nnsfun_iter.
Context d (T : measurableType d) (R : realType) (D : set T).
Variable f : {nnsfun T >-> R}^nat.

Definition sum_nnsfun n := \big[add_nnsfun/nnsfun0]_(i < n) f i.

Import HBNNSimple.

Lemma sum_nnsfunE n t : sum_nnsfun n t = \sum_(i < n) (f i t).
Proof. by rewrite /sum_nnsfun; elim/big_ind2 : _ => [|x g y h <- <-|]. Qed.

Definition bigmax_nnsfun n := \big[max_nnsfun/nnsfun0]_(i < n) f i.

Lemma bigmax_nnsfunE n t : bigmax_nnsfun n t = \big[maxr/0]_(i < n) (f i t).
Proof. by rewrite /bigmax_nnsfun; elim/big_ind2 : _ => [|x g y h <- <-|]. Qed.

End nnsfun_iter.

Section nnsfun_cover.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable f : {nnsfun T >-> R}.

Import HBNNSimple.

Lemma nnsfun_cover : \big[setU/set0]_(i \in range f) (f @^-1` [set i]) = setT.
Proof. by rewrite fsbig_setU//= -subTset => x _; exists (f x). Qed.

Lemma nnsfun_coverT : \big[setU/set0]_(i \in [set: R]) f @^-1` [set i] = setT.
Proof.
by rewrite -(fsbig_widen (range f)) ?nnsfun_cover//= => x [_ /preimage10].
Qed.

End nnsfun_cover.

Section measure_fsbig.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable m : {measure set T -> \bar R}.

Lemma measure_fsbig (I : choiceType) (A : set I) (F : I -> set T) :
  finite_set A ->
  (forall i, A i -> measurable (F i)) -> trivIset A F ->
  m (\big[setU/set0]_(i \in A) F i) = \sum_(i \in A) m (F i).
Proof.
move=> Afin Fm Ft.
by rewrite fsbig_finite// -measure_fin_bigcup// -bigsetU_fset_set.
Qed.

Import HBNNSimple.

Lemma additive_nnsfunr (g f : {nnsfun T >-> R}) x :
  \sum_(i \in range g) m (f @^-1` [set x] `&` (g @^-1` [set i])) =
  m (f @^-1` [set x] `&` \big[setU/set0]_(i \in range g) (g @^-1` [set i])).
Proof.
rewrite -?measure_fsbig//.
- by move=> i Ai; apply: measurableI.
- exact/trivIset_setIl/trivIset_preimage1.
- by rewrite !fsbig_finite//= big_distrr.
Qed.

Lemma additive_nnsfunl (g f : {nnsfun T >-> R}) x :
  \sum_(i \in range g) m (g @^-1` [set i] `&` (f @^-1` [set x])) =
  m (\big[setU/set0]_(i \in range g) (g @^-1` [set i]) `&` f @^-1` [set x]).
Proof. by under eq_fsbigr do rewrite setIC; rewrite setIC additive_nnsfunr. Qed.

End measure_fsbig.

Section mulem_ge0.
Local Open Scope ereal_scope.

Let mulef_ge0 (R : realDomainType) x (f : R -> \bar R) :
  0 <= f x -> ((x < 0)%R -> f x = 0) -> 0 <= x%:E * f x.
Proof.
case: (ltP x 0%R) => [x_lt0 ? ->|x_ge0 fx_ge0 _] //; last exact: mule_ge0.
by rewrite mule0.
Qed.

Lemma nnfun_muleindic_ge0 d (T : sigmaRingType d) (R : realDomainType)
  (f : {nnfun T >-> R}) r z : 0 <= r%:E * (\1_(f @^-1` [set r]) z)%:E.
Proof.
apply: (@mulef_ge0 _ _ (fun r => (\1_(f @^-1` [set r]) z)%:E)).
  by rewrite lee_fin// indicE.
by move=> r0; rewrite preimage_nnfun0// indic0.
Qed.

Lemma mulemu_ge0 d (T : sigmaRingType d) (R : realType)
    (mu : {measure set T -> \bar R}) x (A : R -> set T) :
  ((x < 0)%R -> A x = set0) -> 0 <= x%:E * mu (A x).
Proof.
by move=> xA; rewrite (@mulef_ge0 _ _ (mu \o _))//= => /xA ->; rewrite measure0.
Qed.
Global Arguments mulemu_ge0 {d T R mu x} A.

Import HBNNSimple.

Lemma nnsfun_mulemu_ge0 d (T : sigmaRingType d) (R : realType)
    (mu : {measure set T -> \bar R}) (f : {nnsfun T >-> R}) x :
  0 <= x%:E * mu (f @^-1` [set x]).
Proof.
by apply: (mulemu_ge0 (fun x => f @^-1` [set x])); exact: preimage_nnfun0.
Qed.

End mulem_ge0.





(*************)

(* General lemmas, to add after *)
(*
Definition measurableTypeNormedModType (R : numDomainType)
    (V : normedModType R) :=
  @g_sigma_algebraType V open.

(* corresponds to measurableR *)
Definition measurableNormedModType (R : numDomainType)
    (V : normedModType R) : set (set V) :=
  open.-sigma.-measurable.

HB.instance Definition NormedModType_isMeasurable (R : numDomainType)
    (V : normedModType R) :
  isMeasurable default_measure_display V :=
  @isMeasurable.Build _ (measurableTypeNormedModType V)
    (@measurableNormedModType _ V)
    measurable0 (@measurableC _ _) (@bigcupT_measurable _ _).


Lemma singleton_bigcap {R : realType} {N : normedModType R} (x:N) : [set x] = \bigcap_(k:nat) (ball x (1/((k.+1)%:R))).
Proof.
  rewrite eqEsubset; split=> [_ ->| y] /=. rewrite /bigcap /= => k _;
  apply: ballxx; by rewrite ltr_pdivlMr.
  rewrite /bigcap/=; apply: contraPP=> ynx; rewrite -existsNE.
  exists (truncn (1/ `|x- y|)). rewrite not_implyE; split => [//|].
  rewrite pseudo_metric_ball_norm/= ltr_pdivlMr => //. have := truncnS_gt (1/`|x-y|);
  rewrite ltr_pdivrMr. rewrite normr_gt0; apply/eqP=>/subr0_eq; exact: nesym.
  by rewrite mulrC => asb bsa; have:= lt_trans asb bsa; rewrite lt_irreflexive.
Qed.

Lemma measurable1 {R : realType} {N : normedModType R} 
(x : N) : measurable [set x].
Proof.
  rewrite singleton_bigcap; apply: bigcap_measurable=> [//|k _].
  rewrite/measurable/=/smallest/bigcap/=. [sda osa]. apply: osa; exact: (ball_open x).
Qed.

Section composition.
Context d (aT : measurableType d) (rT : realType) (T1 T2 T3 : normedModType rT).
Import HBSimple.

(* No choice but to do it all at the same time: 
B(X x Y) != B(X) \otimes B(Y) in the general case.*)
Lemma sfun_op (f: {sfun aT >-> (g_sigma_algebraType (@open T1))}) (g: {sfun aT >-> T2}) (h: T1*T2 -> T3) : (fun x:aT => h (f x, g x)) \in sfun.
Proof.
  rewrite inE; apply/andP; split. all: rewrite in_setE /=.
    move=> maT W mW. rewrite /preimage/= [X in measurable X] 
    (_:_ = \bigcup_( a in range f) \bigcup_(b in range g) 
   ((f@^-1`[set a])`&`(g@^-1`[set b])`&`[set t | W (h(a,b))])) /bigcup.
    apply: eq_set=>t/=; rewrite propeqE.
    split=>[[_ whfgt]|[a [x _ <-]] [b [x0 _ <-]] [[-> ->] Whfgt]//].
    exists (f t). by exists t. exists (g t). by exists t. by[].
    apply: fin_bigcup_measurable => [//| a rfa]. apply: fin_bigcup_measurable=>[//|b rgb].
    apply: measurableI. apply: measurableI.
    rewrite -(setTI (_ @^-1` [set _])); exact: measurable_funPT f maT [set a] (measurable1 a).
    rewrite -(setTI (_ @^-1` [set _])); exact: measurable_funPT g maT [set b] (measurable1 b).
    rewrite -(in_setE W); have[_|_] := boolP (h (a,b) \in W). 
    by rewrite trueE. rewrite falseE [[set _ | False]] (_:_ = set0)=>//.
  rewrite -image_comp; apply: finite_image.
  apply: (@sub_finite_set _ _ ((range f) `*`(range g))) => [[a b] [x _ [<- <-]]/=|].
  by split; exists x. by apply: finite_setX.
Qed.

End composition.

Section module.
Context d (aT : measurableType d) (rT : realType) (nT : normedModType rT).
Import HBSimple.

Lemma sfun_submod_closed : submod_closed (@sfun d aT nT).
Proof.
split=> [|k f g sf sg]. exact: (valP (cst_sfun (0:nT))).
  apply: (sfun_op (sfun_Sub sf) (sfun_Sub sg) (fun t=>k*:t.1 + t.2)).
Qed.

HB.instance Definition _ := GRing.isSubmodClosed.Build _ _ sfun
  sfun_submod_closed.
HB.instance Definition _ := [SubChoice_isSubLmodule of {sfun aT >-> nT} by <:].

Implicit Types (f g : {sfun aT >-> nT}).

Lemma sfun0 : (0 : {sfun aT >-> nT}) =1 cst 0. Proof. by []. Qed.
Lemma sfunN f : - f =1 \- f. Proof. by []. Qed.
Lemma sfunD f g : f + g =1 f \+ g. Proof. by []. Qed.
Lemma sfunB f g : f - g =1 f \- g. Proof. by []. Qed.
Lemma sfunS k g : k*: g =1 k \*: g. Proof. by []. Qed.
Lemma sfun_sum I r (P : {pred I}) (f : I -> {sfun aT >-> nT}) (x : aT) :
  (\sum_(i <- r | P i) f i) x = \sum_(i <- r | P i) f i x.
Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed.
Lemma sfun_prod I r (P : {pred I}) (f : I -> {sfun aT >-> nT}) (x : aT) :
  (\sum_(i <- r | P i) f i) x = \sum_(i <- r | P i) f i x.
Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed.
  
(* TODO : make these work*)(* 
HB.instance Definition _ f g := MeasurableFun.copy (f \+ g) (f + g).
HB.instance Definition _ f g := MeasurableFun.copy (\- f) (- f).
HB.instance Definition _ f g := MeasurableFun.copy (f \- g) (f - g).
HB.instance Definition _ (k: rT) g := MeasurableFun.copy (k \*: g) (k *: g). *)

Definition mindic_mod {D : set aT} (mD : d.-measurable D) (z: nT)
    : aT -> g_sigma_algebraType (@open nT) :=
  *:%R^~ z \o \1_D.

Lemma mindic_modE {A : set aT} (mA : d.-measurable A) (z: nT) :
mindic_mod mA z = fun x => if x \in A then z else 0.
Proof.
  by apply/funext=>x; rewrite /mindic_mod/=indicE; 
  case: ifP; [rewrite scale1r | rewrite scale0r].
Qed.

Lemma measurable_mindic_mod {D A : set aT} (mA : d.-measurable A) (z:nT) :
measurable_fun D (mindic_mod mA z).
Proof.
  move=> mD Y mY. rewrite mindic_modE /preimage [X in _`&`X] (_:_ = 
  if z \in Y then (if 0 \in Y then [set:aT] else A) else (if 0\in Y then ~`A else set0)).
  have [zY|nzY] := boolP (z \in Y); have [zeroY|nzeroY] := boolP (0\in Y); apply: eq_set=>t; 
  case: ifP=> tA//=; try apply: propT; try apply: propF; try rewrite propeqE.
  by rewrite -in_setE. by rewrite -in_setE. by split=>_//; rewrite -in_setE.
  rewrite notin_setE in nzeroY. apply/iff_not2.
  by have : ~ A t by rewrite -notin_setE tA.
  by rewrite notin_setE in nzY; apply/iff_notr; rewrite in_setE in tA.
    rewrite in_setE in zeroY. by rewrite -notin_setE tA/=.
    by rewrite -notin_setE. by rewrite -notin_setE.
  apply: measurableI=>//. case: ifP=>_//. case: ifP=>// _. 
  case: ifP=>_//. exact: measurableC.
Qed.

HB.instance Definition _ D mD z := @isMeasurableFun.Build _ _ aT
(g_sigma_algebraType open) (mindic_mod mD z) (@measurable_mindic_mod _ D mD z).

Lemma mindic_mod_fimfun_subproof {A : set aT} (mA : d.-measurable A) (z:nT) : 
@FiniteImage aT nT (mindic_mod mA z).
Proof.
split. apply: (finite_subfset [fset 0; z]%fset) => x [a _ <-/=].
rewrite mindic_modE !inE. case: ifP=>[_|_]; by rewrite ?eqxx ?orbT. 
Qed.

HB.instance Definition _ A mA z := @mindic_mod_fimfun_subproof A mA z.
HB.instance Definition _ (A : set aT) (mA : measurable A) z:
  @FImFun aT (g_sigma_algebraType open) (mindic_mod mA z) := 
  FImFun.on (mindic_mod mA z).

Definition indic_mod_sfun {A : set aT} (mA : measurable A) (z: nT) : {sfun aT >-> nT} :=
  mindic_mod mA z.

End module.

Section simple_bounded.
Context d (T : sigmaRingType d) (R : realType) (N : normedModType R).

Import HBSimple.

Lemma simple_bounded (f : {sfun T >-> N}) : bounded_fun f.
Proof.
have /finite_seqP[r fr] := fimfunP f.
exists (fine (\big[maxe/-oo%E]_(i <- r) `|i|%:E)).
split; rewrite ?num_real// => x mx z _; apply/ltW/(le_lt_trans _ mx).
have ? : f z \in r by have := imageT f z; rewrite fr.
rewrite -[leLHS]/(fine `|f z|%:E) fine_le//.
  (* TODO: generalize the statement of bigmaxe_fin_num *)
  have := @bigmaxe_fin_num _ (map normr r) `|f z|.
  by rewrite big_map => ->//; apply/mapP; exists (f z).
by rewrite (unstable.bigmax_sup_seq _ _ (lexx _)).
Qed.

End simple_bounded.
*)