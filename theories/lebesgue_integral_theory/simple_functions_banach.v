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
(*
(* Introducing the Borel sigma-algebra for topological spaces*)
Section Topological_measurable.
Variable T : topologicalType.

Let G := @open T.

Definition measurableTop : set (set T) :=
  G.-sigma.-measurable.

Lemma measurable0T : measurableTop set0. Proof. exact: sigma_algebra0. Qed.
Lemma measurableCT : forall A, measurableTop A -> measurableTop (~` A). 
Proof. exact: sigma_algebraC. Qed.
Lemma measurable_bigcupT : forall F : (set T)^nat, (forall i, measurableTop (F i)) -> 
measurableTop (\bigcup_i (F i)). Proof. exact: sigma_algebra_bigcup. Qed.    

Definition measurableTypeTop := g_sigma_algebraType G.

End Topological_measurable.

HB.instance Definition topological_isMeasurable (T : topologicalType) :
  isMeasurable default_measure_display T :=
  @isMeasurable.Build _ T (@measurableTop T)
    (@measurable0T T) (@measurableCT T) (@measurable_bigcupT T).
*)
Module HBSimple.

HB.structure Definition SimpleFun d (aT : sigmaRingType d) 
(T : topologicalType) :=
  {f of @isMeasurableFun _ _ aT (@g_sigma_algebraType T open) f & @FiniteImage aT (@g_sigma_algebraType T open) f}.

End HBSimple.

Notation "{ 'sfun' aT >-> T }" := (@HBSimple.SimpleFun.type _ aT T) : form_scope.
Notation "[ 'sfun' 'of' f ]" := [the {sfun _ >-> _} of f] : form_scope.

Module HBNNSimple.
Import HBSimple.

HB.structure Definition NonNegSimpleFun
    d (aT : sigmaRingType d) (rT : realType) :=
  {f of @SimpleFun d aT rT f & @NonNegFun aT rT f}.

End HBNNSimple.

Notation "{ 'nnsfun' aT >-> T }" := (@HBNNSimple.NonNegSimpleFun.type _ aT%type T) : form_scope.
Notation "[ 'nnsfun' 'of' f ]" := [the {nnsfun _ >-> _} of f] : form_scope.

Section sfun_pred.
Context {d} {aT : sigmaRingType d} {T: topologicalType}.
Definition sfun : {pred _ -> _} := [predI (@mfun d _ aT (@g_sigma_algebraType T open)) & @fimfun aT (@g_sigma_algebraType T open)].
Definition sfun_key : pred_key sfun. Proof. exact. Qed.
Canonical sfun_keyed := KeyedPred sfun_key.
Lemma sub_sfun_mfun : {subset sfun <= mfun}. Proof. by move=> x /andP[]. Qed.
Lemma sub_sfun_fimfun : {subset sfun <= fimfun}. Proof. by move=> x /andP[]. Qed.

End sfun_pred.

Section sfun.
Context {d} {aT : measurableType d} {T : topologicalType}.
Notation Sf := {sfun aT >-> T}.
Notation sfun := (@sfun _ aT T).
Section Sub.
Context (f : aT -> (g_sigma_algebraType open)) (fP : f \in sfun).
Definition sfun_Sub1_subproof :=
  @isMeasurableFun.Build d _ aT (g_sigma_algebraType open) f (set_mem (sub_sfun_mfun fP)).
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
HB.instance Definition _ x : @FImFun aT (@g_sigma_algebraType T open) (cst x) := FImFun.on (cst x).

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
Import HBSimple.

Lemma singleton_bigcap {R : realType} {N : normedModType R} (x:N) : [set x] = \bigcap_(k:nat) (ball x (k.+1%:R)^-1).
Proof.
  rewrite eqEsubset; split=> [_ ->| y] /=. rewrite /bigcap /= => k _;
  apply: ballxx. by rewrite invr_gt0. 
  rewrite /bigcap/==> bbxy. apply: Logic.eq_sym. have cxy : close x y.
  rewrite ball_close=> e. have [n0 _ a] := near_infty_natSinv_lt e.
  apply: (@le_ball _ _ _ n0.+1%:R^-1 e%:num); rewrite /subset/= in a;
  have ins:= a n0 (le_refl n0). apply/lt_le=> t tn0. exact: (lt_trans tn0).
  exact: (bbxy n0). exact: (close_eq (@norm_hausdorff _ N) cxy).
Qed.

Lemma measurable1 {R : realType} {N : normedModType R} (x : @g_sigma_algebraType N open) : measurable [set x].
Proof.
  rewrite singleton_bigcap; apply: bigcap_measurable=> [//|k _]; 
  rewrite/measurable/=/smallest/bigcap/= => A [sda osa]; apply: osa; exact: (ball_open x).
Qed.

(* No choice but to do it all at the same time: 
B(X x Y) != B(X) \otimes B(Y) in the general case.*)
Lemma sfun_op (f: {sfun aT >-> T1}) (g: {sfun aT >-> T2}) (h: T1*T2 -> T3) : (fun x:aT => h (f x, g x)) \in sfun.
Proof.
  rewrite inE; apply/andP; split. all: rewrite in_setE /=.
    move=> maT W mW. rewrite /preimage/= [X in measurable X] 
    (_:_ = \bigcup_( a in range f) \bigcup_(b in range g) 
   ((f@^-1`[set a])`&`(g@^-1`[set b])`&`[set t | W (h(a,b))])) /bigcup.
    apply: eq_set=>t/=; rewrite propeqE.
    split=>[[_ whfgt]|[a [x _ <-]] [b [x0 _ <-]] [[-> ->] Whfgt]//].
    exists (f t). by exists t. exists (g t). by exists t. by[].
    apply: fin_bigcup_measurable => [//| a rfa]. 
    apply: fin_bigcup_measurable=>[//|b rgb]. apply: measurableI. 
    apply: measurableI. 
    rewrite -(setTI (_ @^-1` [set _])); exact: measurable_funPT f maT _ (measurable1 a).
    rewrite -(setTI (_ @^-1` [set _])); exact: measurable_funPT g maT _ (measurable1 b).
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
  
(* TODO : make these work*)
(* HB.instance Definition _ f g := MeasurableFun.copy (f \+ g) (f + g).
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
Context d (T : sigmaRingType d) (R : realType) (N : normedModType R).


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

Section set_lemmas.

Lemma bigcapDr {T I} (F : I -> set T) [P : set I] (A : set T) : 
\bigcup_(i in P)  (A `\` F i) = A `\` \bigcap_(i in P)  F i.
Proof.
by rewrite setDE setC_bigcap setI_bigcupr; 
  apply: eq_bigcup; rewrite -?eqEsubset.
Qed.

End set_lemmas.

(* Will be moved to measurable_structure.v *)
Section sigma_algebra_lemmas.
Lemma sigma_algebra_subset {d} {M : measurableType d} {H : set (set M)}
(mH : H `<=`d.-measurable) : <<s H>> `<=` measurable.
Proof.
  by rewrite /smallest/bigcap=> K/= /(_ d.-measurable) oK; apply: oK;
  split=>[|//]; apply:sigma_algebra_measurable.
Qed.

Lemma sigma_algebra_gen {M : choiceType} {G : set (set M)} : G `<=`<<s G>>.
Proof.
  by rewrite /smallest=>A hA H [saH GH]; apply: GH.
Qed.

Lemma bigcup_cvg_mu {d} {M : measurableType d} {R : realType} 
{mu : {measure set M -> \bar R}} (A : (set M)^nat) : (forall i:nat, measurable (A i)) ->
mu (\bigcup_(i<n) A i) @[n-->\oo] --> mu (\bigcup_n A n).
Proof.
  have nduA : nondecreasing_seq (fun n=>\bigcup_(i<n) A i).
  move=> n m nm/=. apply/subsetPset=> a [i/= i_n ai].
  exists i=>//=. rewrite -ltz_nat. rewrite -?ltz_nat -?lez_nat in i_n, nm.
  apply: (lt_le_trans i_n nm). move=> ma. 
  have mua: forall n, measurable (\bigcup_(i<n) A i). move=>n. exact: bigcup_measurable.
  rewrite [\bigcup_n A n] (_:_ = \bigcup_n (\bigcup_(i<n) A i)). 
  rewrite eqEsubset; split=> [a [n _ Ana]|a [n _ [k kn aka]]]. 
  exists n.+1=>//; exists n=>//=. by exists k.
  apply: (nondecreasing_cvg_mu mua _ nduA). exact: bigcup_measurable.
Qed.

Lemma bigcap_cvg_mu {d} {M : measurableType d} {R : realType} 
{mu : {finite_measure set M -> \bar R}} (A : (set M)^nat) : (forall i:nat, measurable (A i)) ->
mu (\bigcap_(i<n) A i) @[n-->\oo] --> mu (\bigcap_n A n).
Proof.
  have ndiA : nonincreasing_seq (fun n=>\bigcap_(i<n) A i).
    rewrite /bigcap => n m nm/=. apply/subsetPset=> a/= Ia i i_n.
    apply: Ia; rewrite -ltz_nat; rewrite -?ltz_nat -?lez_nat in nm, i_n.
    apply: lt_le_trans i_n nm.
  move=> ma. have mia: forall n, measurable (\bigcap_(i<n) A i). move=>n. 
    exact: bigcap_measurableType.
  rewrite [\bigcap_n A n] (_:_ = \bigcap_n (\bigcap_(i<n) A i)). 
  rewrite eqEsubset/bigcap; split=> [a/=aia j _ i ij|a/= aIa i _]. exact: aia.
  exact: (aIa i.+1).
  apply: (nonincreasing_cvg_mu _ mia _ ndiA). rewrite/bigcap/=. 
  under eq_set do under eq_forall do rewrite ltn0 [false -> _] 
  (_:_ = True) ?propeqE//. rewrite [X in mu X] (_:_ = [set:M]) -?subTset=>//=.
  apply: fin_num_fun_lty. exact: fin_num_measure.
  exact: bigcap_measurable.
Qed.

Lemma open_closed_measurable (t : topologicalType) : 
(@open t).-sigma.-measurable = (@closed t).-sigma.-measurable.
Proof.
  rewrite eqEsubset; split; rewrite{1}/measurable/=. 
  apply: (@sigma_algebra_subset _ (g_sigma_algebraType (@closed t)) (@open t))=> U oU.
  rewrite -(setCK U); apply: sigma_algebraC. 
  apply: sigma_algebra_gen=>//; exact: open_closedC.
  apply: sigma_algebra_subset=> F cF; rewrite -(setCK F); apply:sigma_algebraC.
  apply: sigma_algebra_gen=>//; exact: closed_openC.
Qed.

Lemma countable_bigcup_measurable {d} {T : sigmaRingType d} {U} {F : U -> set T}
{P : set U} : countable P -> (forall i:U, P i -> measurable (F i)) -> 
measurable (\bigcup_(i in P) F i).
Proof.
  move=>/[dup] cP /pfcard_geP=>[[-> _|/surjfunPex [f ->] mF]]. by rewrite bigcup0.
  rewrite bigcup_image.
  apply: bigcupT_measurable=>// i. exact: mF.
Qed.

End sigma_algebra_lemmas.

(* Some should be moved in topology_structure.v, some in metric_structure.v*)
Section topology_lemmas.

Lemma basisP {T : ptopologicalType} {B : set (set T)} : basis B <-> B `<=`open /\
(forall U: set T, open U -> U = \bigcup_(V in [set W | B W /\ W `<=`U]) V).
Proof.
  split=> [[oB bB]|[Bo dec]]. split=> //U oU.
    rewrite eqEsubset /bigcup; split=>[x Ux/=|x [A/= [BA AU] /AU //]].
    have:= bB x. rewrite/cvg_to {2}/nbhs/filter_from/= => /(_ U)/=.
    have nT: \near x, U x by apply: (open_in_nearW oU)=>[y|]; rewrite in_setE. 
    rewrite nbhs_nearE !exists2E/= => /(_ nT). 
    by under eq_exists=>x0 do rewrite -andA {1}(andC (x0 x) _) andA.
  split=>// x. rewrite/cvg_to/=nbhsE/open_nbhs => P /= [U [/(dec U)->]].
  rewrite/bigcup {2}/subset => /=[[A [BA AU] Ax] UP]. exists A=>//= t At.
  apply: UP. by exists A.
Qed.

Lemma basis_nonzero {T : ptopologicalType} {B : set (set T)} : basis B -> B!=set0.
Proof.
  move=> /basisP [Bo /(_ [set:T] openT) Tb]. apply/set0P/eqP => B0.
  move: B0 Tb ->. rewrite [X in _=X] (_:_ = set0).
  apply: eq_set=> x. apply: propF=> [[A/= [F//]]]. apply/eqP. exact: setT0.
Qed.

Lemma countable_basis_to_seq {T : ptopologicalType} {B : set (set T)} : 
countable B -> basis B -> exists f : nat -> (set T), range f = B /\ 
forall U : set T, open U -> U = \bigcup_(n in [set m| f m `<=`U]) (f n).
Proof.
  move=> /pfcard_geP. 
  case=>/= [B0 /basis_nonzero/set0P/eqP/(_ B0)//| /surjfunPex [f ->] /basisP [Bo dec]].
  exists f. split=>//. move=> U /(dec U) ->. rewrite/bigcup/=. apply:eq_set=>x/=.
  rewrite !exists2E propeqE; split=>//=[[A [[[n _ <- fnU] fnx]]]| [n [fni fnx]]]. 
    exists n. split=>//= y fny/=. exists (f n)=>//. split=>//. by exists n.
  exists (f n); split=>//. split=>[|y /fni/= [V [_ VU /VU//]]]. by exists n.
Qed.

Lemma second_countable_seq {T : ptopologicalType} : @second_countable T -> 
exists f : nat -> (set T), range f `<=` open /\ 
forall U : set T, open U -> U = \bigcup_(n in [set m| f m `<=`U]) (f n).
Proof.
  rewrite /second_countable=>[[B cB bB]]. 
  have[f [rfb dec]]:= countable_basis_to_seq cB bB. exists f; split=>//. 
  rewrite rfb. by have[Bo _] := bB.
Qed.

Definition separable {T : ptopologicalType} := 
exists D: set T, countable D /\ dense D.

Lemma second_countable_separable {T : ptopologicalType} : 
@second_countable T -> @separable T.
Proof.
  move=> [B] /(sub_countable (card_le_setD B [set set0])). 
  rewrite/countable=> /pfcard_geP. case=> [|[f] /basisP [oB bB]].
  rewrite setD_eq0=> /subset_set1. case=> -> /basisP [oB bB];
  have:= (bB [set:T]) openT. rewrite [X in \bigcup_(_ in X) _] (_:_ = set0).
      by apply: eq_set=>x/=; rewrite andB. rewrite bigcup0=>//.
      have:= (@setT0 T). by move=> /eqP.
    rewrite [X in \bigcup_(_ in X) _] (_:_ = [set set0]).
    apply: eq_set=>x/=; rewrite [X in _/\ X] (_:_ = True). 
    by apply: propT; exact: subsetT. by rewrite andB.1.2. rewrite bigcup_set1;
    have:= (@setT0 T). by move=>/eqP.
  have:= image_eq f. rewrite eqEsubset=> [[rfbs bsrf]].
  have: forall n, exists x:T, B (f n) /\ f n x.
    move:rfbs=>/[swap] n. rewrite/subset/= => /(_ (f n)).
    have:exists2 x, True & f x = f n by exists n. 
  move=> /[swap] /[apply] [[bfn /eqP /set0P [x fnx]]]. by exists x.
  move=> /choice [g gP]. exists (range g). 
  split=> [|U /[swap] /(bB U) -> /bigcup_nonempty [A/= [BA AU] /set0P /eqP An0]].
  apply: card_image_le. have: (B `\ set0) A by[]. move=> /bsrf [n _ fnA]. 
  exists (g n). split=>/=. by exists A=>//; rewrite -fnA;
  have [_] := gP n. by exists n.
Qed.

Lemma salgebra_second_countable {T : ptopologicalType} {B : set (set T)} : 
countable B -> basis B -> open.-sigma.-measurable = B.-sigma.-measurable.
Proof.
  move=> cB bB; have [f [rfb dec]] := countable_basis_to_seq cB bB. 
  rewrite eqEsubset -rfb=>/=; split; rewrite {1}/measurable/=. 
  apply: (@sigma_algebra_subset _ (g_sigma_algebraType (range f)))=> U /(dec U)->.
  apply: bigcup_measurable=>k/= _. by apply:sigma_algebra_gen.
  apply: sigma_algebra_subset. rewrite rfb. have [Bo _] := bB.
  exact: subset_trans Bo (sigma_algebra_gen).
Qed.

Lemma cvg_uniform_fin_bigcup {U : choiceType} {V : uniformType} [f : U -> V] 
[F : set_system (U -> V)] {I} [D : set I] {A : I -> set U} : Filter F -> 
finite_set D -> (forall i, D i -> {uniform A i, F --> f}) -> 
{uniform \bigcup_(i in D) A i, F --> f}.
Proof.
move=> fF /finite_setP [n]. move:D.
elim:n=>/=[D|n Ih D /eq_cardSP [x Dx /Ih Dxn] UD]. 
  rewrite II0 card_eq0 => /eqP -> _; rewrite bigcup0 => //=;
  exact: cvg_uniform_set0. rewrite -(setD1K Dx) bigcup_setU1. 
apply: cvg_uniformU. exact: (UD x). by apply: Dxn=>i [/UD Di//].
Qed.

End topology_lemmas.

Section norm_lemmas.

Definition norm_separable_set {K : numDomainType} {M : pseudoMetricType K} 
(A : set M) := exists D, [/\ countable D, D `<=` A & forall (x:M) (r : K), 
0<r -> A x -> exists d, D d /\ ball d r x].

Lemma bigcupT_norm_separable {K : numDomainType} {M : pseudoMetricType K}
[A : (set M)^nat] : (forall n, norm_separable_set (A n)) -> 
norm_separable_set (\bigcup_n A n).
Proof.
move=>/choice [D_ /all_and3 [cDx DAx dDx]]. exists (\bigcup_n D_ n); split.
  exact: bigcup_countable. exact: subset_bigcup. move=> x r r0 [n _ Anx].
have [d [Dnd bdrx]] := dDx n x r r0 Anx; exists d; split=>//. by exists n.
Qed.

Lemma bigcup_norm_separable {K : numDomainType} {M : pseudoMetricType K}
[A : (set M)^nat] [P : set nat] : (forall n, P n -> norm_separable_set (A n)) 
-> norm_separable_set (\bigcup_(i in P) A i).
Proof.
rewrite bigcup_mkcond => nsPA. apply: bigcupT_norm_separable=>n.
case: ifPn=>[|_]. rewrite in_setE. apply: (nsPA n). by exists set0; split.
Qed.

(* Needs pseudoMetricNormedZmodType to use ball_open lemma,
  and realType for rational radii *)
Lemma second_countable_ball {R : realType} {M : pseudoMetricNormedZmodType R} : 
@second_countable M -> exists D : set M, countable D /\
basis [set ball m k.+1%:R^-1 | m in D & k in [set:nat]].
Proof.
  move=> /second_countable_separable [D [cD dD]]. exists D. split=>//.
  split=>[U [n _ [k _ ]<-]|x U]. exact: ball_open.
  rewrite/dense in dD. rewrite -filter_from_ballE=> [[r/= r0 bxrU]].
  have xq2x : forall x:R, 0<x -> x / 2 < x. move=> z z0. rewrite ltr_pdivrMr=>//.
    rewrite ltr_pMr=>//. rewrite [1] (_:_ = (1:nat)%:R). by[]. by rewrite ltr_nat.
  have[eps [eps0 [eps1 bxeU]]]: exists eps:R, 0<eps /\ eps< 1 / 2 /\ ball x eps `<=`U.
    exists (minr 1 r / 4); split; rewrite/minr/=; case:ifPn=>//.
    by rewrite divr_gt0. split. rewrite ltr_pdivrMr=>//. 
    rewrite -[4]divr1 mulf_div mulr1 mul1r ltr_pdivlMr ?mul1r ?ltr_nat=>//=.
    have q1: ((1:nat)%:R/4 < (1 : R)) by rewrite ltr_pdivrMr ?mul1r ?ltr_nat.
    exact: subset_trans (le_ball (ltW (lt_trans q1 i))) bxrU. 
    rewrite -real_leNgt=>//. exact: num_real. move=> r1; split.
    rewrite ltr_pdivrMr=>//. apply: (le_lt_trans r1).
    rewrite div1r ltr_pdivlMl ?mulr1 ?ltr_nat=>//.
    have r4r: r/4 < r. rewrite ltr_pdivrMr ?ltr_pMr=>//.
      rewrite [1] (_:_ = (1:nat)%:R) ?ltr_nat//.
    apply: subset_trans (le_ball (ltW r4r)) bxrU.
  have [y//= [bxe3y Dy] ] : exists y:M, ball x (eps / 3) y /\ D y.
    apply: (dD _ _ (ball_open x (eps / 3))). exists x. 
    apply: (ballxx x); exact: divr_gt0.
  have eps2: 0<2/eps by rewrite ltr_pdivlMr ?mul0r.
  have t0 : (0%:R : R) < (truncn (2 / eps))%:R.
      rewrite ltr_nat truncn_gt0 ler_pdivlMr//mul1r.
      apply: ltW (lt_trans eps1 _). rewrite ltr_pdivrMr//= -natrM//=
      [1] (_:_ = (1:nat)%:R) ?ltr_nat//. 
  exists (ball y (truncn (2/eps))%:R^-1). split=>/=. exists y=>//=. 
    exists (subn (truncn (2/eps)) 1)=>//. rewrite -subSn. 
        rewrite truncn_gt0 ler_pdivlMr ?mul1r =>//. apply: (ltW (lt_trans eps1 _)).
        rewrite ltr_pdivrMr=>//.
        by apply: mulr_egt1; rewrite [1] (_:_ = (1:nat)%:R) ?ltr_nat.
      by rewrite subn1.
    rewrite ball_symE. have e2e3 : eps/3 < (truncn (2 / eps))%:R^-1.
      rewrite invf_pgt ?posrE//. by rewrite ltr_pdivlMr ?mul0r. 
      have /andP [t2eps _]:= truncn_itv (ltW eps2). apply: (le_lt_trans t2eps).
      rewrite invf_div ltr_pdivrMr// -{2}(divr1 eps) mulf_div 
      [X in _/X]mulrC -mulf_div divff ?divr1 ?mulr1 ?ltr_nat//; exact: lt0r_neq0.
    by apply: (le_ball (ltW e2e3)).
  apply: (subset_trans _ bxeU). rewrite -ball_normE => z /= fnz.
  apply: (le_lt_trans (ler_distD y x z)). rewrite [eps] (_:_ = eps/3 + 2/3*eps).
    rewrite mulrC -mulrDl [X in X*_] (_:_ = 1) ?mul1r// -div1r -{1}(mul1r (1/3))
      -mulrDl [1+2] (_:_ = 3)// div1r divff//.
  apply: ltrD. rewrite -ball_normE//= in bxe3y.
  apply: (lt_trans fnz). rewrite invf_plt ?posrE//. 
    by apply: mulr_gt0.
  have /andP[_ e2ts] := truncn_itv (ltW eps2). rewrite -{2}natr1 in e2ts.
  rewrite (pred_Sn (truncn (2/eps))). rewrite -subn1 natrB// ltrBrDl.
  apply: (lt_trans _ e2ts). rewrite -{1}(divr1 eps) mulf_div invf_div mulr1 
  ltr_pdivlMr // mulrDl mul1r -{3}(divr1 eps) mulf_div mulr1 -mulf_div divff.
    exact: lt0r_neq0. rewrite mulr1 {2}[2](_:_ = 1/2+3/2). 
    rewrite -mulrDl [1+3] (_:_ = 4)//. rewrite -natf_div//.
  by apply: ltr_leD.
Qed.

(* Should be generalized to metric spaces, 
but normedModType doesn't inherit from metricType yet*)
Lemma closed_dist0 {R:realType} {N:normedModType R} {F : set N} 
(cF : closed F) (x:N) :
F x = forall e:R, 0 < e -> exists f:N, F f /\ `|x - f| < e.
Proof.
  rewrite propeqE; split=>[Fx e|Cx]. exists x; split=>//=. by rewrite subrr normr0.
  have Q : forall n:nat, exists f:N, F f /\ `|x-f| < n.+1%:R^-1.
  move=> n; apply: (Cx n.+1%:R^-1)=>//.
  have [f Pf] := choice Q. apply: (@closed_cvg _ _ _ eventually_filter f _ cF).
  by exists 0=>// n _; have [Ffn _] := Pf n.
  apply/cvg_ballP=> e e0. rewrite pseudo_metric_ball_norm/=.
  have Pfe := (Pf (truncn (e^-1))). near=>n. apply: (@lt_trans _ _ (n.+1%:R^-1)).
  near:n. by apply: nearW=>n; have [_ d] := (Pf n).
  rewrite invf_plt=>//. by rewrite posrE. apply: (@lt_trans _ _ n%:R).
  near:n. exact: nbhs_infty_gtr. by rewrite ltr_nat.
Unshelve. all: end_near. Qed.

Lemma supP {R : realType} (S : set R) (x : R) (supS: has_sup S) :
sup S <= x <-> forall y, S y -> y<=x.
Proof.
split=> [sSx y Sy|Sx]. apply: (le_trans _ sSx); exact: sup_upper_bound. 
apply: ge_sup=>//. by apply/set0P/eqP=> S0; apply: (@has_sup0 _ R); rewrite -S0.
Qed.

Lemma gt_sup {R : realType} (S : set R) (x : R) (supS : has_sup S): 
sup S < x -> forall y, S y -> y<x.
Proof.
move=> sSx y Sy. apply: (le_lt_trans _ sSx); exact: sup_upper_bound.
Qed.

Lemma uniform_to_norm  {T : choiceType} {R : realType} {N : normedModType R} 
{f_ : (T->N)^nat} {f : T -> N} (A : set T) (An0 : A !=set0) (eps:R) (e0 : 0<eps):
{uniform A, f_ @ \oo --> f} -> 
\forall n \near \oo, forall t:T, A t -> `|f_ n t - f t| < eps.
rewrite -nbhs_entourageE uniform_entourage => [/filter_fromP/= Cuf].
set C := [set gf: (T->N)*_ | forall t, A t -> ball (gf.1 t) eps (gf.2 t)]. 
have: nbhs \oo (f_ @^-1` xsection C f). apply: Cuf. 
  apply: (@in_filter_from _ _ _ _ [set xy | ball xy.1 (PosNum e0)%:num xy.2]);
  exact: entourage_ball. rewrite /xsection/=. under eq_set do rewrite in_setE.
rewrite/C/= => [[n0 _ Cvn]]; exists n0=>//n/Cvn. rewrite -ball_normE/= => 
/[swap] t /[swap] At /(_ t At) fnte. by rewrite distrC.
Qed.

Lemma uniform_cvg_sup0 {T : choiceType} {R : realType} {N : normedModType R} 
{f_ : (T->N)^nat} {f : T -> N} (A : set T) (An0 : A !=set0):
{uniform A, f_ @ \oo --> f} <->
(\forall n\near \oo, has_sup [set `|f_ n x - f x| | x in A]) /\ 
sup [set `|f_ n x - f x| | x in A] @[n--> \oo] --> 0.
Proof.
split=>[/(uniform_to_norm An0) L |[[n1 _ has_sup_n1] /cvgr0Pnorm_lt s0]].
  split. have [n0 _ fNf1] := (L 1 ltr01).
    exists n0=>// n /fNf1 fnf1; split. exact: image_nonempty. 
    exists 1=>a [t At <-]. exact: (ltW (fnf1 t At)).
  apply/cvgr0Pnorm_le => e /(L e) [n0 _ fNfe]. exists n0=>// n /fNfe fnfe.
  have /normr_idP -> : 0 <= sup [set `|f_ n x - f x| | x in A] by
  apply: sup_ge0=>x /= [t At <-]; exact: normr_ge0. apply/supP=>[|y [t At <-]]. 
    split. exact: image_nonempty. exists e=> a [t At <-]. 
    1,2: try (exact: (ltW (fnfe t At))).
rewrite -nbhs_entourageE uniform_entourage -entourage_from_ballE => 
[F/= [G [H [e/=e0 beH] HG]]]. rewrite/xsection; under eq_set do rewrite in_setE.
have [n0 _ Nfe] := s0 e e0 => GF. exists (maxn n0 n1)=>// n. 
under eq_set do rewrite geq_max. move=> /andP /[dup] [[n0n n1n]] [/Nfe]. 
have /normr_idP -> : 0 <= sup [set `|f_ n x - f x| | x in A] by
  apply: sup_ge0=>x /= [t At <-]; exact: normr_ge0.
move=> /[swap] /(has_sup_n1) hs /(gt_sup hs) fnfe/=. apply: GF;
apply: HG=>t At; apply: beH=>/=. rewrite -ball_normE/= distrC. apply: fnfe.
by exists t.
Qed.

Lemma uniform_cvg_has_sup0 {T : choiceType} {R : realType} {N : normedModType R} 
{f_ : (T->N)^nat} {f : T -> N} (A : set T) (An0 : A !=set0):
{uniform A, f_ @ \oo --> f} <->
forall eps, 0<eps -> \forall n\near \oo, has_sup 
  [set `|f_ n x - f x| | x in A] /\ sup [set `|f_ n x - f x| | x in A] < eps.
Proof.
apply: (iff_trans (uniform_cvg_sup0 An0)); split=> [[hs /cvgr0_norm_lt s0 eps 
/(s0 eps) se]|S0]. near=>n; split. by near:n. rewrite -[X in X < _](normr_idP _). 
  apply: sup_ge0=> x [y _ <-]//. by near:n.
split. have [n _ nP] := S0 1 ltr01; exists n=>// n0 /nP [//].
apply/cvgr0Pnorm_lt=> eps /(S0 eps) [n0 _ ns]. exists n0=>// n /ns [_ se].
by rewrite (normr_idP _)//; apply: sup_ge0=> x [y _ <-]//.
Unshelve. all: end_near. Qed.

End norm_lemmas.

(*Should be moved to measurable_fun.v*)
Section measurable_fun_lemmas.

Lemma measurable_fun_open_closed {d} {aT : measurableType d} 
{T : topologicalType} {D : set aT} (f : aT -> T) :
measurable_fun D (f : aT -> g_sigma_algebraType (@open T)) = 
measurable_fun D (f : aT -> g_sigma_algebraType (@closed T)).
Proof.
  rewrite propeqE; split=> mf mD Y;
  [rewrite -open_closed_measurable| rewrite open_closed_measurable]; exact: mf.
Qed.

(*Cannot be generalized yet as it is for a different display from normr_continuous*)
Lemma normr_measurable_gen {R : realType} {N : normedModType R} {A : set N} : 
measurable_fun (A : set (g_sigma_algebraType open)) normr.
Proof.
  move=> /[dup] mA.
  apply: (@measurability _ _ _ _ _ (normr : g_sigma_algebraType open -> R) _).
  by rewrite/measurable/=/measurableR/measurable/=.
  move=> U [I [[a b] _] <-] <-/=. apply: measurableI=>//.
  rewrite /preimage/=. under eq_set do rewrite in_itv//=.
  have [nopen _] := continuousP (normr: N-> R).
  move: nopen => /(_ norm_continuous) nopen.
  rewrite [X in measurable X] (_:_ = normr@^-1`(`]a,+oo[) `&` ~`normr@^-1`(`]b,+oo[)).
    apply: eq_set=>/= x; rewrite in_itv propeqE. split=>[/andP [ax xb]|[/=/andP[ax _] xb]].
    split=>//. exact/andP. rewrite in_itv/==>/andP [bx _]. have:= le_lt_trans xb bx.
    by rewrite lt_irreflexive. apply/andP; split=>//. rewrite (real_leNgt _ _)=>//.
    exact: num_real. rewrite /not in_itv/= in xb; apply/negP=>bx; apply: xb; exact/andP.
  apply: measurableI. 
    apply: (@sigma_algebra_gen _ open) (nopen `]a,+oo[%classic (rray_open a)).
    apply: measurableC.
    exact: (@sigma_algebra_gen _ open) (nopen `]b,+oo[%classic (rray_open b)).
Qed.

Lemma measurable_funD_dist {d} {A : measurableType d} {R : realType} 
{N : normedModType R} {f g : A -> N} {D : set A}: norm_separable_set (image D f)
-> measurable_fun D (f: A -> g_sigma_algebraType open) -> 
measurable_fun D (g: A -> g_sigma_algebraType open) -> measurable D ->
forall (r:R), 0<r -> measurable (D `&` [set a | `|f a - g a| < r]).
Proof.
move=> [Df [cDf _ DF]] mf mg mD r r0. rewrite [X in measurable X] (_:_ = 
\bigcup_q \bigcup_(z in Df) \bigcup_(k in [set k | rat.ratr q + k.+1%:R^-1 < r])
(D `&` f@^-1`(ball z k.+1%:R^-1) `&` (D `&` g@^-1`(ball z (rat.ratr q))))).
  rewrite eqEsubset /bigcup; split=>[x [Dx /= fgxr]|x [q _ /= [z Dfz] [k qkr] 
      [[Dx bzkf] [_ bzqg]]]].
    have fgrne : `]`|f x - g x|, r[%classic !=set0. exists ((`|f x - g x|+r)/2).
      rewrite/=in_itv/=. apply/andP;split; by apply (midf_lt fgxr).
    have[q]:= dense_rat fgrne (itv_open `|f x - g x| r). 
    rewrite /=in_itv=>/= [[/andP[fgq qr]] [q1 _ q1q]].
    pose eps := minr (q - `|f x - g x|) (r-q). pose k := truncn eps^-1.
    have eps0 : 0 < eps by rewrite lt_min !subr_gt0; apply/andP.
    have [erq eqfg] : eps <= r-q /\ eps <= q - `|f x - g x|. 
      rewrite !ge_min; split; apply/orP. by right. by left.
    exists q1=>//=. rewrite q1q/=.
    have ke : k.+1%:R^-1 < eps by rewrite invf_plt ?posrE//; 
      exact: truncnS_gt.
    have k0 : (0:R) < k.+1%:R^-1 by rewrite invr_gt0.
    have [z [Dfz b1]]:= (DF (f x) _ k0 (imageP f Dx)).
    exists z=>//. exists k. rewrite -ltrBrDl. exact: (lt_le_trans ke erq).
    split=>//; split=>//. rewrite -ball_normE/=. rewrite -ball_normE/= in b1.
    apply: (le_lt_trans (ler_distD (f x) z (g x))).
    have zfq : `|z - f x| < q - `|f x - g x| by apply: (lt_le_trans 
      (lt_trans b1 ke) eqfg).
    apply: (lt_le_trans (ltr_leD zfq (le_refl _))). 
    by rewrite -addrA [X in _ + X]addrC subrr addr0.
  split=>//. rewrite -ball_normE /= in bzkf, bzqg. 
  apply: (le_lt_trans (ler_distD z _ _)). rewrite {1}distrC addrC. 
  exact: (lt_trans (ltrD bzqg bzkf) qkr).
apply: bigcupT_measurable_rat=> q. apply: countable_bigcup_measurable=>// z Dfz.
apply: bigcup_measurable=>k /= qkr. apply: measurableI. apply: (mf mD).
  apply: sigma_algebra_gen; exact: ball_open.
apply: (mg mD). apply: sigma_algebra_gen; exact: ball_open.
Qed.

(* Lemma 4.29 Infinite Dimensional Analysis A Hitchhikers Guide, 
Third Edition (Charalambos D. Aliprantis, Kim C. Border)*)
Lemma measurable_fun_cv {d} {T : measurableType d} {R : realType} 
{X : normedModType R} [D : set T] [h : (T->X)^nat] [f : T -> X] : 
(forall m:nat, measurable_fun D (h m : T -> g_sigma_algebraType open)) -> 
(forall x : T, D x -> h ^~ x @\oo --> f x)
-> measurable_fun D (f : T -> g_sigma_algebraType open).
Proof.
  move=> mhn hf; rewrite measurable_fun_open_closed. 
  rewrite/measurable_fun=> /[dup] mD. apply: measurability=>// C. case=>F cF<-.
  pose G := fun n => [set y | exists c:X, c \in F /\ `|c-y| < (n.+1%:R)^-1].
  rewrite [D`&`f@^-1` F] (_:_ = \bigcap_m \bigcup_n \bigcap_(k>=n) 
  (D`&`(h k)@^-1`(G m))).
  rewrite eqEsubset; split=>[x/= [Dx Cfx]|x b/=].
    rewrite/bigcup/bigcap/G/==> m _. have mp : 0<m.+1%:R^-1. move=>N; 
    by rewrite invr_gt0. 
    have:= @cvg_ball _ _ _ _ eventually_filter _ _ (hf x Dx) _ (mp _).
    move=>[n0 _]; rewrite/subset/==>bn0. exists n0=>// n n0n; split=>//. 
    exists (f x). split. by rewrite in_setE. 
    by have:= (bn0 _ n0n); rewrite -ball_normE/=.
    split; rewrite/bigcup/bigcap/= in b. 
    by have [i _]:= (b 0 I)=> /(_ i (le_refl i)) [Dx _].
  have [i _]:= (b 0 I)=> /(_ i (le_refl i)) [Dx _].
  rewrite (@closed_dist0 R X F cF) => e e0. rewrite (splitr e).
  have e20 : 0 < e/2 by apply: divr_gt0=>//.
  have [n0 _] := b (truncn (e/2)^-1) I.
  have [n1 _ bfehn]:= @cvg_ball _ _ _ _ eventually_filter _ _ (hf x Dx) _ e20.
  rewrite /G => /= /(_ (maxn n0 n1) (leq_maxl n0 n1)) [_ [f0 [f0F yhe]]].
  rewrite /subset/= in bfehn.
  have := bfehn (maxn n0 n1) (leq_maxr n0 n1). rewrite -ball_normE=> /= fhn0e.
  exists f0; split. by rewrite -in_setE. 
    rewrite -(subrKA (h (maxn n0 n1) x) (f x) (-f0)).
    apply: (le_lt_trans (ler_normD (f x-h (maxn n0 n1) x) (h (maxn n0 n1) x-f0))). 
    apply: ltrD=>//. rewrite distrC; apply: (lt_trans yhe).
    rewrite invf_plt=>//. by rewrite posrE.
    exact: truncnS_gt.
  apply: bigcap_measurable=>// m _. apply: bigcup_measurable=>// n _. 
  apply: bigcap_measurable. exists n=>//=. rewrite /G=> k /= nk.
  apply: (mhn k)=>//. apply: (@sigma_algebra_gen _ open).
  rewrite [X in open X] (_:_ = \bigcup_(c in F) [set y | `|c-y| < m.+1%:R^-1]).
  apply eq_set=> x/=. rewrite exists2E; apply: eq_exists=>y/=. by rewrite in_setE.
  apply: bigcup_open=> f0 f0F. have df0c : continuous (normr \o(fun y=> f0-y)).
  move=> x. apply: continuous_comp. apply: continuousB=>//. exact: cst_continuous.
  exact: norm_continuous. rewrite -preimage_itvNyo.
  exact: open_comp.
Qed.

End measurable_fun_lemmas.

Section measure_lemmas.
Context d {T : measurableType d} {R : realType} {mu : {measure set T -> \bar R}}.

Lemma measure0P {A} : (forall eps, 0<eps -> (mu A < eps%:E)%E) -> mu A = 0.
Proof.
move=> mAe. apply/eqP; rewrite eq_le; apply/andP; split=>//.
apply/le_ltP=> z z0. have [/(_ (ltW z0)) [->|[r r0 rz]] _] := (gee0P z).
  apply: (lt_trans (mAe 1 (ltr01))). exact: ltry. 
by move: z0; rewrite rz lte_fin=> /mAe.
Qed.

Lemma measure0P_invn {A} : (forall n, (mu A < n.+1%:R^-1%:E))%E -> mu A = 0.
Proof.
move=> mAn; apply/measure0P=>eps e0. apply: (lt_trans (mAn (truncn eps^-1))).
rewrite lte_fin invf_plt ?posrE //; exact: truncnS_gt.
Qed.

End measure_lemmas.

Section almost_uniform_cvg.
Context {d} {T : measurableType d} {R : realType} 
{U : pseudoMetricType R} (mu : {measure set T -> \bar R})
(f_ : (T->U)^nat) (f : T -> U).

Definition almost_uniform_cvg  (D : set T) :=
forall eps:R, 0<eps -> exists E, [/\ measurable E, (mu E < eps%:E)%E &
    {uniform D `\` E, f_ @ \oo --> f}].

Definition almost_uniform_cvgT :=
forall eps:R, 0<eps -> exists E, [/\ measurable E, (mu E < eps%:E)%E &
    {uniform ~`E, f_ @ \oo --> f}].

Lemma almost_uniform_cvgTP : almost_uniform_cvg [set:T] <-> almost_uniform_cvgT.
Proof.
by rewrite /almost_uniform_cvg/almost_uniform_cvgT;
  under eq_forall do under eq_exists do rewrite setTD.
Qed.

Lemma almost_uniform_cvg_nnincseqP (D : set T) (h : R^nat) 
(ph : forall n, 0 < h n) (h0 : h @ \oo --> 0) : almost_uniform_cvg D <->
exists E_ : (set T)^nat, {homo E_ : n m / (n<=m)%N >-> (m<=n)%O} /\
  forall n, [/\ measurable (E_ n), (mu (E_ n) < (h n)%:E)%E & 
  {uniform D`\`(E_ n), f_ @ \oo --> f}].
Proof.
split=>[aucD|[E_ [nniE /all_and3 [mE0 mEn CuEn] eps e0]]].
  have /choice [E /all_and3 [mE0 mEn CuEn]] : forall n, exists E, 
  [/\ measurable E, (mu E < (h n)%:E)%E & {uniform D`\`E, f_ @ \oo --> f}] by
    move=>n; apply: (aucD (h n)).
  exists (fun n => \bigcap_(k < n.+1) (E k)); split.
  apply/nonincreasing_seqP=>n/=.
  rewrite subsetEset/bigcap => x /= bn2x i in1; 
    exact: (bn2x i (ltn_trans in1 (ltnSn n.+1))).
  move=>n. split. apply: bigcap_measurableType=>//.
    apply: (le_lt_trans _ (mEn n)). apply: le_measure; rewrite ?in_setE//.
      apply: bigcap_measurableType=>//. apply: bigcap_inf=>/=; exact: ltnSn.
  rewrite -bigcapDr; exact: cvg_uniform_fin_bigcup.
have [n0 _ /=/(_ n0 (le_refl n0))]:= cvgr0_norm_lt h h0 eps e0.
rewrite (normr_idP (ltW (ph n0)))=> hne; exists (E_ n0); split=>//.
exact: lt_trans.
Qed.

End almost_uniform_cvg.

Section egorov.
Context d {R : realType} {N : normedModType R}
 {T : measurableType d} {mu : {finite_measure set T -> \bar R}}.
Local Open Scope ereal_scope.

(* A more general version of Erogov's theorem *) 
Lemma pointwise_almost_uniform_sep (f : (T -> N)^nat) (g : T -> N) 
  (D : set T) : (forall n, norm_separable_set (image D (f n)))
  -> (forall n, measurable_fun D (f n : T -> g_sigma_algebraType open)) ->
  measurable D -> (forall x, D x -> f ^~ x @ \oo --> g x) ->
  almost_uniform_cvg mu f g D.
Proof.
  move=> sf mf mD fg eps e0. pose A n k := D `&` 
  [set x | (`|f n x - g x| >=k.+1%:R^-1)%R]. have mg := measurable_fun_cv mf fg.
  have mA : forall n k, measurable (A n k).
    rewrite /A/==>n k. rewrite -setDD {2}/setD/= [X in _`\`X] (_:_ = 
    [set x| D x /\ (`|f n x - g x| < k.+1%:R^-1)%R]).
      apply: eq_set=>x. rewrite propeqE; split=>/=[[Dx nle]|[Dx lt]]; split=>//.
        apply: (contra_not_lt nle)=>//. 
      exact: (@contra_lt_not _ _ (k.+1%:R^-1 <= `|f n x - g x|)%R _ _ _ lt).
    apply: measurableD=>//. exact: measurable_funD_dist.
  pose B n k := \bigcup_(i>=n) A i k. have mB: forall n k, measurable (B n k) 
    by rewrite/B=> n k; apply: bigcup_measurable.
  have capB_0 : forall k, \bigcap_n B n k = set0.
    rewrite/bigcap/B/bigcup/A/==>k; rewrite -subset0 =>a/=. apply: contraPP=> _. 
    rewrite -existsNE. under eq_exists=>n do rewrite not_implyE exists2E -forallNE.
    have[ad|nad]:= boolP (a\in D). rewrite in_setE in ad.
    have invkp : (0 < k.+1%:R^-1)%R. by move=> t; rewrite invr_gt0.
    have [n0 _ P]:= @cvg_ball _ _ _ _ eventually_filter _ _ (fg a ad) _ (invkp R).
    exists n0. split=>// n [n0n [_ kfg]].
    have:= P n n0n. rewrite -ball_normE/= -normrN opprB=>fgk.
    by have := (le_lt_trans kfg fgk); rewrite (lt_irreflexive k.+1%:R^-1%R).
    exists (0:nat). split=>//n.
    by rewrite not_andE not_andE; right; left; rewrite -notin_setE.
  have cvB0 : forall k, fine (mu (\bigcap_(i<n) B i k)) @[n --> \oo] --> 0%R.
    move=>k. rewrite [0%R] (_:_ = fine (mu (\bigcap_n B n k))). 
    by rewrite capB_0 measure0. apply: fine_cvg; rewrite fineK ?fin_num_measure//.
    exact: bigcap_measurable. exact: bigcap_cvg_mu (mB ^~ k).
  have nk_cap : forall k, exists n, true -> mu (\bigcap_(i<n) B i k) <= (eps/(2^+(k+2))%:R)%:E.
    move=>k. have ekp : (0 < eps/(2^(k+2))%:R)%R by rewrite ltr_pdivlMr ?mul0r. 
    have [n0 _ P] := @cvg_ball R _ _ _ eventually_filter _ _ (cvB0 k) _ ekp.
    exists n0=> _. rewrite -[X in X <= _](fineK) ?fin_num_measure//.
    apply: bigcap_measurableType=>//.
    rewrite lee_fin/=. have:= P n0 (le_refl n0). rewrite/ball/=sub0r normrN 
    ger0_norm -?lee_fin ?fineK ?fin_num_measure//; try (exact: bigcap_measurableType).
    rewrite -lte_fin fineK ?fin_num_measure//. exact: bigcap_measurableType. 
    rewrite /lee/lte/=lt_def_ereal => /andP[_ c2]//.
  have [p pBe] := choice nk_cap. have mBp : forall k:nat, 
    measurable (\bigcap_(i<p k) (B i k)). move=>k; apply: bigcap_measurableType=>//.
  pose C := (\bigcup_k \bigcap_(i<(p k)) (B i k)). exists C.
  split=>[||]. exact: bigcupT_measurable.
    apply: (le_lt_trans (generalized_Boole_inequality mu mBp _)).
    exact: bigcup_measurable. have nn_muB : forall i:nat, (0 <= i)%N -> true -> 
      0%R <= mu (\bigcap_(i0 < p i)  B i0 i). move=> i _ _; exact: measure_ge0.
    have:= lee_nneseries nn_muB pBe. rewrite (@cvg_lim _ (@ereal_hausdorff R) 
    _ _ eventually_filter _ _ (@cvg_geometric_eseries_half _ eps 1)).
    move=> mBe2; apply: (le_lt_trans mBe2).
    rewrite lte_fin expr1 ltr_pdivrMr ?ltr_pMr ?ltr1n=>//.
  apply/uniform_restrict_cvg=> U/=; rewrite uniform_nbhsT.
  case/nbhs_ex => r /= ballU; apply: filterS; first by move=> ?; exact: ballU.
  have [n0 _ /(_ n0)/(_ (leqnn _)) n0ir] := near_infty_natSinv_lt r.
  exists (p n0)=>// n /=pn0n x; rewrite /patch. case: ifPn=>//.
  rewrite in_setD=>/andP[xD]. rewrite in_setE in xD; 
  rewrite -in_setC in_setE/C setC_bigcup {1}/bigcap.
  under eq_set do under eq_forall do rewrite setC_bigcap.
  rewrite /B/A/bigcup/= => /(_ n0) /(_ I) [i ipn]. 
  rewrite exists2E -forallNE=> /(_ n).
  rewrite -implypN -implypN => /(_ (ltnW (@lt_le_trans _ _ _ i _ ipn pn0n)) xD). 
  move=> /negP. rewrite -real_ltNge=>//fgn0; apply: (le_ball (ltW n0ir)). 
  by rewrite ball_symE -ball_normE.
Qed.

End egorov.


Section mu_measurable_function. (* will be moved to bochner_integral.v*)
Import HBSimple.
Context {d} {T : measurableType d} {R : realType}
  (mu : {finite_measure set T -> \bar R}) (X : normedModType R).

Definition mu_measurable (f: T -> X) := exists f_ : {sfun T >-> X}^nat, 
\forall x \ae mu, f_ n x @[n --> \oo]--> f x.

Lemma ae_forall2 {P1 P2 Q: T -> Prop} : (forall x, P1 x /\ P2 x -> Q x) -> 
(\forall x \ae mu, P1 x) -> (\forall x \ae mu, P2 x) -> \forall x \ae mu, Q x.
Proof.
  move=> P12Q [A [mA mA0 p1A]] [B [mB mB0 p1B]]. exists (A`|`B); split. 
  exact: measurableU. exact: null_set_setU. 
  have P12sQ: [set x | P1 x]`&`[set x | P2 x] `<=`[set x | Q x] 
  by rewrite /setI=>x/=; exact:P12Q. apply: (subset_trans (subsetC P12sQ)); 
  rewrite setCI; exact: setUSS.
Qed.

Lemma mmeas_meas (f : T -> X) (mmf : mu_measurable f) : measure_is_complete mu
 -> measurable_fun [set:T] (f : T -> g_sigma_algebraType open).
Proof.
case:mmf=> F [A [mA mA0 /subsetCl cv]] cmu. rewrite -(setvU A).
apply/measurable_funU=>//. exact: measurableC. split=>[|_ Y mY].
  apply: measurable_fun_cv _ cv=>m. apply: measurable_funP.
apply: cmu. apply: (negligibleS (@subIsetl _ A (f@^-1`Y))).
by exists A; split.
Qed.

Lemma mmeasD (f g : T -> X) (mmf : mu_measurable f) (mmg : mu_measurable g) :
mu_measurable (f + g).
Proof.
  case: mmf=> F aFf; case: mmg=> G aGg. exists (F+G). 
  have cvgD : forall x:T, (F n x @[n --> \oo] --> f x) /\ (G n x @[n --> \oo] --> g x)
  -> (F n x + G n x @[n --> \oo] --> f x + g x) 
  by move=> x [Ffx Ggx]; exact: fun_cvgD.
  by apply: (ae_forall2 cvgD).
Qed.

Lemma mmeasZ (x : R) (f : T -> X) (mmf : mu_measurable f) : 
mu_measurable (x *: f).
Proof.
case: mmf=> F [A [mA mA0 CnA]]. exists (x*:F); exists A; split=>//.
apply: (subset_trans _ CnA). apply: subsetC=>y /=. exact: cvgZl_tmp.
Qed.

Lemma sfun_norm_sep_val (f : {sfun T >-> X}) (D:set T) : 
norm_separable_set (image D f).
Proof.
exists (image D f); split=>//[|y r r0 [x Dx <-]]. apply: finite_set_countable. 
  exact: (sub_finite_set (image_subset f (subsetT D))).
exists (f x); split=>//; exact: (ballxx (f x) r0).
Qed.

Lemma mmeas_almost_uniformP (f : T -> X) : mu_measurable f <-> 
exists (f_ : {sfun T >-> X}^nat), almost_uniform_cvgT mu f_ f.
Proof.
split=> [[f_ [N [mN mN0 /subsetCl f_fN]]]|[f_] Cf]. exists f_=> eps eps0.
  have nsf_ : forall n, norm_separable_set [set f_ n x  | x in ~` N] by move=>n;
    apply: sfun_norm_sep_val.
  have mf_ : forall n, measurable_fun (~`N) (f_ n) by move=>n; 
    exact: (measurable_funS measurableT). 
  have[E [mE0 mEe f_fnE]]:= @pointwise_almost_uniform_sep _ _ _ _ mu f_ f (~`N) 
    nsf_ mf_ (measurableC mN) f_fN eps eps0.
  exists (E`|`N); split. exact: measurableU. by rewrite measureU0.
  rewrite [~`(E `|` N)] (_:_ = ~`N `\` E); by rewrite // setDE setCU setIC.
have /choice [E_ /all_and3 [mE mEn Une]] : forall n, exists E, [/\ measurable E, 
  (mu E < n.+1%:R^-1%:E)%E & {uniform ~`E, (f_ : (T->X)^nat) @ \oo --> f}] 
  by move=>n; exact: (Cf n.+1%:R^-1).
exists f_. exists (\bigcap_n (E_ n)); split. exact: bigcap_measurable.
  apply: measure0P_invn=>//n. 
  apply: (le_lt_trans (le_measure mu _ _ (bigcap_inf _)) (mEn n)); 
    rewrite ?in_setE //. exact: bigcap_measurableType. 
apply: subsetCl. rewrite setC_bigcap=> z [i _ nEi]/=.
rewrite -in_setE -sub1set in nEi. 
have: {uniform [set z], (f_ : (T->X)^nat) @ \oo --> f} 
  by apply: (uniform_subset_cvg _ nEi).
by rewrite uniform_set1.
Qed.

Lemma mmeas_almost_uniformP_invn (f : T -> X) : mu_measurable f <-> 
exists (f_ : {sfun T>->X}^nat), forall n, exists E, [/\ measurable E, 
(mu E < n.+1%:R^-1%:E)%E & {uniform (~`E), (f_ : (T->X)^nat) @ \oo --> f}].
Proof.
split=>[/mmeas_almost_uniformP [f_ Uf]|[f_ Ufn]]. 
  exists f_=> n; exact: (Uf n.+1%:R^-1).
apply/mmeas_almost_uniformP; exists f_ => eps e0. 
have [Ee [mEe mEee UEe]] := Ufn (truncn eps^-1); exists Ee; split=>//.
apply: (lt_trans mEee). rewrite lte_fin invf_plt ?posrE//; exact: truncnS_gt.
Qed.

Lemma mmeas_cvg (f : (T -> X)^nat) (g : T -> X) 
(mmf : forall n:nat, mu_measurable (f n)) (fg : forall x, f ^~ x  @\oo--> g x) :
mu_measurable g.
Proof.
have /choice [f_ /choice [E0_ /all_and2 [decE0 mE0_]]] : forall n,
  exists (fn_ : {sfun T>->X}^nat), exists En_ : (set T) ^nat, 
  {homo En_ : n m / (n <= m)%N >-> (m<=n)%O} /\ forall k : nat, 
  [/\ d.-measurable (En_ k),  (mu (En_ k) < (k.+2%:R^-1 * 2^-n.+1)%:E)%E & 
  {uniform ~`En_ k, (fn_ : (T->X)^nat) @\oo --> f n}].
  move=>n; have /mmeas_almost_uniformP[fn_ /almost_uniform_cvgTP sfnf] := mmf n;
  exists fn_. under eq_exists do under eq_forall do rewrite -setTD.
  apply/almost_uniform_cvg_nnincseqP=>//. apply/cvgr0Pnorm_lt=> eps e0; near=>k. 
  rewrite (normr_idP _) ?invr_ge0//; apply: (@lt_trans _ _ k.+2%:R^-1).
    rewrite ltr_pdivrMr // ltr_pMr // exprn_egt1 // [1] (_:_ = (1:nat)%:R) 
      ?ltr_nat //. apply: (@lt_trans _ _ k.+1%:R^-1). 
    rewrite invf_plt ?posrE// -[X in X^-1]div1r invf_div divr1 ltr_nat//.
  near:k; apply: (near_infty_natSinv_lt (PosNum e0)).
pose E_ k := \bigcup_n E0_ n k.
have [dE /all_and3 [mE mEk UEk]] : {homo E_ : n m / (n<=m)%N >-> (m<=n)%O} /\ 
forall k, [/\ measurable (E_ k), (mu (E_ k) < k.+1%:R^-1%:E)%E & ~`E_ k !=set0 
-> forall n, (\forall m \near \oo, 
  has_sup [set `|f_ n m x - f n x| | x in ~`E_ k]) /\ 
  sup [set `|f_ n m x - f n x| | x in ~`E_ k] @[m --> \oo] --> 0].
  split=>[n m nm |k]. by rewrite subsetEset; apply: subset_bigcup => i _;
    rewrite -subsetEset; exact: (decE0 i).
  have /all_and3 [mE0 mE0nk UE0]: forall n, [/\ forall k, measurable (E0_ n k), 
  forall k, (mu (E0_ n k) < (k.+2%:R^-1 / 2^+n.+1)%:E)%E & forall k, {uniform 
    ~`E0_ n k, (f_ n : (T->X)^nat) @\oo --> f n}]. move=>n; exact: all_and3.
  split. exact: bigcupT_measurable.
    have k20: (0:R) <= k.+2%:R^-1 by rewrite invr_ge0.
    have leE0k: forall n, xpredT n -> 
      (mu (E0_ n k) <= (k.+2%:R^-1 / 2^+n.+1)%:E)%E 
      by move=> n _; exact: (ltW (mE0nk n k)).
    apply: (le_lt_trans (le_mu_bigcup _ _ _))=>//. exact: bigcupT_measurable.
    apply: (le_lt_trans (lee_nneseries _ leE0k))=> [i _ _|]. exact: measure_ge0.
    under eq_eseriesr do rewrite -natrX.
    apply (le_lt_trans (epsilon_trick0 xpredT k20)).
    by rewrite lte_fin invf_plt ?posrE// invrK ltr_nat.
  move=> nEk0 n. have EkE0 : ~` E_ k `<=` ~` E0_ n k by apply: subsetC; 
    exact: bigcup_sup. apply (uniform_cvg_sup0 nEk0). 
    apply: (uniform_subset_cvg _ EkE0). exact: (UE0 n k).
have /choice [M PM] : forall t, exists mt, forall x,
  (~` E_ t.1) x -> `|f_ t.2 mt x - f t.2 x| < t.2.+1%:R^-1. move=> [k n]. 
  have [->| /set0P nEk0] := eqVneq (~`E_ k) set0. by exists 0.
  have invn0 : (0:R) < n.+1%:R^-1 by rewrite invr_gt0.
  have [[m1 _ hsup] /cvgr0Pnorm_lt/(_ _ invn0) 
    [m2 _  sup0]] := UEk k nEk0 n. exists (maxn m1 m2)=>x nEkx.
  have hsupm := hsup _ (leq_maxl m1 m2); 
  have := sup0 _ (leq_maxr m1 m2). rewrite (normr_idP _). 
    apply: sup_ge0=> y /= [z _ <-]; exact: normr_ge0.
  move=> /(gt_sup hsupm) supn. by apply: supn=>/=; exists x.
exists (fun n => f_ n (M (n, n))); exists (\bigcap_k (E_ k)).
split. exact: bigcap_measurableType. apply/measure0P_invn=>n.
  apply: (le_lt_trans (le_measure mu _ _ (bigcap_inf _)) (mEk n)); 
    rewrite ?in_setE //. exact: bigcap_measurableType.
apply: subsetCl. rewrite setC_bigcap => x [i _ nEi] /=.
apply/cvgrPdistC_lt=> eps e0. have e20: 0 < eps/2 by rewrite ltr_pdivlMr ?mul0r.
have /=fnge2 := cvgr_distC_lt (f ^~ x) (g x) (fg x) _ e20.
have /=n2e2 := near_infty_natSinv_lt (PosNum e20). near=>n.
rewrite (splitr eps). apply: (le_lt_trans (ler_distD (f n x) _ _) (ltrD _ _)).
  have /(dE i n) : (i<=n)%N by near:n; exact: nbhs_infty_ge. 
  rewrite subsetEset => /subsetC /(_ x nEi) dEin.
  apply: (lt_trans (PM (n,n) x dEin))=>/=. by near:n. by near:n; apply: fnge2.
Unshelve. all: end_near. Qed.

(* Mix of lemma 11.37 in Infinite Dimensional Analysis : a Hitchhiker's guide
  and thm2 (petti's measurability theorem) in Vector Measures (math survey)*)
Lemma mmeas_meas_ess_sepP (f : T -> X) : mu_measurable f <-> exists A, 
  [/\ measurable A, mu A = 0,  measurable_fun (~`A)
  (f : _ -> g_sigma_algebraType open) & norm_separable_set (image (~`A) f)].
Proof.
  split=>[/mmeas_almost_uniformP_invn [f_ /choice[E_ /all_and3 [mE mEn UEn]]]|].
  exists (\bigcap_n E_ n); split. exact: bigcap_measurableType.
      apply: measure0P_invn=>n. apply: (le_lt_trans 
        (le_measure mu _ _ (bigcap_inf _)) (mEn n)); rewrite ?in_setE //. 
      exact: bigcap_measurableType.
    apply: (@measurable_fun_cv _ _ _ _ _ f_). move=> m. 
      exact: (measurable_funS measurableT). rewrite setC_bigcap=> x [i _ nEix].
    have nEin0 : ~`E_ i !=set0 by exists x.
    apply/cvgrPdist_lt=> eps e0.
    have /(uniform_cvg_has_sup0 nEin0) /(_ eps e0) [n0 _ nhs] := UEn i.
    exists n0=>// n /nhs [hsn sne].
    
(* exists (maxn n1 n2)=>//n. rewrite /= geq_max => /andP[/hsn1 n1n /s0n2].
    rewrite distrC (normr_idP _). apply: sup_ge0=> y [z _ <-]//.
    move=> /(gt_sup n1n)/= /(_ `|f_ n x - f x|) se; apply: se. by exists x.
  rewrite setC_bigcap image_bigcup.
  apply: bigcupT_norm_separable=>n.
  have[->|/set0P nEn0]:= eqVneq (~`E_ n) set0. 
    by rewrite image_set0; exists set0; split.
  have /(uniform_cvg_sup0 nEn0) [hs /cvgr0_norm_lt s0] := UEn n. *)
Abort.


End mu_measurable_function.