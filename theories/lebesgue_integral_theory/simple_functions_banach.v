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

(* Will be moved to measurable_structure.v *)
Lemma sigma_algebra_subset {d} {M : measurableType d} {H : set (set M)}
(mH : H `<=`d.-measurable) : <<s H>> `<=` measurable.
Proof.
  by rewrite /smallest/bigcap=> K/= /(_ d.-measurable) oK; apply: oK;
  split=>[|//]; apply:sigma_algebra_measurable.
Qed.

Lemma sigma_algebra_gen {d} {M : measurableType d} {G : set (set M)} : G `<=`<<s G>>.
Proof.
  by rewrite /smallest=>A hA H [saH GH]; apply: GH.
Qed.

Section mu_measurable_function. (* will be moved to bochner_integral.v*)
Import HBSimple.
Context {d} {T : measurableType d} {R : realType}
  (mu : {finite_measure set T -> \bar R}) (X : normedModType R).

Definition mu_measurable (f: T -> X) := exists f_ : {sfun T >-> X}^nat, 
\forall x \ae mu, f_ n x @[n --> \oo]--> f x.

Lemma ae_forall2 {P1 P2 Q: T -> Prop} : (forall x, P1 x /\ P2 x -> Q x) -> 
(\forall x \ae mu, P1 x) -> (\forall x \ae mu, P2 x) -> \forall x \ae mu, Q x.
Proof.
  move=> P12Q [A [mA mA0 p1A]] [B [mB mB0 p1B]]. exists (A`|`B); split. exact: measurableU.
  exact: null_set_setU. have P12sQ: [set x | P1 x]`&`[set x | P2 x] `<=`[set x | Q x] 
  by rewrite /setI=>x/=; exact:P12Q. apply: (subset_trans (subsetC P12sQ)); 
  rewrite setCI; exact: setUSS.
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

Lemma measurable_fun_open_closed {t : topologicalType} {D : set T} (f : T -> t) :
measurable_fun D (f : T -> g_sigma_algebraType (@open t)) = 
measurable_fun D (f : T -> g_sigma_algebraType (@closed t)).
Proof.
  rewrite propeqE; split=> mf mD Y;
  [rewrite -open_closed_measurable| rewrite open_closed_measurable]; exact: mf.
Qed.

Lemma closed_dist0 {R:realFieldType} {M:metricType R} {F : set M} 
(cF : closed F) (x:M) :
F x <-> forall e:R, exists f:M, F f /\ mdist x f < n.+1%:R^-1.
Proof.
  split=>[Fx n|Cx]. exists x; split=>//. by rewrite mdistxx.
  have [f Ffx]:= choice Cx.

Lemma measurable_fun_cv [D : set T] [h : (T->X)^nat] [f : T -> X] : 
(forall m:nat, measurable_fun D (h m : T -> g_sigma_algebraType open)) -> (forall x : T, D x -> h ^~ x @\oo --> f x)
-> measurable_fun D (f : T -> g_sigma_algebraType open).
Proof.
  move=> mhn hf; rewrite measurable_fun_open_closed. 
  apply: measurability=>// C. case=>F cF<-.
  pose G := fun n => [set y | exists c:X, c \in F /\ `|c-y| < (n.+1%:R)^-1].
  rewrite [D`&`f@^-1` F] (_:_ = D`&`\bigcap_m \bigcup_n \bigcap_(k>=n) (h k)@^-1`(G m)).
  rewrite eqEsubset; split=>[x/= [Dx Cfx]|x /=[Dx]]; split=>//. rewrite/bigcup/bigcap/G/==> m _.
  have mp : 0<m.+1%:R^-1. move=>N; by rewrite invr_gt0. 
  have:= @cvg_ball _ _ _ _ eventually_filter _ _ (hf x Dx) _ (mp _).
  move=>[n0 _]; rewrite/subset/==>bn0. exists n0=>// n n0n; exists (f x).
  split. by rewrite in_setE. by have:= (bn0 _ n0n); rewrite -ball_normE/=.
  rewrite/bigcup/bigcap/= in b. 






  rewrite eqEsubset; split=>[x/= [Dx fxV]| x/=[Dx [n0 _ caphV]]]. split=>//. rewrite /bigcup/bigcap/=.
  have:= open_subball oV fxV. case=> r/= rpos br.
  have r2pos : 0<r/2 by rewrite ltr_pdivlMr//mul0r.
  have:= @cvg_ball _ _ _ _ eventually_filter _ _ (hf x Dx) _ r2pos.
  move=>[n0 _ ]; rewrite/subset/==>bn0.
  exists n0=>// i ir. rewrite /subset/= in br.
  apply: (br (r/2)). rewrite add0r normrN normrZ gtr0_norm//gtr_pMr//.
  rewrite gtr0_norm. by rewrite invr_gt0. rewrite invf_lt1// Rint_ltr_addr1=>//;
  exact: Rint1. rewrite ltr_pdivlMr//mul0r//. exact: bn0.
  split=>//. apply: (open_subball oV).


(*TODO : remove the cast when top_meas will be automatic*)
Lemma mmeas_meas (f : T -> X) (mmf : mu_measurable f) : 
measurable_fun [set:T] (f : T -> g_sigma_algebraType (@open X)).
Proof.
  case:mmf=> F [A [mA mA0 cv]].
  About measurable_fun_cvg.

Lemma mmeas_add (f g : T -> X) (mmf : mu_measurable f) (mmg : mu_measurable g) :
mu_measurable (f + g).
Proof.
  case: mmf=> F aFf; case: mmg=> G aGg. exists (F+G). 
  have cvgD : forall x:T, (F n x @[n --> \oo] --> f x) /\ (G n x @[n --> \oo] --> g x)
  -> (F n x + G n x @[n --> \oo] --> f x + g x) 
  by move=> x [Ffx Ggx]; exact: fun_cvgD.
  by apply: (ae_forall2 cvgD).
Qed.

Lemma mmeas_cvg (f : (T -> X)^nat) (g : T -> X) 
(mmf : forall n:nat, mu_measurable (f n)) (fg : forall x, f ^~ x  @\oo--> g x) : mu_measurable g.
Proof.
  have cvaeu_g : exists (A: (set T)^nat) (F : (T->X)^nat^nat), forall n:nat, 
  (mu (A n) < (1/(n%:R))%:E)%E /\ {uniform [set:T] `\`(A n), F n @\oo--> f n}.
  rewrite /mu_measurable in mmf. have [F P] := choice mmf.
  have Q := forall n:nat, ae_pointwise_almost_uniform (P n). 
  

  


End mu_measurable_function.