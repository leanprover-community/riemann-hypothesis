module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseLevelRowSideTransport
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host
open Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.RealGeo
open scoped TensorProduct

namespace GlobalTheory.Mem.R3.Tr

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B} {a : Late B C} (c : Refill a) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

section Generic

variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {N : Type} [AddCommGroup N] [Module ℂ N] {P P' : Submodule ℂ N}
  {ip : N → N → ℂ} {j : X ≃ₗ[ℂ] P}

theorem hilbTie_ofEq (e : P = P') (h : HilbTie P ip j) : HilbTie P' ip (j.trans (LinearEquiv.ofEq _ _ e)) := fun x y => h x y

theorem projTie_ofEq {Y : Type} {f : Y → X} {g g' : Y → N} (e : P = P') (h : ProjTie P ip j f g) (hg : ∀ y, g' y = g y) :
    ProjTie P' ip (j.trans (LinearEquiv.ofEq _ _ e)) f g' := fun x y => (h x y).trans (congrArg (ip (j x)) (hg y).symm)


omit [NormedAddCommGroup X] [InnerProductSpace ℂ X] in
theorem le_of_eqs {Q Q' : Submodule ℂ N} (e : P = P') (e' : Q = Q') (h : P ≤ Q) : P' ≤ Q' := e ▸ e' ▸ h

theorem val_trans_ofEq (e : P = P') (x : X) : ((j.trans (LinearEquiv.ofEq _ _ e)) x).1 = (j x).1 := rfl

theorem map_incl {Q Q' : Submodule ℂ N} {Z : Type} (e : P = P') (e' : Q = Q') (h : P ≤ Q) (j : X ≃ₗ[ℂ] P) {f : Q → Z} (f' : Q' → Z)
    (hf : ∀ v, f' (LinearEquiv.ofEq _ _ e' v) = f v) (y : X) :
    f' (Submodule.inclusion (le_of_eqs e e' h) ((j.trans (LinearEquiv.ofEq _ _ e)) y)) = f (Submodule.inclusion h (j y)) := by
  subst e e'
  exact hf (Submodule.inclusion h (j y))

omit [NormedAddCommGroup X] [InnerProductSpace ℂ X] in
private theorem mem_of_eq (e : P = P') {w : N} (h : w ∈ P') : w ∈ P := e.symm ▸ h

end Generic

section Chain

variable {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} {R : RealDat a.D A Ks} {F : Face a.D A} {tupT : a.D.what₂.Tup → T}
  {hm : 0 < a.D.R.m} {hTop : TopMultH R}

def stepB (l : Bool) (μ : a.D.what₂.Tup) (k : ℕ) (v : spCC c F tupT hm hTop l μ (k + 1)) : (toChainReal R F tupT hm hTop).Amb k :=
  (by with_unfolding_all exact (((chainB c.to F tupT hm hTop).ioC l ((μ)) k ((v))).1 : _))

theorem stepB_eq (l : Bool) (μ : a.D.what₂.Tup) (k : ℕ) (v : (toChainReal R F tupT hm hTop).CC l μ (k + 1)) :
    stepB c l μ k (LinearEquiv.ofEq _ _ (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) (k + 1)) v) =
      ((toChainReal R F tupT hm hTop).ioC l μ k v).1 := (ioCB_eq c l μ k v)

def topB (l : Bool) (μ : a.D.what₂.Tup) (v : spCCX c F tupT hm hTop l μ) : (toChainReal R F tupT hm hTop).Amb (a.D.R.m - 1) :=
  (by with_unfolding_all exact (((chainB c.to F tupT hm hTop).ioX l ((μ)) ((v))).1 : _))

theorem topB_eq (l : Bool) (μ : a.D.what₂.Tup) (v : (toChainReal R F tupT hm hTop).CCX l μ) :
    topB c l μ (LinearEquiv.ofEq _ _ (congrFun (congrFun (spCCX_eq c F tupT hm hTop) l) μ) v) =
      ((toChainReal R F tupT hm hTop).ioX l μ v).1 := (ioXB'_eq c l μ v)

section Rows

variable {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] {X : RowSide a.D EE} {l : Bool}

def rowIds (I : RowIds X (toChainReal R F tupT hm hTop) l) : RowIds (rowSide c X) (chainB c.to F tupT hm hTop) l :=
  @RowIds.mk c.to.D EE _ _ _ (rowSide c X) (chainB c.to F tupT hm hTop) l
    ((by with_unfolding_all exact ((I.jE.trans (LinearEquiv.ofEq _ _ (congrFun (spEEc_eq c F tupT hm hTop) l))) :)))
    ((by with_unfolding_all exact ((fun (μ : a.D.what₂.Tup) (h : Used0 a.D μ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ a.D.R.m - 1) => (I.jM μ h j h1 h2).trans
      (LinearEquiv.ofEq _ _ (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) j))) :)))
    ((by with_unfolding_all exact ((fun (μ : a.D.what₂.Tup) (h : Used0 a.D μ) => (I.jX μ h).trans
      (LinearEquiv.ofEq _ _ (congrFun (congrFun (spCCXP_eq c F tupT hm hTop) l) μ))) :)))
    ((I.prt))



theorem rowSideReal_tr {I : RowIds X (toChainReal R F tupT hm hTop) l} {n : ℕ} {bs : OrthonormalBasis (Fin n) ℂ EE}
    {ty : Fin n → a.D.what₂.FT} (H : RowSideReal X (toChainReal R F tupT hm hTop) l I bs ty) :
    RowSideReal (rowSide c X) (chainB c.to F tupT hm hTop) l (rowIds c I) bs ((ty)) :=
  set_option backward.isDefEq.lazyProjDelta false in
  set_option backward.isDefEq.lazyWhnfCore false in by
  refine @RowSideReal.mk _ _ _ _ _ _ _ _ _ _ _ _ ?parY ?lvl ?lvlP ?lvlX ?ee ?mult ?multX ?io0 ?io0X ?io ?ioTop ?ft ?prt_disj
  case parY =>
    exact (H.parY)
  case lvl =>
    exact (fun (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) => le_of_eqs (congrFun (spEEc_eq c F tupT hm hTop) l) (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) 0) (H.lvl μ hμ))
  case lvlP =>
    exact (fun (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ a.D.R.m - 1) =>
      le_of_eqs (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) j) (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) j) (H.lvlP μ hμ j h1 h2))
  case lvlX =>
    exact (fun (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) => le_of_eqs (congrFun (congrFun (spCCXP_eq c F tupT hm hTop) l) μ) (congrFun (congrFun (spCCX_eq c F tupT hm hTop) l) μ) (H.lvlX μ hμ))
  case ee =>
    intro x y
    dsimp only [rowIds, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
    with_unfolding_all exact H.ee x y
  case mult =>
    intro μ hμ j h1 h2 x y
    dsimp only [rowIds, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
    with_unfolding_all exact H.mult μ hμ j h1 h2 x y
  case multX =>
    intro h μ hμ x y
    dsimp only [rowIds, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
    with_unfolding_all exact H.multX h μ hμ x y
  case io0 =>
    intro h μ hμ ok x y
    change 2 ≤ a.D.R.m at h
    have hj : 1 ≤ a.D.R.m - 1 := by omega
    have hs := stepB_eq c l μ 0 (Submodule.inclusion (H.lvlP μ hμ 1 le_rfl hj) (I.jM μ hμ 1 le_rfl hj y))
    have ht := (H.io0 h μ hμ (okB_imp c ok) x y).trans
      (congrArg ((toChainReal R F tupT hm hTop).ipE l (I.jE x)) hs.symm)
    with_unfolding_all exact ht
  case io0X =>
    intro h μ hμ ok x y
    change a.D.R.m = 1 at h
    have hj : a.D.R.m - 1 = 0 := by omega
    have hs := topB_eq c l μ
      (Submodule.inclusion (H.lvlX μ hμ) (I.jX μ hμ (cast (congrArg (X.Mult μ) h.symm) y)))
    have ht := (H.io0X h μ hμ (okB_imp c ok) x y).trans
      (congrArg (fun v => (toChainReal R F tupT hm hTop).ipE l (I.jE x)
        (cast (congrArg (toChainReal R F tupT hm hTop).Amb hj) v)) hs.symm)
    with_unfolding_all exact ht
  case io =>
    intro μ hμ ok j h1 h2 x y
    change j + 1 ≤ a.D.R.m - 1 at h2
    have hj : 1 ≤ j + 1 := Nat.succ_pos j
    have hs := stepB_eq c l μ j (Submodule.inclusion (H.lvlP μ hμ (j + 1) hj h2) (I.jM μ hμ (j + 1) hj h2 y))
    have ht := (H.io μ hμ (okB_imp c ok) j h1 h2 x y).trans
      (congrArg ((toChainReal R F tupT hm hTop).ipP l μ j (I.jM μ hμ j h1 (by omega) x)) hs.symm)
    with_unfolding_all exact ht
  case ioTop =>
    intro h μ hμ ok x y
    change 2 ≤ a.D.R.m at h
    have hs := topB_eq c l μ (Submodule.inclusion (H.lvlX μ hμ) (I.jX μ hμ y))
    have ht := (H.ioTop h μ hμ (okB_imp c ok) x y).trans
      (congrArg ((toChainReal R F tupT hm hTop).ipP l μ (a.D.R.m - 1) (I.jM μ hμ _ (by omega) le_rfl x)) hs.symm)
    with_unfolding_all exact ht
  case ft =>
    intro σ
    with_unfolding_all exact H.ft σ
  case prt_disj =>
    exact (H.prt_disj)

end Rows

variable {hinj : ∀ i t, Function.Injective (R.extV i t)}


variable (F tupT hm hTop hinj) in
def spWc : type_of% (toLiftReal R F tupT hm hTop hinj).Wc := ((liftB c.to F tupT hm hTop hinj).Wc)


variable (F tupT hm hTop hinj) in
theorem spWc_eq : (toLiftReal R F tupT hm hTop hinj).Wc = spWc c F tupT hm hTop hinj := (lift_Wc c.to F tupT hm hTop hinj)


variable (F tupT hm hTop hinj) in
def spMultW : type_of% (toLiftReal R F tupT hm hTop hinj).MultW := ((liftB c.to F tupT hm hTop hinj).MultW)


variable (F tupT hm hTop hinj) in
theorem spMultW_eq : (toLiftReal R F tupT hm hTop hinj).MultW = spMultW c F tupT hm hTop hinj := (lift_MultW c.to F tupT hm hTop hinj)

def liftIds (I : LiftIds (toLiftReal R F tupT hm hTop hinj)) : LiftIds (liftB c.to F tupT hm hTop hinj) :=
  @LiftIds.mk c.to.D (chainB c.to F tupT hm hTop) (liftB c.to F tupT hm hTop hinj)
    ((by with_unfolding_all exact ((fun i : Fin a.D.R.m => (I.jMj i).trans (LinearEquiv.ofEq _ _ (congrFun (spWc_eq c F tupT hm hTop hinj) i))) :)))
    ((I.jMt)) ((I.prtW))

theorem liftTie_tr {I : LiftIds (toLiftReal R F tupT hm hTop hinj)} (H : LiftTie (toLiftReal R F tupT hm hTop hinj) I) :
    LiftTie (liftB c.to F tupT hm hTop hinj) (liftIds c I) :=
  set_option backward.isDefEq.lazyProjDelta false in
  set_option backward.isDefEq.lazyWhnfCore false in by
  refine @LiftTie.mk _ _ _ _ ?hol ?mj ?mt ?theta ?isot ?prtW_disj ?lamP
  case hol => exact H.hol
  case mj =>
    intro i x y
    dsimp only [liftIds, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
    with_unfolding_all exact H.mj i x y
  case mt => exact H.mt
  case theta =>
    intro μ hμ i x w hTheta hMult hEmb hWc
    have hMult' := mem_of_eq (congrFun (spMultW_eq c F tupT hm hTop hinj) i) hMult
    have hWc' := mem_of_eq (congrFun (spWc_eq c F tupT hm hTop hinj) i) hWc
    dsimp only [liftIds, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
    with_unfolding_all
      refine H.theta μ hμ i x w ?_ hMult' ?_ hWc'
      · dsimp only [liftB, toLiftReal, real] at hTheta ⊢
        exact hTheta
      · dsimp only [liftB, toLiftReal, liftIds, real] at hEmb ⊢
        exact hEmb
  case isot =>
    intro i π y
    with_unfolding_all exact H.isot i π y
  case prtW_disj => exact H.prtW_disj
  case lamP => exact H.lamP

theorem recTied_tr {X0 : BaseLevelRowSide a.D} {Ish : RowIds (RowSide.sharp a.D) (toChainReal R F tupT hm hTop) true}
    {Iz : RowIds X0.s (toChainReal R F tupT hm hTop) false} {IL : LiftIds (toLiftReal R F tupT hm hTop hinj)} {K : ColReal a.D}
    (H : RecTied a.D X0 (toChainReal R F tupT hm hTop) Ish Iz (toLiftReal R F tupT hm hTop hinj) IL K) :
    RecTied c.to.D (baseLevelRowSideTransport c X0) (chainB c.to F tupT hm hTop) ((rowIds c Ish)) ((by with_unfolding_all exact @rowIds B C a c G ‹Group G› ‹Fintype G› Pl0 T Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK A R F tupT hm hTop (@Rows.Data.EE0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0i (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0f (@Late.D B C a).R (@Late.D B C a).what₂) (@BaseLevelRowSide.s (@Late.D B C a) X0) false Iz)) (liftB c.to F tupT hm hTop hinj)
      (liftIds c IL) (colReal c K) :=
  @RecTied.mk _ _ _ _ _ _ _ _ ((rowSideReal_tr c H.sharp)) ((by with_unfolding_all exact @rowSideReal_tr B C a c G ‹Group G› ‹Fintype G› Pl0 T Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK A R F tupT hm hTop (@Rows.Data.EE0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0i (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0f (@Late.D B C a).R (@Late.D B C a).what₂) (@BaseLevelRowSide.s (@Late.D B C a) X0) false Iz (@Rows.Data.D0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.onb0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.ft0 (@Late.D B C a).R (@Late.D B C a).what₂) (@RecTied.base (@Late.D B C a) X0 (@toChainReal (@Late.D B C a) G ‹Group G› ‹Fintype G› Pl0 T A Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK R F tupT hm hTop) Ish Iz (@toLiftReal (@Late.D B C a) G ‹Group G› ‹Fintype G› Pl0 T A Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK R F tupT hm hTop hinj) IL K H))) (liftTie_tr c H.lift)
    (@ColTieR.mk _ _ _ ((H.col.tup)) ((H.col.xi0)) ((H.col.bu)))

def mjTie (x : MjTie R F) : @MjTie c.to.D G _ _ Pl0 T (famM c.to A) Ks _ _ (alg c.to iK) (real c.to R) (face c.to F) :=
  @MjTie.mk c.to.D G _ _ Pl0 T (famM c.to A) Ks _ _ (alg c.to iK) (real c.to R) (face c.to F) ((x.eW))
    ((by with_unfolding_all exact ((cast (congrArg (fun W : type_of% R.Wat => ∀ i, LinearMap.range (x.eW i) =
      (W i (sg0 a.D A) (R.levL F false (sg0 a.D A))).comap (R.HW i (sg0 a.D A)).e) (wat_eq c.to R)) x.eW_range) :)))
    ((x.eW_norm)) ((x.eW_lat))

end Chain

end GlobalTheory.Mem.R3.Tr

end
