module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.IsFirstChernThickening
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.FirstChernRationalLift

variable {K B' : Type} [Field K] [CharZero K] [CommRing B'] [Algebra K B'] {I : Ideal B'} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of K)) (s : ℕ)

abbrev famK {C : Type 1} [Category.{0} C] (G : C ⥤ (TS γ q 1 s {⊤}).FullSubcategory) : C ⥤ Thick (smFun X q) :=
  G ⋙ (smO γ q 1 s {⊤}).G ⋙ (TO q 1 s {⊤}).ι

theorem pt_famK {C : Type 1} [Category.{0} C] (G : C ⥤ (TS γ q 1 s {⊤}).FullSubcategory) (c : C) :
    pt ((famK γ q s G).obj c) = pt (G.obj c).obj := Category.comp_id _

def liftK {C : Type 1} [Category.{0} C] {G : C ⥤ (TS γ q 1 s {⊤}).FullSubcategory} {D : E.LineData X}
    (Λ : B.CLift (q := q) (b := nlBase B' I γ 0) (ht := rfl) (κ := κA K I) (G ⋙ (TS γ q 1 s {⊤}).ι) D) :
    CLiftK (famK γ q s G) D where
  p c := Λ.p c
  hp c := (Λ.hp c).trans (Category.comp_id _).symm
  w φ := Λ.w φ
  hw φ h := Λ.hw φ h

theorem isFirstChernThickening_muB_of_isFirstChernDeRham (D : E.LineData X) (c : HdR q 2)
    (h : IsFirstChernDeRham (q := q) D c) :
    IsFirstChernThickening (TS γ q 1 s {⊤}) D s (muB γ q 1 s {⊤} 2 c) := by
  intro C _ G hG Λ
  have hpd : ∀ c', ((famK γ q s G).obj c').pdPow s = ⊥ := fun c' => ((smO γ q 1 s {⊤}).G.obj (G.obj c')).property.1.1
  have hV : ∀ c', ∃ (V : X.Opens) (σ : (V : Scheme.{0}) ⟶ D.Y), σ ≫ D.f = V.ι ∧ InU V ((famK γ q s G).obj c') := by
    intro c'
    obtain ⟨V, ⟨σ, hσ⟩, hU⟩ := hG c'
    refine ⟨V, σ, hσ, ?_⟩
    unfold InU
    rw [pt_famK]
    exact hU
  obtain ⟨z, hz, hzv, hcls⟩ := h s C (famK γ q s G) hpd hV (liftK γ q s Λ)
  let m' : CH.Mor (famK γ q s G ⋙ O (smFun X q)) (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) (algebraMap K B') :=
    ⟨𝟭 _, fun T => (smO γ q 1 s {⊤}).o.τ (G.obj T), fun φ x => (smO γ q 1 s {⊤}).o.nat (G.map φ) x⟩
  have e : (show CH.Cn (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2 from Λ.coc (RingHom.id _) s) = m'.pullC 2 z := by
    funext σ
    exact (hzv σ).symm
  have hb : CH.d (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2 (m'.pullC 2 z) = 0 := by
    rw [m'.d_pullC, hz, map_zero]
  have hz' : CH.d (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2 (Λ.coc (RingHom.id _) s) = 0 := (congrArg (CH.d (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2) e).trans hb
  refine ⟨hz', ?_⟩
  have e1 := CrystallineSemistableComparison.P.mapH_cls m'.hom 2 z hz hb
  have e2 : (CH.Mor.restrict (CH.modF (sP (TS γ q 1 s {⊤})).A) G).pull 2 (muB γ q 1 s {⊤} 2 c) =
      m'.pull 2 ((CH.Mor.restrict (O (smFun X q)) (famK γ q s G)).pull 2 c) := by
    have a1 := (CrystallineSemistableComparison.P.pull_comp (CH.Mor.restrict (O (smFun X q)) (TO q 1 s {⊤}).ι) (smO γ q 1 s {⊤}).o 2 c).1
    have a2 := (CrystallineSemistableComparison.P.pull_comp ((CH.Mor.restrict (O (smFun X q)) (TO q 1 s {⊤}).ι).comp (smO γ q 1 s {⊤}).o)
      (CH.Mor.restrict (CH.modF (sP (TS γ q 1 s {⊤})).A) G) 2 c).1
    have b := (CrystallineSemistableComparison.P.pull_comp (CH.Mor.restrict (O (smFun X q)) (famK γ q s G)) m' 2 c).1
    exact (congrArg ((CH.Mor.restrict (CH.modF (sP (TS γ q 1 s {⊤})).A) G).pull 2) a1.symm).trans (a2.symm.trans b)
  rw [e2, ← hcls]
  refine Eq.trans ?_ e1.symm
  have key : ∀ (a : CH.Cn (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2) (ha : CH.d (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2 a = 0),
      a = m'.pullC 2 z → (CH.cx (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A)).cls a ha =
        (CH.cx (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A)).cls (m'.pullC 2 z) hb := by
    rintro _ _ rfl
    rfl
  exact key _ hz' e

end GlobalTheory.CompanionTheory.FirstChernRationalLift
