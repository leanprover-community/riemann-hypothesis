module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothA

@[expose] public section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Exists

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem exists_smoothDerived (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    ∃ (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D),
      (∀ v : H, v ∈ D ↔ IsSmoothVecU ε σ v) ∧
      (IsURepOn (UJset ε) σ →
        (∀ (v : D) (a b : Fin n), ((E a b v : D) : H) =
          dS σ (S7.cpart1 ε (Matrix.single a b 1)) v +
            Complex.I • dS σ (S7.cpart2 ε (Matrix.single a b 1)) v) ∧
        IsDerivedOn ε σ D E) := by
  classical
  let D := SmDerA.smSub (ε := ε) (σ := σ)
  by_cases hσ : IsURepOn (UJset ε) σ
  · refine ⟨D, fun a b => SmDerA.EcL hσ (Matrix.single a b 1), fun v => Iff.rfl,
      fun _ => ⟨?_, ?_⟩⟩
    · intro v a b
      show ((SmDerA.EcL hσ (Matrix.single a b 1) v : D) : H) = _
      rw [SmDerA.EcL_apply, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add,
        Submodule.coe_smul, SmDerA.Tm_apply hσ (SmDerA.inG_cpart1 ε _),
        SmDerA.Tm_apply hσ (SmDerA.inG_cpart2 ε _)]
    · refine ⟨SmDerA.EcL_glRep hσ, fun k hk v hv => IsSmoothVecU.kStable hσ hk hv, fun X hX v => ?_⟩
      rw [SmDerA.actM_EcL hσ X, SmDerA.EcL_inG hσ hX, SmDerA.Tm_apply hσ hX]
      exact hasDerivAt_dS hσ hX v.2
  · exact ⟨D, fun _ _ => 0, fun v => Iff.rfl, fun h => absurd h hσ⟩

def smD (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ H :=
  (exists_smoothDerived ε σ).choose

def smE (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    Fin n → Fin n → Module.End ℂ (smD ε σ) :=
  (exists_smoothDerived ε σ).choose_spec.choose

theorem mem_smD_iff (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) :
    v ∈ smD ε σ ↔ IsSmoothVecU ε σ v :=
  (exists_smoothDerived ε σ).choose_spec.choose_spec.1 v

theorem smE_apply {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) (v : smD ε σ) (a b : Fin n) :
    ((smE ε σ a b v : smD ε σ) : H) =
      dS σ (S7.cpart1 ε (Matrix.single a b 1)) v +
        Complex.I • dS σ (S7.cpart2 ε (Matrix.single a b 1)) v :=
  ((exists_smoothDerived ε σ).choose_spec.choose_spec.2 hσ).1 v a b

theorem isDerivedOn_smE {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) : IsDerivedOn ε σ (smD ε σ) (smE ε σ) :=
  ((exists_smoothDerived ε σ).choose_spec.choose_spec.2 hσ).2

end Exists

section Derived

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem dS_eq_actM (hD : IsDerivedOn ε σ D E) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v : D) :
    dS σ X v = ((actM E X v : D) : H) := by
  simpa only [dS] using (hD.deriv X hX v).deriv

theorem casU_eq_casimir (hD : IsDerivedOn ε σ D E) (v : D) :
    casU ε σ v = ((casimir E v : D) : H) := by
  have h1 : ∀ p, dS σ (casGen ε p) (dS σ (casGen ε p) (v : H)) =
      ((actM E (casGen ε p) (actM E (casGen ε p) v) : D) : H) := by
    intro p
    rw [dS_eq_actM hD (SmDerA.inG_casGen ε p) v, dS_eq_actM hD (SmDerA.inG_casGen ε p)]
  simp only [casU, h1]
  rw [SmDerA.casimir_eq E ε]
  rw [LinearMap.neg_apply, Submodule.coe_neg, LinearMap.sum_apply, Submodule.coe_sum]
  simp only [LinearMap.smul_apply, Submodule.coe_smul, Module.End.mul_apply]

end Derived

end ReciprocityTheory.ChartRestriction.DS
