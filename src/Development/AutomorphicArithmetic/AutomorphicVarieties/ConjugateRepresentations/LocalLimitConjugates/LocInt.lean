module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemLpLiftL2DiscreteQuotientOnCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

open scoped Pointwise in
theorem UpperTheory.V.Cj.H.locInt :
    UpperTheory.V.Cj.H.LocInt := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _
  refine ⟨fun F => ?_, fun C hC => ?_⟩
  · rw [MeasureTheory.locallyIntegrable_iff]
    intro K hK
    exact (GlobalTheory.AutomorphicL2Local.memLp_restrict_compact G Γ μ F K hK).2
  · have hfin := GlobalTheory.AutomorphicL2Unitary.finite_mem_compact (Γ := Γ) (hC.mul hC.inv)
    refine ⟨hfin.toFinset.card, fun g => ?_⟩
    by_cases hne : {γ : Γ | ↑γ * g ∈ C}.Nonempty
    · obtain ⟨γ0, hγ0⟩ := hne
      calc {γ : Γ | ↑γ * g ∈ C}.encard ≤ {δ : Γ | ↑δ ∈ C * C⁻¹}.encard := by
            apply Set.encard_le_encard_of_injOn (f := fun γ => γ * γ0⁻¹)
            · intro γ hγ
              refine ⟨↑γ * g, hγ, (↑γ0 * g)⁻¹, Set.inv_mem_inv.2 hγ0, ?_⟩
              simp [mul_assoc]
            · intro a _ b _ h
              simpa using h
        _ = hfin.toFinset.card := hfin.encard_eq_coe_toFinset_card
    · rw [Set.not_nonempty_iff_eq_empty.1 hne]
      simp
