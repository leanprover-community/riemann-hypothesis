module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableComb

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

namespace GlobalTheory.GalTheta

theorem exists_top_embedding_eq_on_countable (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (S : Set ℂ)
    (hS : S.Countable) :
    ∃ σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ, ∀ x ∈ S, x ∈ M → cj ⊤ σ x = cj M ρ x := by
  let A : Set M := {y | (y : ℂ) ∈ S}
  have hA : A.Countable := hS.preimage Subtype.val_injective
  let k : Subfield M := Subfield.closure A
  haveI : Countable k := by
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (Subfield.cardinalMk_closure_le_max A).trans (max_le ?_ le_rfl)
    exact Cardinal.mk_le_aleph0_iff.2 hA.to_subtype
  obtain ⟨τ, hτ⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq (K := k)
    ((M.val : M →+* ℂ).comp k.subtype) ((ρ : M →+* ℂ).comp k.subtype)
  refine ⟨(τ.toRingHom.toRatAlgHom).comp (⊤ : IntermediateField ℚ ℂ).val, fun x hx hxM => ?_⟩
  have h := hτ ⟨⟨x, hxM⟩, Subfield.subset_closure hx⟩
  have h1 : liftM ⊤ x = ⟨x, IntermediateField.mem_top⟩ := dif_pos IntermediateField.mem_top
  have h2 : liftM M x = ⟨x, hxM⟩ := dif_pos hxM
  unfold cj
  rw [h1, h2]
  exact h

end GlobalTheory.GalTheta
