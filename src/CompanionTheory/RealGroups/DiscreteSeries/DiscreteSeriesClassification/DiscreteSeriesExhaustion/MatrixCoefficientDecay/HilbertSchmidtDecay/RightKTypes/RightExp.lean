module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.RightKTypes.CoefFam
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace CompanionTheory.RgExh.Dec.L.WyKR

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem rightExp {ε : Fin n → Bool} {X : GMod n} (A : KAct ε X) (x : X.V) :
    ∃ (r : ℕ) (w : Fin r → X.V) (a : Fin r → S7.KG ε → ℂ) (B : ℝ), (∀ l k, ‖a l k‖ ≤ B) ∧
      ∀ k, A.ρ k x = ∑ l, a l k • w l := by
  obtain ⟨W, hW, hmem⟩ := A.fin x
  obtain ⟨C, hC⟩ := A.bdd
  let b := Module.finBasis ℂ W
  let embW : W →ₗ[ℂ] A.N := A.emb ∘ₗ W.subtype
  have hinj : Function.Injective embW := A.inj.comp Subtype.val_injective
  let e : W ≃ₗ[ℂ] LinearMap.range embW := LinearEquiv.ofInjective embW hinj
  have : FiniteDimensional ℂ (LinearMap.range embW) := LinearMap.finiteDimensional_range embW
  let ψ : Fin (Module.finrank ℂ W) → (LinearMap.range embW →L[ℂ] ℂ) :=
    fun l => LinearMap.toContinuousLinearMap ((b.coord l) ∘ₗ e.symm.toLinearMap)
  refine ⟨Module.finrank ℂ W, fun l => (b l : X.V), fun l k => b.repr ⟨A.ρ k x, hmem k⟩ l,
    ∑ l, ‖ψ l‖ * (|C| * ‖A.emb x‖), fun l k => ?_, fun k => ?_⟩
  · have h1 : b.repr ⟨A.ρ k x, hmem k⟩ l = ψ l (e ⟨A.ρ k x, hmem k⟩) := by
      simp [ψ]
    show ‖b.repr ⟨A.ρ k x, hmem k⟩ l‖ ≤ _
    rw [h1]
    have h2 : ‖e ⟨A.ρ k x, hmem k⟩‖ = ‖A.emb (A.ρ k x)‖ := rfl
    calc ‖ψ l (e ⟨A.ρ k x, hmem k⟩)‖ ≤ ‖ψ l‖ * ‖e ⟨A.ρ k x, hmem k⟩‖ := (ψ l).le_opNorm _
      _ ≤ ‖ψ l‖ * (|C| * ‖A.emb x‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [h2]
          exact (hC k x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))
      _ ≤ _ := Finset.single_le_sum (f := fun l => ‖ψ l‖ * (|C| * ‖A.emb x‖))
          (fun l _ => by positivity) (Finset.mem_univ l)
  · have h3 := congrArg Subtype.val (b.sum_repr ⟨A.ρ k x, hmem k⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h3
    exact h3.symm

end CompanionTheory.RgExh.Dec.L.WyKR
