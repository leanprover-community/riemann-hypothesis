module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
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

@[expose] public section

namespace GlobalTheory.CoefficientSpanFiniteDimensional

theorem dual_apply_eq_sum {W ι : Type} [AddCommGroup W] [Module ℂ W] [Fintype ι] (b : Module.Basis ι ℂ W)
    (ℓ : Module.Dual ℂ W) (w : W) (A : W →ₗ[ℂ] W) :
    ℓ (A w) = ∑ j, ∑ i, (b.repr w j * ℓ (b i)) * b.repr (A (b j)) i := by
  conv_lhs => rw [← b.sum_repr w]

  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_smul]
  conv_lhs => rw [← b.sum_repr (A (b j))]

  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, smul_eq_mul]
  ring

theorem finiteDimensional_coeffSpan {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ ↥(GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  classical
  let b := Module.finBasis ℂ W
  let e : Fin (Module.finrank ℂ W) × Fin (Module.finrank ℂ W) → (K → ℂ) :=
    fun p k => b.repr (ρ k (b p.2)) p.1
  haveI : FiniteDimensional ℂ ↥(Submodule.span ℂ (Set.range e)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range e)
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range e)) (Submodule.span_le.mpr ?_)
  rintro f ⟨ℓ, w, rfl⟩
  have h : (fun k => ℓ (ρ k w)) = ∑ j, ∑ i, (b.repr w j * ℓ (b i)) • e (i, j) := by
    funext k
    rw [dual_apply_eq_sum b ℓ w (ρ k)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, e]
  rw [h]
  exact Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)

end GlobalTheory.CoefficientSpanFiniteDimensional
