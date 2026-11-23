module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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

@[expose] public section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem riemLat_basis_periods_linearIndependent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (n : ℕ) (b : Module.Basis (Fin n) ℤ Λ), LinearIndependent ℝ (fun j => R.P (b j)) := by
  intro E _ _ _ g Λ _ _ R n b
  have hspan : Submodule.span ℝ (Set.range R.P) = ⊤ := (GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R).2.1
  have hmem : ∀ x : Λ, R.P x ∈ Submodule.span ℝ (Set.range fun j => R.P (b j)) := by
    intro x
    have hx : x ∈ Submodule.span ℤ (Set.range b) := by
      rw [b.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact Submodule.subset_span ⟨j, rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      rw [map_zsmul]
      exact Submodule.smul_of_tower_mem _ c hy
  have htop : ⊤ ≤ Submodule.span ℝ (Set.range fun j => R.P (b j)) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact hmem x
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (Fin g → ℂ) := by
    have h1 : Module.finrank ℤ Λ = Fintype.card (Fin n) := by
      haveI := R.free
      haveI := R.fin
      exact Module.finrank_eq_card_basis b
    have h2 : Module.finrank ℝ (Fin g → ℂ) = 2 * g := by
      simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
    rw [← h1, R.rank, h2]
  exact linearIndependent_of_top_le_span_of_card_eq_finrank htop hcard

end GlobalTheory.CompanionTheory.Ar.Cusp
