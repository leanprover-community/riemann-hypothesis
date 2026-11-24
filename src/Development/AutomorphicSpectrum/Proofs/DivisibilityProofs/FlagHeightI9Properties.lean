module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HasBaseDegreeSetting
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightPolynomialEvalStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightPowerSumOneZeroStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyBoundaryDimensionDropStatement
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem flag_gap_eq_sub {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (lam : Wt Ψ N) (τ : Ψ) (a : Fin N)
    (h : (a : ℕ) + 1 < N) :
    PB.gap (fun x : Ψ × Fin N => lam x.1 x.2) (τ, a) = lam τ a - lam τ ⟨(a : ℕ) + 1, h⟩ := by
  simp [PB.gap, PB.gapX, h]

theorem flag_dim_eq_antisymmetric_degree (Ψ : Type) [Fintype Ψ] (N : ℕ) :
    dimFl Ψ N = GroundTheory.Heights₂.Heights.antisymDegree Ψ N := by
  simp [dimFl, GroundTheory.Heights₂.Heights.antisymDegree, Nat.choose_two_right]

theorem flag_height_I9 : PB.FlagHeight → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ], 2 ≤ N →
      I9 (Ψ := Ψ) (N := N) (hhFl Ψ N II) := by
  intro hFH hIn II hII Ψ _ _ N _ hN
  have hA : IsArithVar (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1) := by
    rw [flag_dim_eq_antisymmetric_degree]
    exact (GlobalTheory.T.flag_variety_boundary_dimension_drop Ψ N hN).1
  have hev : ∀ lam : Wt Ψ N, hhFl Ψ N II (linRoot lam ^ (dimFl Ψ N + 1)) =
      eval (fun x => lam x.1 x.2) (PB.hFlPoly Ψ N II) := fun lam =>
    GlobalTheory.T.flag_height_polynomial_eval II hII Ψ N lam hN hA
  obtain ⟨-, hgap, hdom⟩ := hFH hIn II hII Ψ N hN
  refine ⟨?_, ?_, ?_⟩
  · rintro lam - ⟨τ, a, b, hab, heq⟩
    have h : (a : ℕ) + 1 < N := hab ▸ b.2
    have hb : b = ⟨(a : ℕ) + 1, h⟩ := Fin.ext hab
    rw [hev]
    refine hgap _ (τ, a) h ?_
    rw [flag_gap_eq_sub lam τ a h, ← hb, heq, sub_self]
  · intro lam hlam
    rw [hev]
    refine hdom _ fun p hp => ?_
    obtain ⟨τ, a⟩ := p
    rw [flag_gap_eq_sub lam τ a hp, sub_nonneg]
    exact hlam τ a ⟨(a : ℕ) + 1, hp⟩ (Fin.le_def.2 (Nat.le_succ _))
  · intro τ Q hQ
    exact GlobalTheory.T.flag_height_power_sum_one_zero II hII Ψ N τ Q hN hA hQ

end GlobalTheory.CompanionTheory.Ar.Top
