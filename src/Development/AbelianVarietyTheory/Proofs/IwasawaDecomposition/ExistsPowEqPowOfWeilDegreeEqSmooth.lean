module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne


open NumberField IsDedekindDomain Polynomial Module in
theorem _root_.GlobalTheory.WeilDeligne.exists_pow_eq_pow_of_deg_eq : ∀ (E Ω : Type) [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ (_root_.GlobalTheory.WeilDeligne.Weil h) V),
    _root_.GlobalTheory.WeilDeligne.IsSmooth ρ → ∀ σ τ : _root_.GlobalTheory.WeilDeligne.Weil h, _root_.GlobalTheory.WeilDeligne.deg σ = _root_.GlobalTheory.WeilDeligne.deg τ →
      ∃ m : ℕ, 0 < m ∧ ρ σ ^ m = ρ τ ^ m := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ ρ hρ σ τ hdeg
  let x : ℕ → _root_.GlobalTheory.WeilDeligne.Weil h := fun k ↦ (τ ^ k)⁻¹ * σ ^ k
  have hmem : ∀ k, ρ (x k) ∈ Set.range fun ι ↦ ρ (_root_.GlobalTheory.WeilDeligne.ineIncl h ι) := by
    intro k
    have h0 : _root_.GlobalTheory.WeilDeligne.deg (x k) = 0 := by
      simp only [x, _root_.GlobalTheory.WeilDeligne.deg_mul, _root_.GlobalTheory.WeilDeligne.deg_inv, _root_.GlobalTheory.WeilDeligne.deg_pow, hdeg]
      ring
    refine ⟨⟨_, _root_.GlobalTheory.WeilDeligne.deg_eq_zero_iff.mp h0⟩, ?_⟩
    simp only
    congr 1
  obtain ⟨k, l, hkl, hρkl⟩ :=
    Set.Finite.exists_lt_map_eq_of_forall_mem hmem hρ.finite_range
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hkl
  have hx : ρ (x k) = ρ (x (k + m + 1)) := hρkl
  refine ⟨m + 1, Nat.succ_pos m, ?_⟩
  have key : σ ^ (m + 1) = τ ^ (k + m + 1) * x (k + m + 1) * (x k)⁻¹ * (τ ^ k)⁻¹ := by
    simp only [x]
    group
  have key' : τ ^ (m + 1) = τ ^ (k + m + 1) * (τ ^ k)⁻¹ := by
    group
  have hinv : ρ (x k) * ρ (x k)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  rw [← map_pow, ← map_pow, key, key']
  simp only [map_mul]
  rw [← hx, mul_assoc (ρ _) (ρ (x k)), hinv, mul_one]

end GlobalTheory.WeilDeligne
