module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemSpanRatPolysVanishingOfAutStableStatement
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_component_mem_vanI_of_mem_span {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ))
    (l : ℂ →ₗ[ℚ] ℚ) (f : MvPolynomial (ι × ι) ℂ)
    (hf : f ∈ Submodule.span ℂ ((MvPolynomial.map (algebraMap ℚ ℂ)) '' vanI Γ)) :
    ∀ c : ℂ, ∃ f' ∈ vanI Γ, ∀ m, AddMonoidAlgebra.coeff f' m = l (c * AddMonoidAlgebra.coeff f m) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    intro c
    have hvan : l c • p ∈ vanI Γ := by
      show ∀ g ∈ Γ, ev (l c • p) g = 0
      intro g hg
      have h0 : ev p g = 0 := hp g hg
      simp only [ev] at h0 ⊢
      rw [map_smul, h0, smul_zero]
    refine ⟨l c • p, hvan, fun m => ?_⟩
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul, mul_comm c,
      ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  | zero =>
    intro c
    have hvan : (0 : MvPolynomial (ι × ι) ℚ) ∈ vanI Γ := by
      show ∀ g ∈ Γ, ev (0 : MvPolynomial (ι × ι) ℚ) g = 0
      intro g _
      simp [ev]
    exact ⟨0, hvan, fun m => by simp⟩
  | add x y _ _ hx hy =>
    intro c
    obtain ⟨a, ha, ha'⟩ := hx c
    obtain ⟨b, hb, hb'⟩ := hy c
    have hvan : a + b ∈ vanI Γ := by
      show ∀ g ∈ Γ, ev (a + b) g = 0
      intro g hg
      have h1 : ev a g = 0 := ha g hg
      have h2 : ev b g = 0 := hb g hg
      simp only [ev] at h1 h2 ⊢
      rw [map_add (f := _), h1, h2, add_zero]
    refine ⟨a + b, hvan, fun m => ?_⟩
    rw [MvPolynomial.coeff_add, ha', hb', MvPolynomial.coeff_add, mul_add, map_add (f := _)]
  | smul a x _ hx =>
    intro c
    obtain ⟨f', hf', h'⟩ := hx (c * a)
    exact ⟨f', hf', fun m => by rw [h', MvPolynomial.coeff_smul, smul_eq_mul, mul_assoc]⟩

theorem component_mem_vanI : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ g ∈ Γ, evC f g = 0) → ∀ (l : ℂ →ₗ[ℚ] ℚ) (f' : MvPolynomial (ι × ι) ℚ), (∀ m, AddMonoidAlgebra.coeff f' m = l (AddMonoidAlgebra.coeff f m)) → f' ∈ vanI Γ := by
  intro ι _ _ Γ hΓ f hf l f' hf'
  obtain ⟨p, hp, hpc⟩ :=
    exists_component_mem_vanI_of_mem_span Γ l f (GlobalTheory.T.mem_span_ratPolysVanishing_of_autStable ι Γ hΓ f hf) 1
  have hfp : f' = p := by
    ext m
    rw [hf', hpc, one_mul]
  exact hfp ▸ hp

end GlobalTheory.ClassFin
