module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.countEx_of :
    CountEx := by
  classical
  intro T Z S p π ι σ m hsym
  refine ⟨fun Ω _ _ z => if h : ∃ x : gp Ω ⟶ T, z ≫ p = x ≫ π then
      ∑ᶠ (j : ι) (_ : j ∈ {j | h.choose ≫ σ j = z}), m j else 0, ?_⟩
  intro Ω _ _ x z hz
  have hex : ∃ x : gp Ω ⟶ T, z ≫ p = x ≫ π := ⟨x, hz⟩
  simp only [dif_pos hex]
  set x₀ := hex.choose with hx₀
  have h₀ : z ≫ p = x₀ ≫ π := hex.choose_spec
  obtain ⟨e, he⟩ := hsym Ω x x₀ (hz.symm.trans h₀)
  symm
  apply finsum_mem_eq_of_bijOn e
  · refine ⟨?_, ?_, ?_⟩
    · intro j hj
      simp only [Set.mem_setOf_eq] at hj ⊢
      rw [← (he j).1, hj]
    · intro a _ b _ hab
      exact e.injective hab
    · intro k hk
      simp only [Set.mem_setOf_eq] at hk
      refine ⟨e.symm k, ?_, by simp⟩
      simp only [Set.mem_setOf_eq]
      rw [(he (e.symm k)).1, Equiv.apply_symm_apply, hk]
  · intro j _
    exact ((he j).2).symm
