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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtDegConst_of :
    PtEx → WtDegConst := by
  intro _ Z S p _ _ w hw
  obtain ⟨ψ, hψ, hsum⟩ := hw (Sq.self p) (fun _ => 1) (IsLocallyConstant.const 1)
  have hψ' : IsLocallyConstant (fun s : S => ψ s) := hψ
  by_cases hS : Nonempty S
  · obtain ⟨s₀⟩ := hS
    refine ⟨ψ s₀, ?_⟩
    funext Ω _ _ x
    have h : ψ (pt x) = ∑ᶠ (z : gp Ω ⟶ Z) (_ : z ∈ fib p x), w Ω (z ≫ 𝟙 Z) * 1 := hsum Ω x
    simp only [Category.comp_id, mul_one] at h
    show (∑ᶠ (z : gp Ω ⟶ Z) (_ : z ∈ fib p x), w Ω z) = ψ s₀
    have hc : ψ (pt x) = ψ s₀ := hψ'.apply_eq_of_preconnectedSpace (pt x) s₀
    rw [← hc]
    exact h.symm
  · refine ⟨0, ?_⟩
    funext Ω _ _ x
    exact (hS ⟨pt x⟩).elim
