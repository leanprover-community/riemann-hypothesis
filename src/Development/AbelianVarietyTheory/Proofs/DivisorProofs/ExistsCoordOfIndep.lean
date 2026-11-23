module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily

@[expose] public section

open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links

set_option autoImplicit false

noncomputable section




namespace GlobalTheory.BigOn.Exp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_coord_of_indep {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    (e : K →+* ℂ) (rd : V →ₛₗ[e] W)
    (hF : ∀ (n : ℕ) (v : Fin n → V), LinearIndependent K v → LinearIndependent ℂ fun c => rd (v c))
    {μ : ℂ} {f f' : V} (hf : f ≠ 0) (h : rd f' = μ • rd f) : ∃ u : K, e u = μ := by
  have hrf : rd f ≠ 0 := (hF 1 (fun _ => f) (linearIndependent_unique_iff.2 hf)).ne_zero 0
  by_cases hli : LinearIndependent K ![f, f']
  · have h2 := hF 2 _ hli
    have h2' : LinearIndependent ℂ ![rd f, rd f'] := by
      convert h2 using 1
      funext c
      fin_cases c <;> rfl
    have := (LinearIndependent.pair_iff.1 h2') (-μ) 1 (by rw [h, one_smul, neg_smul, neg_add_cancel])
    exact absurd this.2 one_ne_zero
  · rw [LinearIndependent.pair_iff] at hli
    push_neg at hli
    obtain ⟨s, t, hst, hne⟩ := hli
    have ht : t ≠ 0 := by
      intro ht0
      rw [ht0, zero_smul, add_zero] at hst
      exact hne ((smul_eq_zero.1 hst).resolve_right hf) ht0
    have hf' : f' = (-(s / t)) • f := by
      have : t • f' = -(s • f) := eq_neg_of_add_eq_zero_right hst
      calc f' = t⁻¹ • (t • f') := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = _ := by rw [this, smul_neg, smul_smul, ← neg_smul, div_eq_inv_mul]
    refine ⟨-(s / t), ?_⟩
    have h3 : e (-(s / t)) • rd f = μ • rd f := by rw [← h, hf', map_smulₛₗ]
    exact smul_left_injective ℂ hrf h3

end GlobalTheory.BigOn.Exp
