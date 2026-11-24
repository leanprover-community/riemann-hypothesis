module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

private theorem qdet2 {A : Type} [Ring A] [Algebra ℂ A] (E : Fin 2 → Fin 2 → A) (u : ℂ) :
    Formalism.REAL.qdet E u = (algebraMap ℂ A u + E 0 0) * (algebraMap ℂ A (u - 1) + E 1 1) - E 1 0 * E 0 1 := by
  have h : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  rw [Formalism.REAL.qdet, Formalism.REAL.qminor, h, Finset.sum_pair (by decide)]
  simp [Formalism.REAL.Tm, List.ofFn_succ, sub_eq_add_neg]

private theorem cap2 {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin 2 → Fin 2 → Module.End ℂ V)
    (hE : Formalism.REAL.GlRel E) (a b : ℂ) (φ : V)
    (h : ∀ u : ℂ, Formalism.REAL.qdet E (u + 1 / 2) φ = ((u + a) * (u + b)) • φ) :
    E 0 0 φ + E 1 1 φ = (a + b) • φ ∧
      E 0 0 (E 0 0 φ) + E 0 1 (E 1 0 φ) + E 1 0 (E 0 1 φ) + E 1 1 (E 1 1 φ) = (a ^ 2 + b ^ 2 - 1 / 2) • φ := by
  have h0 := h 0
  have h1 := h 1
  rw [qdet2] at h0 h1
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, Module.algebraMap_end_apply, map_add (f := _),
    map_smul] at h0 h1
  have hs : E 0 0 φ + E 1 1 φ = (a + b) • φ := by
    linear_combination (norm := module) h1 - h0
  have r1 : E 0 0 (E 1 1 φ) - E 1 1 (E 0 0 φ) = 0 := by
    simpa using LinearMap.congr_fun (hE 0 0 1 1) φ
  have r2 : E 0 1 (E 1 0 φ) - E 1 0 (E 0 1 φ) = E 0 0 φ - E 1 1 φ := by
    simpa using LinearMap.congr_fun (hE 0 1 1 0) φ
  have s0 := congrArg (E 0 0) hs
  have s1 := congrArg (E 1 1) hs
  simp only [map_add (f := _), map_smul] at s0 s1
  refine ⟨hs, ?_⟩
  linear_combination (norm := module) s0 + s1 + (a + b) • hs + r1 + r2 - (2 : ℂ) • h0

theorem UpperTheory.V.Br.capTwo :
    UpperTheory.V.Br.CapTwo := by
  intro F _ _ _ π v a b h φ hφ
  refine cap2 _ (UpperTheory.V.TR.glRel_Eop v) a b φ fun u => ?_
  have := h.2 u φ hφ
  rw [UpperTheory.V.TR.cap] at this
  norm_num at this ⊢
  exact this
