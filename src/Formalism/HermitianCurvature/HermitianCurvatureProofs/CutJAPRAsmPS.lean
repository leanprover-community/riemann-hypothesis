module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPolyRadialCut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

noncomputable section

namespace Asm

def ggP (TT : ℝ) : MvPolynomial (Fin 3) ℂ := MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (TT : ℂ)

theorem gg_eval (TT : ℝ) (ζ : ℂ) : MvPolynomial.eval ![ζ, conj ζ, sig TT ζ] (ggP TT) = gg TT ζ := by
  simp only [ggP, map_sub, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, gg]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Complex.mul_conj]
  push_cast
  ring

theorem PS.congr {TT : ℝ} {f g : ℂ → ℂ} (hf : PS TT f) (h : ∀ ζ : ℂ, TT < Complex.normSq ζ → g ζ = f ζ) :
    PS TT g := by
  obtain ⟨m, p, hp⟩ := hf
  exact ⟨m, p, fun ζ hζ => by rw [h ζ hζ]; exact hp ζ hζ⟩

theorem PS.const (TT : ℝ) (a : ℂ) : PS TT (fun _ => a) :=
  ⟨0, MvPolynomial.C a, fun ζ _ => by simp⟩

theorem PS.mul {TT : ℝ} {f g : ℂ → ℂ} (hf : PS TT f) (hg : PS TT g) : PS TT (fun ζ => f ζ * g ζ) := by
  obtain ⟨m, p, hp⟩ := hf
  obtain ⟨m', p', hp'⟩ := hg
  refine ⟨m + m', p * p', fun ζ hζ => ?_⟩
  rw [map_mul, ← hp ζ hζ, ← hp' ζ hζ]
  ring

theorem PS.add {TT : ℝ} {f g : ℂ → ℂ} (hf : PS TT f) (hg : PS TT g) : PS TT (fun ζ => f ζ + g ζ) := by
  obtain ⟨m, p, hp⟩ := hf
  obtain ⟨m', p', hp'⟩ := hg
  refine ⟨m + m', p * ggP TT ^ m' + p' * ggP TT ^ m, fun ζ hζ => ?_⟩
  rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, gg_eval, ← hp ζ hζ, ← hp' ζ hζ]
  ring

theorem PS.sum {TT : ℝ} {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (h : ∀ i ∈ s, PS TT (f i)) :
    PS TT (fun ζ => ∑ i ∈ s, f i ζ) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact PS.congr (PS.const TT 0) fun ζ _ => by simp
  | insert a s ha ih =>
    exact PS.congr (PS.add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))
      fun ζ _ => by rw [Finset.sum_insert ha]

theorem PSV.apply {TT : ℝ} {V : Type*} [AddCommGroup V] [Module ℂ V] {f : ℂ → V} (hf : PSV TT f)
    (L : V →ₗ[ℂ] ℂ) : PS TT (fun ζ => L (f ζ)) := by
  obtain ⟨n, a, v, ha, hf⟩ := hf
  refine PS.congr (PS.sum Finset.univ (fun i ζ => a i ζ * L (v i)) fun i _ => PS.mul (ha i) (PS.const TT _))
    fun ζ hζ => ?_

  rw [hf ζ hζ, map_sum]
  simp only [map_smul, smul_eq_mul]

end Asm

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
