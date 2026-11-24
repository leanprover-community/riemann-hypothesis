module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.MvPolynomial.Tower

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.RatPts


open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
lemma _root_.GlobalTheory.ClassFin.RatPts.ev_map_algebraMap {ι R : Type} [CommRing R] [Algebra ℚ R]
    (f : MvPolynomial (ι × ι) ℚ) (γ : Matrix ι ι ℚ) :
    _root_.GlobalTheory.ClassFin.ev f (γ.map (algebraMap ℚ R)) = algebraMap ℚ R (_root_.GlobalTheory.ClassFin.ev f γ) := by
  unfold _root_.GlobalTheory.ClassFin.ev
  rw [← MvPolynomial.aeval_algebraMap_apply]
  rfl


open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
theorem _root_.GlobalTheory.ClassFin.RatPts.rat_mem_pts : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ γ : Matrix ι ι ℚ, γ.map (algebraMap ℚ ℂ) ∈ Γ → γ ∈ _root_.GlobalTheory.ClassFin.pts Γ ℚ) ∧ ∀ (R : Type) [CommRing R] [Algebra ℚ R], ∀ γ ∈ _root_.GlobalTheory.ClassFin.pts Γ ℚ, γ.map (algebraMap ℚ R) ∈ _root_.GlobalTheory.ClassFin.pts Γ R := by
  intro ι _ _ Γ
  refine ⟨fun γ hγ => ?_, fun R _ _ γ hγ => ?_⟩
  · simp only [_root_.GlobalTheory.ClassFin.pts, Set.mem_setOf_eq]
    intro f hf
    have h := hf _ hγ
    rw [_root_.GlobalTheory.ClassFin.RatPts.ev_map_algebraMap] at h
    exact (algebraMap ℚ ℂ).injective (by rw [h, map_zero])
  · simp only [_root_.GlobalTheory.ClassFin.pts, Set.mem_setOf_eq] at hγ ⊢
    intro f hf
    rw [_root_.GlobalTheory.ClassFin.RatPts.ev_map_algebraMap, hγ f hf, map_zero]

end GlobalTheory.ClassFin.RatPts
