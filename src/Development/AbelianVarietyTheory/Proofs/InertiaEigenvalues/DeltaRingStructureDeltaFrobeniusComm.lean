module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem int_frob_lift (l : ℕ) [hl : Fact l.Prime] (a : ℤ) :
    ∃ b : ℤ, (RingHom.id ℤ) a = a ^ l + (l : ℤ) * b := by
  have h : ((a ^ l : ℤ) : ZMod l) = ((a : ℤ) : ZMod l) := by
    push_cast; exact ZMod.pow_card _
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨b, hb⟩ := h
  exact ⟨b, by simp only [RingHom.id_apply]; linear_combination hb⟩

def intDelta (l : ℕ) [hl : Fact l.Prime] : Delta l ℤ :=
  Delta.ofLift l (RingHom.id ℤ)
    (fun x hx => (mul_eq_zero.1 hx).resolve_left (by exact_mod_cast hl.out.ne_zero))
    (int_frob_lift l)

theorem poly_δ_φ (l : ℕ) [hl : Fact l.Prime] (x : MvPolynomial ℕ ℤ) :
    (polyDelta (intDelta l)).δ ((polyDelta (intDelta l)).φ x) =
      (polyDelta (intDelta l)).φ ((polyDelta (intDelta l)).δ x) := by
  set D := polyDelta (intDelta l)
  have hl0 : (l : MvPolynomial ℕ ℤ) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  refine mul_left_cancel₀ hl0 ?_
  have h1 := D.φ_eq (D.φ x)
  have h2 := D.φ_eq x
  have h3 : D.φ ((l : MvPolynomial ℕ ℤ) * D.δ x) = (l : MvPolynomial ℕ ℤ) * D.φ (D.δ x) := by
    rw [map_mul, map_natCast]
  have h4 : D.φ (D.φ x) = D.φ (x ^ l) + D.φ ((l : MvPolynomial ℕ ℤ) * D.δ x) := by
    rw [← map_add (f := _), ← h2]
  rw [map_pow] at h4
  linear_combination -h1 + h4 + h3

theorem Delta.δ_φ_comm : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (a : A),
    D.δ (D.φ a) = D.φ (D.δ a) := by
  intro l hl A _ D a
  set D₀ := polyDelta (intDelta l)
  let g : MvPolynomial ℕ ℤ →+* A := MvPolynomial.eval₂Hom (Int.castRingHom A) (fun i => D.δ^[i] a)
  have hg : ∀ p, p ∈ δLocus D₀ D g := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C n =>
      have : MvPolynomial.C n = ((n : ℤ) : MvPolynomial ℕ ℤ) := by simp
      rw [this]; exact intCast_mem _ n
    | add p q hp hq => exact add_mem hp hq
    | mul_X p i hp =>
      refine mul_mem hp (mem_δLocus.2 ?_)
      rw [polyDelta_X]
      simp only [g, MvPolynomial.eval₂Hom_X']
      rw [Function.iterate_succ_apply']
  have hgδ : ∀ p, g (D₀.δ p) = D.δ (g p) := fun p => mem_δLocus.1 (hg p)
  have hgφ : ∀ p, g (D₀.φ p) = D.φ (g p) := Delta.map_φ_of_map_δ D₀ D g hgδ
  have hX : g (MvPolynomial.X 0) = a := by simp [g]
  have := congrArg g (poly_δ_φ l (MvPolynomial.X 0))
  rw [hgδ, hgφ, hgφ, hgδ, hX] at this
  exact this

end GlobalTheory.BSP
