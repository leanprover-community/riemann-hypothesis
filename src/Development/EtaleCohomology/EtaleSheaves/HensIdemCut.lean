module

public import Development.EtaleCohomology.EtaleSheaves.EtaleDegreeZeroCohomologyEquivLocallyConstantFun
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

@[expose] public section

noncomputable section
open Polynomial

namespace LateralTheory.E.HensIdemCut

def LJac : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (B : Type) [CommRing B] (φ : A →+* B),
  φ.IsIntegral → I.map φ ≤ Ideal.jacobson ⊥

def LMonic : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) (B : Type) [CommRing B] (φ : A →+* B),
  φ.IsIntegral → ∀ b : B, b * b - b ∈ I.map φ → ∃ (N : ℕ) (f : A[X]), f.Monic ∧ f.eval₂ φ b = 0 ∧
    f.map (Ideal.Quotient.mk I) = X ^ N * (X - C 1) ^ N

def LFactor : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (f : A[X]) (g₀ h₀ : (A ⧸ I)[X]),
  f.Monic → g₀.Monic → h₀.Monic → IsCoprime g₀ h₀ → f.map (Ideal.Quotient.mk I) = g₀ * h₀ →
  ∃ g h : A[X], g.Monic ∧ h.Monic ∧ f = g * h ∧ g.map (Ideal.Quotient.mk I) = g₀ ∧ h.map (Ideal.Quotient.mk I) = h₀

def LIdem : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) (B : Type) [CommRing B] (φ : A →+* B),
  I.map φ ≤ Ideal.jacobson ⊥ → ∀ (b : B), b * b - b ∈ I.map φ → ∀ (N : ℕ) (g h : A[X]),
  g.map (Ideal.Quotient.mk I) = X ^ N → h.map (Ideal.Quotient.mk I) = (X - C 1) ^ N →
  g.eval₂ φ b * h.eval₂ φ b = 0 → ∃ x : B, IsIdempotentElem x ∧ x - b ∈ I.map φ

theorem goal_of (hJ : LJac) (hM : LMonic) (hF : LFactor) (hI : LIdem) : LateralTheory.E.t_E1Cut.HensIdem := by
  intro A _ I _ B _ φ hφ
  refine ⟨hJ A I B φ hφ, ?_⟩
  intro e he
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective e
  have hb : b * b - b ∈ I.map φ := by
    rw [← Ideal.Quotient.eq]
    simpa [IsIdempotentElem] using he
  obtain ⟨N, f, hfm, hf0, hfI⟩ := hM A I B φ hφ b hb
  have hcop : IsCoprime ((X : (A ⧸ I)[X]) ^ N) ((X - C 1) ^ N) :=
    (show IsCoprime (X : (A ⧸ I)[X]) (X - C 1) from ⟨1, -1, by rw [C_1]; ring⟩).pow
  obtain ⟨g, h, -, -, rfl, hg, hh⟩ :=
    hF A I f _ _ hfm ((monic_X).pow N) ((monic_X_sub_C 1).pow N) hcop hfI
  obtain ⟨x, hx, hxb⟩ := hI A I B φ (hJ A I B φ hφ) b hb N g h hg hh (by rw [← eval₂_mul]; exact hf0)
  exact ⟨x, hx, Ideal.Quotient.eq.mpr hxb⟩

end LateralTheory.E.HensIdemCut
