module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Linter.HaveILetI
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

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory

theorem UnitLemma.exists_unit_residue (K : UQ) (B : InvAlg K) (hB : IsReduced B.A) (m : MaximalSpectrum B.A)
    (z : B.A ⧸ m.asIdeal) (hz : z ≠ 0) :
    ∃ y : B.Aˣ, Ideal.Quotient.mk m.asIdeal (y : B.A) = z ∧
      ∀ m' : MaximalSpectrum B.A, m' ≠ m → Ideal.Quotient.mk m'.asIdeal (y : B.A) = 1 := by
  classical
  haveI : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A
  let e := IsArtinianRing.equivPi B.A
  let v : (I : MaximalSpectrum B.A) → B.A ⧸ I.asIdeal := fun I =>
    if h : I = m then h ▸ z else 1
  have hv : IsUnit v := by
    rw [Pi.isUnit_iff]
    intro I
    letI := Ideal.Quotient.field I.asIdeal
    rw [isUnit_iff_ne_zero]
    by_cases h : I = m
    · subst h; simpa [v] using hz
    · simp [v, h]
  have hy : IsUnit (e.symm v) := hv.map e.symm
  refine ⟨hy.unit, ?_, ?_⟩
  · have := IsArtinianRing.equivPi_apply B.A (e.symm v) m
    rw [AlgEquiv.apply_symm_apply] at this
    simp only [IsUnit.unit_spec]
    rw [← this]; simp [v]
  · intro m' hm'
    have := IsArtinianRing.equivPi_apply B.A (e.symm v) m'
    rw [AlgEquiv.apply_symm_apply] at this
    simp only [IsUnit.unit_spec]
    rw [← this]; simp [v, hm']

theorem UnitLemma.unit_prescribed_residue : ∀ (K : UQ) (B : InvAlg K), IsReduced B.A → ∀ (m : MaximalSpectrum B.A)
    (z : B.A ⧸ m.asIdeal), z ≠ 0 → ∃ y : B.Aˣ, Ideal.Quotient.mk m.asIdeal (y : B.A) = z ∧
      ∀ m' : MaximalSpectrum B.A, m' ≠ m → Ideal.Quotient.mk m'.asIdeal (y : B.A) = 1 :=
  fun K B hB m z hz => UnitLemma.exists_unit_residue K B hB m z hz

end GlobalTheory
