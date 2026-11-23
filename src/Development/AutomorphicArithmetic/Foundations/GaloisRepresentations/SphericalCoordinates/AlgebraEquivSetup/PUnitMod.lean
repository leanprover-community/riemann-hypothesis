module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.CharP
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open NumberField

namespace UpperTheory.Gal.W2.Seed

private theorem norm_cast_eq_one {E : Type} [Field E] [NumberField E] (M : ℕ) (b : 𝓞 E) :
    ((Algebra.norm ℤ (1 + (M : 𝓞 E) * b) : ℤ) : ZMod M) = 1 := by
  classical
  let bs := Module.Free.chooseBasis ℤ (𝓞 E)
  rw [Algebra.norm_eq_matrix_det bs, ← eq_intCast (Int.castRingHom (ZMod M)), RingHom.map_det]
  simp only [map_add (f := _), map_one, map_mul, map_natCast, ZMod.natCast_self, zero_mul, add_zero,
    Matrix.det_one, CharP.cast_eq_zero]

theorem pUnitMod : UnitMod := by
  intro E _ _ M c b _ h
  refine ⟨(Algebra.norm ℤ c).natAbs, ?_, ?_⟩
  · rw [← ZMod.isUnit_iff_coprime]
    have key := norm_cast_eq_one (E := E) M b
    rw [← h] at key
    rcases Int.natAbs_eq (Algebra.norm ℤ c) with hn | hn
    · rw [hn, Int.cast_natCast] at key
      rw [key]
      exact isUnit_one
    · rw [hn, Int.cast_neg, Int.cast_natCast, neg_eq_iff_eq_neg] at key
      rw [key]
      exact isUnit_one.neg
  · have hm := Ideal.absNorm_mem (Ideal.span ({c} : Set (𝓞 E)))
    rw [Ideal.absNorm_span_singleton, Ideal.mem_span_singleton] at hm
    obtain ⟨c', hc'⟩ := hm
    exact ⟨c', hc'.symm⟩

end UpperTheory.Gal.W2.Seed
