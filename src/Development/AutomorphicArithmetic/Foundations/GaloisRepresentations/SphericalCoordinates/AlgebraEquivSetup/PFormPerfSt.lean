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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne

@[expose] public section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pFormPerfSt :
    FormPerfSt := by
  intro E _ _ _ A n q hP
  obtain ⟨e, he, hx, c', hc⟩ := hP
  refine ⟨e ^ 3, Nat.Coprime.pow_left 3 he, fun f => ?_⟩
  choose x hxf using fun i : Fin n =>
    hx (((f.toAddMonoidHom.comp (AddMonoidHom.single _ i)).comp A.bar.toAddMonoidHom).toIntLinearMap)
  refine ⟨fun i => -((if (i : ℕ) = 0 then c' * (e : 𝓞 E) else c' ^ 2) * x i), ?_⟩
  refine LinearMap.ext fun y => ?_
  rw [Arith.EF_apply]
  have key : ∀ i, A.hd n i * -((if (i : ℕ) = 0 then c' * (e : 𝓞 E) else c' ^ 2) * x i) * A.bar (y i)
      = ((e ^ 2 : ℕ) : 𝓞 E) * (x i * A.bar (y i)) := by
    intro i
    simp only [Arith.hd, Arith.dg]
    push_cast
    split_ifs
    · linear_combination ((e : 𝓞 E) * x i * A.bar (y i)) * hc
    · linear_combination (c' * A.c + (e : 𝓞 E)) * x i * A.bar (y i) * hc
  have hs : ∀ i, A.trd (x i * A.bar (y i)) = (e : ℤ) * f (Pi.single i (y i)) := by
    intro i
    rw [hxf i]
    simp [Arith.bar_bar]

  rw [Finset.sum_congr rfl (fun i _ => key i), ← Finset.mul_sum, ← nsmul_eq_mul, map_nsmul, map_sum]
  simp_rw [hs]

  rw [← Finset.mul_sum, ← map_sum, Finset.univ_sum_single]
  simp only [LinearMap.smul_apply, nsmul_eq_mul]
  push_cast
  ring
