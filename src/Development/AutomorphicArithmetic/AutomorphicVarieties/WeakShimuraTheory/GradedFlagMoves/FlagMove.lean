module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem up_mul {k : Type} [Field k] {A B : M4 k} (hA : IsUp A) (hB : IsUp B) :
    IsUp (A * B) ∧ ∀ i, (A * B) i i = A i i * B i i := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    rcases lt_or_ge m i with h | h
    · rw [hA i m h, zero_mul]
    · rw [hB m j (lt_of_lt_of_le hij h), mul_zero]
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i (fun m _ hm => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rcases lt_or_gt_of_ne hm with h | h
    · rw [hA i m h, zero_mul]
    · rw [hB m i h, mul_zero]

private theorem up_inv {k : Type} [Field k] {A B : M4 k} (hA : IsUp A) (h : A * B = 1) : IsUp B := by
  have hA' : Matrix.BlockTriangular A id := fun i j hij => hA i j hij
  haveI : Invertible A := invertibleOfRightInverse A B h
  have h1 := Matrix.blockTriangular_inv_of_blockTriangular hA'
  rw [Matrix.inv_eq_right_inv h] at h1
  exact fun i j hij => h1 hij

theorem UpperTheory.V.Ws.Rt.flagMove :
    ∀ (k : Type) [Field k] (X X' Z n n' : M4 k), X * X' = 1 → IsLow n → IsLow n' → IsUp (adj n' * X * n) → IsUp (adj n * Z * n) →
      IsUp (adj n' * (X * Z * X') * n') ∧ ∀ i, (adj n' * (X * Z * X') * n') i i = (adj n * Z * n) i i := by
  intro k _ X X' Z n n' hX hn hn' hB hY
  have h1 : adj n * n = 1 := by simpa [IsGSp] using hn.1
  have h2 : adj n' * n' = 1 := by simpa [IsGSp] using hn'.1
  have h3 : n * adj n = 1 := mul_eq_one_comm.mp h1
  have h4 : ∀ W : M4 k, n * (adj n * W) = W := fun W => by rw [← mul_assoc, h3, one_mul]
  have h5 : ∀ W : M4 k, X * (X' * W) = W := fun W => by rw [← mul_assoc, hX, one_mul]
  have hBB : (adj n' * X * n) * (adj n * X' * n') = 1 := by
    simp only [mul_assoc, h4, h5, h2]
  have hB' := up_inv hB hBB
  have e : adj n' * (X * Z * X') * n' = (adj n' * X * n) * (adj n * Z * n) * (adj n * X' * n') := by
    simp only [mul_assoc, h4]
  rw [e]
  have p1 := up_mul hB hY
  have p2 := up_mul p1.1 hB'
  refine ⟨p2.1, fun i => ?_⟩
  have q := (up_mul hB hB').2 i
  rw [hBB, Matrix.one_apply_eq] at q
  rw [p2.2, p1.2]
  linear_combination (-(adj n * Z * n) i i) * q
