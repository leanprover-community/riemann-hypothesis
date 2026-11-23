module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Formalism.ConjugateSelfDual.Statement
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem UpperTheory.V.GradeZeroInterpolatingElement.sixBlock_unit {R : Type} [CommRing R] [IsLocalRing R] {ν a w p h : R} (hν : IsUnit ν)
    (hp : p ∈ maximalIdeal R) (e : a * w - p * h = ν) : IsUnit a := by
  have hu : IsUnit (a * w) := by
    have hx : a * w = ν + p * h := by rw [← e]; ring
    rw [hx]
    by_contra hn
    have h1 : ν + p * h ∈ maximalIdeal R := (mem_maximalIdeal _).2 hn
    have h2 : p * h ∈ maximalIdeal R := Ideal.mul_mem_right _ _ hp
    have h3 : ν ∈ maximalIdeal R := by simpa using Ideal.sub_mem _ h1 h2
    exact (mem_maximalIdeal _).1 h3 hν
  exact isUnit_of_mul_isUnit_left hu

theorem UpperTheory.V.GradeZeroInterpolatingElement.sixBlock :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (ν : R) (g : M4 R), IsUnit ν → IsGSp ν g → (∀ i j, i ≠ j → g i j ∈ maximalIdeal R) → g 0 1 = 0 → g 0 3 = 0 → g 2 1 = 0 → g 1 0 = 0 → g 3 0 = 0 → g 1 2 = 0 → IsBlock g ∧ (ν = 1 → g 0 2 = 0 → g 2 0 = 0 → g 0 0 = 1 → g 1 1 = 1 → g = 1) := by
  intro R _ _ ν g hν hg hoff h01 h03 h21 h10 h30 h12
  have hg' : adj g * g = ν • 1 := hg
  have E : ∀ i j, (adj g * g) i j = (ν • (1 : M4 R)) i j := fun i j => by rw [hg']
  have errorNonneg := E 0 0
  have bivariateExponentMonomial := E 0 1
  have E11 := E 1 1
  have E10 := E 1 0
  have E13 := E 1 3
  have E20 := E 2 0
  simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, h01, h03, h21, h10, h30, h12,
    Matrix.one_apply] at errorNonneg bivariateExponentMonomial E11 E10 E13 E20
  have u00 : IsUnit (g 0 0) :=
    UpperTheory.V.GradeZeroInterpolatingElement.sixBlock_unit (w := g 3 3) (h := g 2 0) hν (hoff 1 3 (by decide)) (by rw [← errorNonneg]; ring)
  have u11 : IsUnit (g 1 1) :=
    UpperTheory.V.GradeZeroInterpolatingElement.sixBlock_unit (w := g 2 2) (h := g 3 1) hν (hoff 0 2 (by decide)) (by rw [← E11]; ring)
  have h23 : g 2 3 = 0 := u11.mul_left_eq_zero.1 bivariateExponentMonomial
  have h32 : g 3 2 = 0 := u00.mul_left_eq_zero.1 E10
  refine ⟨?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [lamW, h01, h03, h21, h23, h10, h12, h30, h32] at hij ⊢
  · intro hν1 h02 h20 h00 h11
    subst hν1
    have h22 : g 2 2 = 1 := by simpa [h11, h02] using E11
    have h33 : g 3 3 = 1 := by simpa [h00, h20] using errorNonneg
    have h13 : g 1 3 = 0 := by simpa [h22, h02] using E13
    have h31 : g 3 1 = 0 := by simpa [h11, h20, h00] using E20
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.one_apply, h00, h01, h02, h03, h10, h11, h12, h13, h20, h21, h22, h23, h30, h31, h32, h33]
