module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem ent_eq {R : Type} [CommRing R] {X Z : M4 R} (hX : IsBlock X) (hZ : Z ∈ hAB R) (i j : Fin 4)
    (h : ¬ lamW i < lamW j) : ((1 + Z) * X) i j = X i j := by
  have hZX : (Z * X) i j = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hik : lamW i < lamW k
    · rw [hX k j (fun e => h (e ▸ hik)), mul_zero]
    · rw [hZ i k hik, zero_mul]
  rw [add_mul, one_mul, Matrix.add_apply, hZX, add_zero]

theorem UpperTheory.V.Ws.Bl.twistPt :
    ∀ (R : Type) [CommRing R] (X Z : M4 R), IsBlock X → Z ∈ uM R → (∀ ν Y, IsGSp ν Y → IsGSp ν ((1 + Z) * Y)) ∧ (∀ i j, lamW j < lamW i → ((1 + Z) * X) i j = 0) ∧
          ((1 + Z) * X).submatrix ixB ixB = X.submatrix ixB ixB ∧ ((1 + Z) * X).charpoly = X.charpoly := by
  intro R _ X Z hX hZ
  have hZa : Z ∈ hAB R := hZ.1
  have hZs : adj Z = -Z := hZ.2
  have hZZ : Z * Z = 0 := hAB_mul_hAB hZa hZa
  have hlow : ∀ i j, lamW j < lamW i → ((1 + Z) * X) i j = 0 := by
    intro i j hij
    rw [ent_eq hX hZa i j (fun h => lt_asymm h hij)]
    exact hX i j hij.ne'
  refine ⟨?_, hlow, ?_, ?_⟩
  · intro ν Y hY
    have g := grp R
    have h1 : (1 + -Z) * (1 + Z) = 1 := by
      rw [add_mul, one_mul, neg_mul, mul_add, mul_one, hZZ, add_zero]
      abel
    show adj ((1 + Z) * Y) * ((1 + Z) * Y) = ν • 1
    rw [g.1, g.2.2.1, g.2.2.2.2.1, hZs, mul_assoc, ← mul_assoc (1 + -Z), h1, one_mul]
    exact hY
  · ext a b
    exact ent_eq hX hZa _ _ (by fin_cases a <;> fin_cases b <;> decide)
  · have hT : ((1 + Z) * X).BlockTriangular lamW := fun _ _ h => hlow _ _ h
    have hTX : X.BlockTriangular lamW := fun _ _ h => hX _ _ h.ne'
    rw [hT.charpoly, hTX.charpoly]
    refine Finset.prod_congr rfl fun a _ => ?_
    congr 1
    ext i j
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply]
    exact ent_eq hX hZa _ _ (by rw [i.2, j.2]; exact lt_irrefl a)
