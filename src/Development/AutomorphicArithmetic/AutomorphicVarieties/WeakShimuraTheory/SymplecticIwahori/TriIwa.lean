module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.OfMap
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.AdjMulSelf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.SpIwa
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Pp

private theorem adj_mul {R : Type} [CommRing R] (X Y : M4 R) : adj (X * Y) = adj Y * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

private theorem adj_adj {R : Type} [CommRing R] (X : M4 R) : adj (adj X) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]

theorem UpperTheory.V.Ws.Pp.triIwa :
    ∀ {ι A F : Type} [CommRing A] [Field F] (V : ValuationSubring F) (M : ι → M4 A) (P : ι → Fin 4 → A[X]) (g : A →+* V) (h : M4 F), SpTri M P (V.subtype.comp g) h → ∃ k : M4 V, SpTri M P g k := by
  intro ι A F _ _ V M P g h hh
  obtain ⟨k, hk, hb⟩ := spIwa V h hh.1
  refine ⟨k, SpTri.of_map V.subtype Subtype.val_injective ?_⟩
  have a : adj (k.map V.subtype) = (adj k).map V.subtype := by
    ext i j
    simp only [adj_apply, Matrix.map_apply, map_zsmul]
  have k1 : adj (k.map V.subtype) * k.map V.subtype = 1 := by
    rw [a, ← Matrix.map_mul, adj_mul_self hk, Matrix.map_one _ (map_zero _) (map_one _)]
  generalize k.map V.subtype = K at hb k1
  have h2 : h * adj h = 1 := mul_adj_self hh.1
  have hb' : IsUp (adj h * K) := by
    have := IsUp_adj hb
    rwa [adj_mul, adj_adj] at this
  have one : adj K * h * (adj h * K) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc h, h2, Matrix.one_mul, k1]
  refine ⟨k1.trans (one_smul _ _).symm, fun i => ?_⟩
  have e : ∀ X : M4 F, adj K * X * K = adj K * h * (adj h * X * h) * (adj h * K) := fun X => by
    calc adj K * X * K = adj K * (h * adj h) * X * (h * adj h) * K := by
          rw [h2, Matrix.mul_one, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have c := upConj one hb hb' (hh.2 i).1
  rw [e]
  exact ⟨c.1, fun j => by rw [c.2 j]; exact (hh.2 i).2 j⟩
