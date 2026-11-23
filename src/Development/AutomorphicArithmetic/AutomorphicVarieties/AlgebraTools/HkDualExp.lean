module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeEqDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDdSpec
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem dual_symm {R : Type} [CommRing R] {n : ℕ} {ι : Type} [Fintype ι]
    {a b : ι → MvPolynomial (Fin n) R} (h : IsDual a b) : IsDual b a := by
  intro w
  have h2 := congrArg (rename ⇑w) (h w⁻¹)

  simp only [map_sum, map_mul, rename_rename] at h2
  have hc : (⇑w ∘ ⇑w⁻¹ : Fin n → Fin n) = id := by
    funext k
    simp
  simp only [hc, rename_id, AlgHom.id_apply] at h2
  simp_rw [mul_comm (b _)]
  rw [h2]
  by_cases hw : w = 1
  · subst hw
    simp
  · have hw' : w⁻¹ ≠ 1 := inv_ne_one.mpr hw
    simp [hw, hw']

private theorem dual_exp {R : Type} [CommRing R] [IsDomain R] {n : ℕ} {ι : Type} [Fintype ι]
    {a b : ι → MvPolynomial (Fin n) R} (h : IsDual a b) (x : MvPolynomial (Fin n) R) :
    ∑ i, a i * dd (b i * x) = x := by
  obtain ⟨hD, -, -⟩ := UpperTheory.V.AlgebraTools.hkDe R n
  apply mul_left_cancel₀ hD
  rw [Finset.mul_sum]
  simp_rw [mul_left_comm (De R n), UpperTheory.V.AlgebraTools.hkDdSpec, alt, Finset.mul_sum, map_mul]
  rw [Finset.sum_comm]
  have key : ∀ y : Perm (Fin n), ∑ i, a i * Perm.sign y • ((rename ⇑y) (b i) * (rename ⇑y) x) =
      Perm.sign y • ((if y = 1 then De R n else 0) * (rename ⇑y) x) := by
    intro y
    rw [← h y, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, mul_assoc]
  rw [Finset.sum_congr rfl fun y _ => key y]
  simp

theorem UpperTheory.V.AlgebraTools.hkDualExp :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (ι : Type) [Fintype ι] (a b : ι → MvPolynomial (Fin n) R), IsDual a b →
      ∀ x, ∑ i, a i * dd (b i * x) = x ∧ ∑ i, b i * dd (a i * x) = x := by
  intro R _ _ n ι _ a b h x
  exact ⟨dual_exp h x, dual_exp (dual_symm h) x⟩
