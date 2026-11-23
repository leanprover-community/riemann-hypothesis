module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeVectorEqNsmulOfAdelicNsmul
public import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsPPowMulIntOfIsIntAfAlgebraMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Pointwise
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys

@[expose] public section

open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.exists_p_pow_smul_eq_of_mem_completedLattice :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (w : VQ D), (1 : AfP p) ⊗ₜ[ℚ] w ∈ LaHat D → ∃ (r : ℕ) (a : D.La), p ^ r • w = (1 : ℚ) ⊗ₜ[ℤ] a := by
  intro p _ D w hw
  have := D.freeLa
  have := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  let B := b.baseChange ℚ
  have hint : ∀ i, IsIntAf (algebraMap ℚ (AfP p) (B.repr w i)) := by
    intro i
    have h := GlobalTheory.LKGeo.LatDvd.isIntAf_adBasis_repr b i hw
    have e : (GlobalTheory.LKGeo.LatDvd.adBasis b).repr ((1 : AfP p) ⊗ₜ[ℚ] w) i
        = algebraMap ℚ (AfP p) (B.repr w i) := by
      simp only [GlobalTheory.LKGeo.LatDvd.adBasis, Module.Basis.baseChange_repr_tmul]
      rw [Algebra.algebraMap_eq_smul_one]
    rwa [e] at h
  choose r z hz using fun i => UpperTheory.exists_p_pow_mul_int_of_isIntAf_algebraMap p (B.repr w i) (hint i)
  let R : ℕ := Finset.univ.sup r
  have hR : ∀ i, r i ≤ R := fun i => Finset.le_sup (Finset.mem_univ i)
  let a : D.La := ∑ i, ((p : ℤ) ^ (R - r i) * z i) • b i
  refine ⟨R, a, B.ext_elem fun i => ?_⟩
  have ha : b.repr a i = (p : ℤ) ^ (R - r i) * z i := by

    simp [a, map_sum, Finsupp.single_apply]
  have e2 : B.repr ((1 : ℚ) ⊗ₜ[ℤ] a) i = ((b.repr a i : ℤ) : ℚ) := by
    simp [B, Module.Basis.baseChange_repr_tmul]
  rw [e2, ha, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
  push_cast
  rw [← hz i]
  have : (p : ℚ) ^ R = (p : ℚ) ^ (R - r i) * (p : ℚ) ^ r i := by
    rw [← pow_add, Nat.sub_add_cancel (hR i)]
  rw [this]
  ring
