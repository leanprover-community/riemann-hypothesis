module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeNsmulEndomorphismPreservesCompletio
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.exists_dual_vector_of_integral_functional :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D) (g : VQ D →ₗ[ℚ] ℚ), (∀ u ∈ X.lat, ∃ z : ℤ, g u = z) → ∃ w ∈ X.M, ∀ u, X.s * X.B w u = g u := by
  intro p _ D X g hg
  have := D.finLa
  have hnd : X.B.Nondegenerate :=
    (LinearMap.IsRefl.nondegenerate_iff_separatingLeft (LinearMap.IsAlt.isRefl X.alt)).mpr X.nondeg
  let w0 := (X.B.toDual hnd).symm g
  have hB : ∀ u, X.B w0 u = g u := by
    intro u
    exact LinearMap.BilinForm.apply_toDual_symm_apply (hB := hnd) g u
  have hw : ∀ u, X.s * X.B (X.s⁻¹ • w0) u = g u := by
    intro u
    rw [map_smul, LinearMap.smul_apply, hB, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ X.s_pos.ne', one_mul]
  refine ⟨X.s⁻¹ • w0, ?_, hw⟩
  rw [X.perf]
  intro u hu
  rw [hw]
  obtain ⟨t, ht0, htp, htm⟩ := DenEnd.exists_coprime_nsmul_mem D (X.r u)
  have hlat : t • u ∈ X.lat :=
    X.mem_lat.mpr ⟨X.M.nsmul_mem hu t, by simpa only [map_nsmul] using htm⟩
  obtain ⟨z, hz⟩ := hg _ hlat
  rw [map_nsmul, nsmul_eq_mul] at hz
  have ht : (t : ℚ) ≠ 0 := by exact_mod_cast ht0.ne'
  have hq : g u = (z : ℚ) / (t : ℚ) := by
    rw [eq_div_iff ht, mul_comm, hz]
  have hd := Rat.den_dvd z t
  rw [Rat.divInt_eq_div] at hd
  push_cast at hd
  rw [hq]
  exact Nat.Coprime.coprime_dvd_left (Int.natCast_dvd_natCast.mp hd) htp
