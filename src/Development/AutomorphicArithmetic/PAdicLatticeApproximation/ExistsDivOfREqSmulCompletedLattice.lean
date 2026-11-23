module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys
public import Development.AutomorphicArithmetic.PAdicLatticeApproximation.PLatticeSaturatedAndCofinite
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.exists_div_of_r_eq_smul_completedLattice :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D) (w : VQ D) (n : ℕ) (e : AfP p ⊗[ℚ] VQ D), w ∈ X.lat → 0 < n → n.Coprime p → e ∈ LaHat D → X.r w = n • e → ∃ u ∈ X.lat, w = n • u := by
  intro p _ D X w n e hw hn hc he hr
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hwu : w = n • ((n : ℚ)⁻¹ • w) := by
    rw [← Nat.cast_smul_eq_nsmul ℚ n, smul_smul, mul_inv_cancel₀ hn0, one_smul]
  have hru : X.r ((n : ℚ)⁻¹ • w) = e := by
    rw [map_smul, hr, ← Nat.cast_smul_eq_nsmul ℚ n, smul_smul, inv_mul_cancel₀ hn0, one_smul]
  refine ⟨(n : ℚ)⁻¹ • w, ⟨(UpperTheory.p_lattice_saturated_and_cofinite p D X.M X.hM).1 n _ hc ?_, ?_⟩, hwu⟩
  · rw [← hwu]; exact hw.1
  · rw [hru]; exact he
