module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvFilD
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.FilInv

theorem pow_mem_Fil {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {b : ℤ} {x : BdR} (hx : x ∈ PD.Fil b) (n : ℕ) :
    x ^ n ∈ PD.Fil (n * b) := by
  induction n with
  | zero => simpa using PD.one_mem
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ, add_mul, one_mul]
    exact PD.Fil_mul _ _ _ _ ih hx

theorem inv_mem_Fil_neg : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (a : ℤ) (u v : P.R.BdR), u * v = 1 → u ∈ (P.PD K).Fil a → u ∉ (P.PD K).Fil (a + 1) → v ∈ (P.PD K).Fil (-a) := by
  intro l _ P AI T K a u v huv hu hu1
  obtain ⟨s, hs, hts⟩ := GlobalTheory.TopSteps.CrysRules.exists_inverse_fontaineElement_mem_fil_neg_one T K
  have ht := (P.PD K).mem_filtration_one

  obtain ⟨w, w', hw, hw', hww⟩ : ∃ w w' : P.R.BdR, w ∈ (P.PD K).Fil (-a) ∧ w' ∈ (P.PD K).Fil a ∧
      w * w' = 1 := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg a
    · refine ⟨s ^ n, ((P.PD K).ι (P.PD K).t) ^ n, ?_, ?_, ?_⟩
      · simpa using pow_mem_Fil (P.PD K) hs n
      · simpa using pow_mem_Fil (P.PD K) ht n
      · rw [← mul_pow, mul_comm, hts, one_pow]
    · refine ⟨((P.PD K).ι (P.PD K).t) ^ n, s ^ n, ?_, ?_, ?_⟩
      · simpa using pow_mem_Fil (P.PD K) ht n
      · simpa using pow_mem_Fil (P.PD K) hs n
      · rw [← mul_pow, hts, one_pow]
  have hx0 : u * w ∈ (P.PD K).Fil 0 := by
    simpa using (P.PD K).Fil_mul _ _ _ _ hu hw
  have hx1 : u * w ∉ (P.PD K).Fil 1 := by
    intro h
    apply hu1
    have := (P.PD K).Fil_mul _ _ _ _ h hw'
    rwa [mul_assoc, hww, mul_one, add_comm] at this
  obtain ⟨y, hy, hxy⟩ := ((GlobalTheory.Per.TiedField.tied_field l P AI T).2.2.2.2) K _ hx0 hx1
  have hv : v = w * y := by
    calc v = v * ((u * w) * y) := by rw [hxy, mul_one]
      _ = (u * v) * (w * y) := by ring
      _ = w * y := by rw [huv, one_mul]
  rw [hv]
  simpa using (P.PD K).Fil_mul _ _ _ _ hw hy

end GlobalTheory.FilInv
