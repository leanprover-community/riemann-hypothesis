module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastBasicProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastRatCastAndExpRat
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

noncomputable section

namespace GlobalTheory.SizeSqIntegral

theorem sz_nat_val (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (D : ℕ) :
    Sz l lam (-(padicValNat l D : ℝ)) (D : ℂ) := by
  have h := GlobalTheory.SizeRat.sz_ratCast l lam (D : ℚ) (-(padicValNat l D : ℝ)) (by
    rw [padicValRat.of_nat, Nat.padicValNat_def]; simp)
  simpa using h

theorem sz_zero_of_isIntegral (l : ℕ) [hl : Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (x : ℂ)
    (h : IsIntegral ℤ x) : Sz l lam 0 x :=
  GlobalTheory.SzRules.sz_of_isIntegral 1 x (fun hd => hl.out.one_lt.ne' (Nat.dvd_one.1 hd)) (by simpa using h)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (D M : ℕ) (x : ℂ), 0 < D → IsIntegral ℤ ((D : ℂ) * x ^ 2) → Sz l lam (-(padicValNat l D : ℝ) / 2) ((D : ℂ) * x) ∧ Sz l lam (-(padicValNat l D : ℝ) / 2) ((M * l ^ padicValNat l D : ℕ) : ℂ) := by
  intro l hl lam D M x _ hx
  constructor
  · apply GlobalTheory.SzRules.sz_of_sq
    have h := GlobalTheory.SzRules.sz_mul (sz_nat_val l lam D) (sz_zero_of_isIntegral l lam _ hx)
    rw [add_zero] at h
    convert h using 1
    ring
  · have h1 := sz_nat_val l lam (l ^ padicValNat l D)
    rw [Nat.padicValNat_def, Nat.multiplicity_prime_pow] at h1
    have h2 : Sz l lam 0 (M : ℂ) := sz_zero_of_isIntegral l lam _ (by simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (M : ℤ))))
    have h := GlobalTheory.SzRules.sz_mul h2 h1
    rw [zero_add, ← Nat.cast_mul] at h
    refine GlobalTheory.SzRules.sz_mono ?_ h
    have : (0 : ℝ) ≤ (padicValNat l D : ℝ) := Nat.cast_nonneg _
    linarith

end GlobalTheory.SizeSqIntegral
