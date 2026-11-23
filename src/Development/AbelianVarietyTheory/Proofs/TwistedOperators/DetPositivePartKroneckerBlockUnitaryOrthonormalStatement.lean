module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetPositivePartKroneckerBlockUnitaryOrthonormal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open Formalism.IndefR.Datum Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting


theorem _root_.GlobalTheory.T.detPositivePartKronecker_blockUnitary_orthonormal : ∀ {n m : ℕ} (GS sS BS κS : Matrix (Fin n) (Fin n) ℂ) (GT sT BT κT : Matrix (Fin m) (Fin m) ℂ) (pS pT : ℕ), pS ≤ n → pT ≤ m → IsONBasis GS sS BS pS → IsONBasis GT sT BT pT → IsKMat pS κS → IsKMat pT κT → GlobalTheory.WeilParts.detPlus sS sT (BS * κS * BS⁻¹)⁻¹ (BT * κT * BT⁻¹) = detPos pT κT ^ pS * detNeg pT κT ^ (n - pS) * (detPos pS κS ^ pT)⁻¹ * (detNeg pS κS ^ (m - pT))⁻¹ := by
  first | exact @GlobalTheory.PlusDetONB.detPlus_onb | exact GlobalTheory.PlusDetONB.detPlus_onb | (intros; apply GlobalTheory.PlusDetONB.detPlus_onb <;> assumption)
