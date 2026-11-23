module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormMinpolyCoeffZeroPowNumberField
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)

theorem _root_.GlobalTheory.T.abs_norm_minpoly_coeff_zero_pow_numberField : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (β : ℂ) (p : K[X]), GlobalTheory.FunObj.SqNum.IsMinPol σ β p → IsAlgebraic ℚ β → |(Algebra.norm ℚ (p.coeff 0) : ℚ)| ^ (minpoly ℚ β).natDegree = |(minpoly ℚ β).coeff 0| ^ (p.natDegree * Module.finrank ℚ K) := by
  first | exact @GlobalTheory.NormTower.abs_norm_coeff_zero_pow | exact GlobalTheory.NormTower.abs_norm_coeff_zero_pow | (intros; apply GlobalTheory.NormTower.abs_norm_coeff_zero_pow <;> assumption)
