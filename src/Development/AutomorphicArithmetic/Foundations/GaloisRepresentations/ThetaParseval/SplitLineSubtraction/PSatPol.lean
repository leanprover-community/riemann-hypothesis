module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatWDCharPolChars
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
open UpperTheory.Gal.TP.Sub

private theorem satPol_val (q a : ℕ) (b : ℂˣ) (m : ℤ) :
    ((((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ) * (b : ℂ)) ^ (-m) =
      ((q : ℂ) ^ ((((1 : ℝ) - a) / 2 : ℝ) : ℂ)) ^ m * ((b : ℂ)⁻¹) ^ m := by
  have hx : ((((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ))⁻¹ = (q : ℂ) ^ ((((1 : ℝ) - a) / 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg q), Complex.ofReal_natCast, ← Complex.cpow_neg]
    congr 1
    push_cast
    ring
  rw [zpow_neg, ← inv_zpow, mul_inv, ← hx, mul_zpow]

theorem UpperTheory.Gal.TP.Sub.satPol_holds :
    SatPol := by
  intro E Ω _ _ _ _ _ A w h a B g
  rw [GlobalTheory.SatChar.charPol_satWD]
  unfold unrPol algSat
  simp only [bind, pure, Multiset.bind_singleton, Multiset.map_map, Function.comp_def]
  congr 1
  refine Multiset.map_congr rfl fun b _ => ?_
  rw [satPol_val]
