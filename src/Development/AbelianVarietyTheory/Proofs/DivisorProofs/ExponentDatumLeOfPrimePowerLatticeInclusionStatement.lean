module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentDatumLeOfPrimePowerLatticeInclusion
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

theorem _root_.GlobalTheory.T.exponent_datum_le_of_primePowerLatticeInclusion : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 : Type) (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K)) (J : ℕ), LIncl B ℓ Z w J → 0 ≤ B.JexpU ℓ Z w ∧ B.JexpU ℓ Z w ≤ J := by
  first | exact @GlobalTheory.ExpTie.jexpU_le_of_lIncl | exact GlobalTheory.ExpTie.jexpU_le_of_lIncl | (intros; apply GlobalTheory.ExpTie.jexpU_le_of_lIncl <;> assumption)
