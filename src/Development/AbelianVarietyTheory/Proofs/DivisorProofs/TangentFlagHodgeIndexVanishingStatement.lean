module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFlagHodgeIndexVanishing
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

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

theorem _root_.GlobalTheory.T.tangent_flag_hodge_index_vanishing : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (ι : Type) [Fintype ι] [DecidableEq ι] (X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → X ≫ Xo.s = sOf c _ → spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X = y.x → ∀ N : ι → GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K, (∀ k, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y (spMap (GlobalTheory.FlagTan.dir c (Pi.single k (1 : K))).toRingHom ≫ X) (N k)) → ∀ M : ι → K, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) (∑ k, M k • N k) := by
  first | exact @GlobalTheory.FlagTan.isKS_dir_sum | exact GlobalTheory.FlagTan.isKS_dir_sum | (intros; apply GlobalTheory.FlagTan.isKS_dir_sum <;> assumption)
