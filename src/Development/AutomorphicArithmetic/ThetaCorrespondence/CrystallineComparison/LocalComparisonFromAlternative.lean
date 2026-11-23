module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.CFDefs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.ZD
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.LocTied6
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.CFIncl
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.CFPlain
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.LocTied6OfCmp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.LocalComparisonOfComparison
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.LogarithmCompat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.CmpTie

open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

theorem compat_F (l : ℕ) [Fact l.Prime] : Compat l (equivCrystalline l) (equivDeRham l) (equivDeRhamPlus l) :=
  ⟨integer_to_crystalline_compat l, integer_to_deRham_compat l, deRham_plus_algebraMap_compat l, theta_deRham_compat l, galois_action_crystalline_compat l, galois_action_deRham_compat l, frobenius_crystalline_compat l, crystalline_deRham_inclusion_compat l, filtration_deRham_compat l, fun AI y => logarithm_compat l AI y,
    ainf_to_crystalline_compat l⟩

theorem cmp_F (l : ℕ) [Fact l.Prime] : Cmp l := ⟨_, _, _, compat_F l⟩

theorem locTied6_F : ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (P : Formalism.BasicNotions.LocPrime l) (AI : Formalism.BasicNotions.LocAinf l P),
    Nonempty (Formalism.BasicNotions.LocTied l P AI) → Nonempty (Formalism.BasicNotions.LocTied6 l P AI) :=
  fun l _ P AI => locTied6_of_cmp (cmp_F l) P AI

theorem local_comparison_from_alternative : ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (P : Formalism.BasicNotions.LocPrime l) (AI : Formalism.BasicNotions.LocAinf l P),
    Nonempty (Formalism.BasicNotions.LocTied6 l P AI) → Nonempty (Formalism.BasicNotions.LocTied l P AI) :=
  fun l _ P AI => local_comparison_of_comparison (cmp_F l) P AI

end Formalism.BasicNotions.CmpTie
