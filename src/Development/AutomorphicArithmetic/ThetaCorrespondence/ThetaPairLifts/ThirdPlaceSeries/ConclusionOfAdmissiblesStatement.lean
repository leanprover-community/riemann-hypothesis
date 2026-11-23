module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalGlobalCompatibility
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConclusionOfAdmissibles
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section



section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

theorem _root_.GlobalTheory.T.admT_of_artin_reciprocity_and_local_conditions : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (P : Pend D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) (CT : ℕ), 8 * (CT : ℝ) ≤ C → SumRepresentations.adm5 D → EigSpan P → TieInePoly D → admT (D := D) CT → LocalPushoutProposition (D := D) → ResidualAbsIrreducible (D := D) → TypePrimeChoiceLemmas (D := D) → admDZ P → _root_.Formalism.MainNotions.PairedCharacterCondition.GaloisFamilyConditions' (D := D) → admG5 (D := D) → admG6 (D := D) → GlobalTheory.TypeLeaf.SerLoc D → admTB (D := D) HW F → admBK (D := D) → admBC (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.LocalGlobalCompatibility' (D := D) → SumRepresentations.tie0 D → tieChi (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) C CT := by
  first | exact @_root_.GlobalTheory.admT_of_adm5_eigSpan_tieInePoly | exact _root_.GlobalTheory.admT_of_adm5_eigSpan_tieInePoly | (intros; apply _root_.GlobalTheory.admT_of_adm5_eigSpan_tieInePoly <;> assumption)
end
