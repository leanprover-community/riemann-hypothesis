module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CompatibleThetaRestrictions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilConstantTermSourceTargetConjAdjointCorr
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weilConstantTerm_source_target_conjAdjoint_corr : ∀ (D : D7) (S T T' : HSp D) (t : ℕ) (ι : T'.V →ₗ[D.host.E] T.V) (C : Matrix (Fin T.rank) (Fin t) D.host.E), (∀ μ 𝓖, IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ratMx D t S.rank) μ 𝓖 → ∃ μ' 𝓖', IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ratMx D S.rank t) μ' 𝓖' ∧ ∀ φ : WO S T → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resS T T' S ι C μ' 𝓖' (GlobalTheory.PairLift.dag S T φ) = GlobalTheory.PairLift.dag S T' (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT S T T' ι C μ 𝓖 φ)) ∧ ∀ μ' 𝓖', IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ratMx D S.rank t) μ' 𝓖' → ∃ μ 𝓖, IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ratMx D t S.rank) μ 𝓖 ∧ ∀ φ : WO S T → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resS T T' S ι C μ' 𝓖' (GlobalTheory.PairLift.dag S T φ) = GlobalTheory.PairLift.dag S T' (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT S T T' ι C μ 𝓖 φ) := by
  first | exact @GlobalTheory.TwistSwap.res_dag_swap | exact GlobalTheory.TwistSwap.res_dag_swap | (intros; apply GlobalTheory.TwistSwap.res_dag_swap <;> assumption)
