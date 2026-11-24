module

public import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingBounds
public import Formalism.SharpRestriction.LevelLetterCocycles.LetterConditionGlobal
public import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremCConst25OfHypotheses
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.ramified_coefficient_chains_of_hypotheses : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (CR CA CB CK : ℝ), LiftingTheory.adm23 D HW F → Formalism.MainNotions.N.LetterConditionGlobal D HW F → ElementDenominator.HerrClassNaturalExtension D.loc D.locA HW F → CrystallineLiftingBounds.adm22 D HW F → InvariantsGenerators.LitFont D HW F → RamifiedCoefficientChains.Stmt D HW F Cm 25 CR CA CB CK := by
  first | exact @GlobalTheory.theoremC_of_admitted_inputs | exact GlobalTheory.theoremC_of_admitted_inputs | (intros; apply GlobalTheory.theoremC_of_admitted_inputs <;> assumption)
