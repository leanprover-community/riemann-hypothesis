module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Formalism.LocalToGlobal.GlobalTheory.IrreducibleOfCountSizes
public import Formalism.LocalToGlobal.HilbertRowConditions.AllJoin
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IrreducibilityRowOfConcreteAutomorphicData
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.GlobalTheoryTheory.ConcN Formalism.L2.GlobalTheoryTheory.AllJoin Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2

theorem _root_.GlobalTheory.T.irreducibilityRow_of_concreteAutomorphicData : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.RowsDef.RowsFinDim → ∃ cIc : ℝ, 0 < cIc ∧ ∀ 𝒞 : FamClass, (∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TuSize Fm) → (Closed 𝒞 fun Fm _ => 𝒞 Fm → ∃ x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x → ∀ i : Fm.Ix x, ∃ (X : HidaSetting (Fm.D x i)) (G : GoodOp X) (ι : (Fm.D x i).s.HH ≃ₗᵢ[ℂ] HHX X), AutTie (Fm.D x i) X.B X.pl ∧ RowDictTie X G ι ∧ GlobalTheory.LabPin.LabTie X ι) → Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : AllRows (Fm.D x i), LabelCountGoodInjective A ∧ AllJoinA A ∧ CountAllRows A (epsC cIc (Fm.D x i).R.r (Fm.D x i).R.f) := by
  exact GlobalTheory.IrrRowConcrete.irr_row_closed
