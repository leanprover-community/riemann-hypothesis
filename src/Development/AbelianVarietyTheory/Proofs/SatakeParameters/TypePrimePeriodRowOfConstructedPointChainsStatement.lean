module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetSplitAmb
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimePeriodRowOfConstructedPointChains
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc GlobalTheory.Mem.Top GlobalTheory.AtG

theorem _root_.GlobalTheory.T.typePrimePeriodRow_of_constructedPointChains : JetSplitAmb → ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd), RowE Q Lk (fun _ D O _ _ => ∀ μ, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) → TiesAt D O.ex.errX O.X μ) → Row Q Lk fun 𝒜 _ => Closed (W3 𝒜) fun Fm _ => ∃ C1, (∃ x0, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i, Formalism.L2.G.Adm2InU.UsedTuplesBoundByConstant (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1) ∧ WeightDegreeSizes.familySizeBoundAtTypePrime Fm C1 := by
  first | exact @GlobalTheory.AtG.row_atG_of_jetSplitAmb | exact GlobalTheory.AtG.row_atG_of_jetSplitAmb | (intros; apply GlobalTheory.AtG.row_atG_of_jetSplitAmb <;> assumption)
