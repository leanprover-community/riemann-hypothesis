module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CountsIrreducibilityConstants
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountConstantsOfSiegelWeil
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IrreducibilityRowOfConcreteAutomorphicDataStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsFinDimLink
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsWt
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



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2
  GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.Cp
namespace GlobalTheory.CountRow
theorem row_counts_of_ties_alt : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition),
    Row Q Lk (AtAll fun D _ _ _ => ∃ (X : HidaSetting D) (G : GoodOp X) (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X),
      AutTie D X.B X.pl ∧ RowDictTie X G ι ∧ GlobalTheory.LabPin.LabTie X ι) → _root_.GlobalTheory.Fc.R1.CountsIrreducibilityConstants' Q Lk := by
  intro hSW Q Lk hrow
  obtain ⟨c30, -, h1, -, -, h4⟩ := GlobalTheory.CountConstants.count_constants_of_siegelWeil hSW
  obtain ⟨cIc, hc, H⟩ := GlobalTheory.T.irreducibilityRow_of_concreteAutomorphicData hSW GlobalTheory.rowsFinDim_link
  refine ⟨c30, cIc, h1, hc, hrow.imp fun 𝒜 σ _ hA => ⟨?_, ?_⟩⟩
  · exact Formalism.MainNotions.Pk.Closed.of_class fun Fm _ _ => h4 _ Fm
  · exact H (D3 3 𝒜) (fun Fm hw => hw.2.2.1)
      (Formalism.MainNotions.Pk.Closed.of_class fun Fm _ hw _ => ⟨0, fun x hx _ i => hA Fm (d3_a hw) x hx i⟩)
end GlobalTheory.CountRow
end
