module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSelF
public import Formalism.LocalToGlobal.ClassOfRecordOfChoice
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClassOfRecordOfChoice
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GTiedFOfC2S
public import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.AdmissibleClasses.LinkGCl
public import Formalism.LocalToGlobal.GroupLattices.LinkGConcreteNoKer
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
noncomputable section
namespace Formalism.L2.DIV.LinkGCl
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.L2.Top3
variable {eps : ℝ}
theorem gTiedF_of_sel_alt (Fm : FamP eps) (s : _root_.Formalism.L2.TwistSelectionFunctions Fm) : Formalism.L2.G.GroupCompatibilityFamily Fm :=
  _root_.Formalism.L2.gTiedF_of_C2S_alt Fm (_root_.Formalism.L2.Top3.tied_families_of_choice_alt s)
theorem closed_linkG (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) : Closed (D3 3 𝒜) fun Fm _ => LinkG Fm :=
  Formalism.L2.G.linkG_concrete5 (D3 3 𝒜)
    (Closed.of_class fun Fm _ hc => _root_.Formalism.L2.DIV.LinkGCl.gTiedF_of_sel_alt Fm (sel Fm (d3_a hc)))
    (Closed.of_class fun Fm _ hc => admissible_tops_of_class Fm hc)
theorem closed_linkG_of_tuSize_dGamSize (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) :
    Closed (D3 3 𝒜) fun Fm _ => ∀ _ : D3 3 𝒜 Fm, Formalism.MainNotions.TuSize Fm → Formalism.MainNotions.DGamSize Fm → LinkG Fm :=
  (_root_.Formalism.L2.DIV.LinkGCl.closed_linkG 𝒜 sel).imp fun _ _ _ h _ _ _ => h
end Formalism.L2.DIV.LinkGCl
end
end
