module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallnessCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaAtSmallPlace
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
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
namespace GlobalTheory.FrameOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Int
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {l : ℕ} [Fact l.Prime]
end Int
end GlobalTheory.FrameOf
namespace GlobalTheory.FrameOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Pt
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
theorem kapSt_alt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → KapAt p j P w :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ =>
    ⟨0, fun _ _ _ _ p _ _ j P _ _ _ w _ _ _ => kapAt p j P w⟩⟩⟩
end Pt
end GlobalTheory.FrameOf
end
end
