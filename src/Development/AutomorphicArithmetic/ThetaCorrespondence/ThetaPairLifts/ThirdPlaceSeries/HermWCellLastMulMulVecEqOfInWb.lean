module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
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
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
namespace GlobalTheory.Fc.RL.PrimAt
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL}
theorem of_wit_alt {K : Ctx} {q : WPt p.s K} {c : ℝ} {b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c} (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : _root_.GlobalTheory.Fc.R1.PrimitivityBundleCondition _ _ c b := by
  have h : (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => Formalism.IndefR.Links.PrimRows3 r.B.Q.Rl r.B.Q.F ∧ r.P.A3.fam3.TypesSep3) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput w.y.y) :=
    ⟨w.y.intersectionNumber_baseChange.prim, w.y.intersectionNumber_baseChange.sep⟩
  rw [← w.y.eq] at h
  exact h
theorem herm_wCell_last_mul_mulVec_eq_of_inWb (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (Q : V4.Slot) : _root_.GlobalTheory.Fc.R1.SlotPrimitivityCondition Q (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) := by
  refine RowE.row (R := _root_.GlobalTheory.Fc.R1.PrimitivityBundleCondition) (RowE.of_all fun κ K β c b _ _ hl => ?_)
  obtain ⟨q, b', ⟨w⟩, he⟩ := hl
  have := congrArg (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => _root_.GlobalTheory.Fc.R1.PrimitivityBundleCondition s.1 s.2.1 c s.2.2) he
  exact cast this.symm (_root_.GlobalTheory.Fc.RL.PrimAt.of_wit_alt w)
theorem linkedAt_hPA : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP),
    _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotPrimitivityCondition :=
  fun _ N S Γ => _root_.GlobalTheory.Fc.RL.LinkedAt.of_row (_root_.GlobalTheory.Fc.RL.PrimAt.herm_wCell_last_mul_mulVec_eq_of_inWb (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _)
end GlobalTheory.Fc.RL.PrimAt
end
end
