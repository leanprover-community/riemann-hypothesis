module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Semichar
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.AhFrameFactorEqNegOnePowRiemannForm
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
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf

@[expose] public section

set_option autoImplicit false

namespace GlobalTheory

theorem semichar_unit_frame : ReciprocityTheory.ChartRestriction.G.PullbackSections.PPSemicharSt := by
  intro E _ _ _ H Dw l Xo c σ r U _ k x W Wu _ a
  have hF : GlobalTheory.EtaAn.AHFrame W.F (W.ik k) W.Pm Wu.Hm Wu.χl Wu.fr :=
    ⟨Wu.herm, Wu.pos, Wu.c1, Wu.c2, Wu.c3, Wu.c4, fun j hj => by
      rw [← W.pt]; exact Wu.c5 j hj, Wu.c6⟩
  have h : Wu.χl (W.Pm a) =
      ((Int.negOnePow ((W.F.Di (W.ik k)).EF a (H.w0 • a)) : ℤˣ) : ℤ) :=
    GlobalTheory.ahFrame_factor_eq_negOnePow E H Dw l Xo _ _ _ W.F (W.ik k) W.Pm Wu.Hm Wu.χl Wu.fr W.per hF a
  rw [h, Int.cast_negOnePow]

end GlobalTheory
