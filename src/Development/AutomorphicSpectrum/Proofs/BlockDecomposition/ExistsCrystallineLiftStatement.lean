module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.IsFirstChernClassOfLineBundle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCrystallineLift
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge

theorem _root_.GlobalTheory.T.exists_crystalline_lift : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b : Base} {ht : b.t = 1}
    {κ : O →+* b.R ⧸ b.I} {C : Type 1} [Category.{0} C] (G : C ⥤ Thick ((B.schFn q).cr b ht κ)) (D : E.LineData X),
    (∀ T, ∃ p : Spec (CommRingCat.of ((G.obj T).B ⧸ (G.obj T).J)) ⟶ D.Y, p ≫ D.f = B.thPt (G.obj T)) → Nonempty (B.CLift G D) := by
  first | exact @GlobalTheory.CompanionTheory.CLiftEx.nonempty_cLift | exact GlobalTheory.CompanionTheory.CLiftEx.nonempty_cLift | (intros; apply GlobalTheory.CompanionTheory.CLiftEx.nonempty_cLift <;> assumption)
