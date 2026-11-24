module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FrameSqEqOfSymmetricThetaElement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.frame_sq_eq_of_symmetric_thetaElement : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), 1 ≤ N → ∀ (p : QkPt D.toPre F N) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)) (w₀ : W0 U.toUnifPre) (w : Frm D.toPre F N p.g.b), w₀.IsGen → w.IsGen → (∀ t t' s s', U.ExpandsF F N w₀ t s → U.ExpandsF F N w₀ t' s' → IsActOf A.A A.L N θ t t' → PhiRel D.toPre F N p w s s') → (∃ nu : LB.Gen (negLB A.A A.L N (TFK (R := R) F)), nu.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (symGen A.A A.L N θ nu) (LB.oneGen A.L)) → ∀ ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 4) ![(𝟙 D.toPre.P.A ^ (N + 1)).left, (𝟙 D.toPre.P.A ^ N).left, 𝟙 _, (1 : D.toPre.P.A ⟶ D.toPre.P.A).left] ![1, -1, -(2 * (N : ℤ) + 1), 2 * (N : ℤ) + 1]), Normd ν → ∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J ^ 2 = val (p.g.s p.y) (𝟙 _) z J * val ν p.g.b.left z J := by
  first | exact @GlobalTheory.SymFrame.sq_frame_of_symmetric | exact GlobalTheory.SymFrame.sq_frame_of_symmetric | (intros; apply GlobalTheory.SymFrame.sq_frame_of_symmetric <;> assumption)
