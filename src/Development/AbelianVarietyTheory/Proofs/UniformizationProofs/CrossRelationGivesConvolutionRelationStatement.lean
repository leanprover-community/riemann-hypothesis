module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
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

theorem _root_.GlobalTheory.T.crossRelation_gives_convolution_relation : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (E : EndU U.toUnifPre) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (j j' : ℕ), 1 ≤ j → 1 ≤ j' → ∀ (t₁ t₂ : SecA A F j) (t₁' t₂' : SecA A F j') s₁ s₂ s₁' s₂', U.ExpandsF F j w₀ t₁ s₁ → U.ExpandsF F j w₀ t₂ s₂ → U.ExpandsF F j' w₀ t₁' s₁' → U.ExpandsF F j' w₀ t₂' s₂' → Cross E.aA t₁ t₂ t₁' t₂' → ∀ (g g' : GtPtF D.toPre F), E.Act g g' → ∀ (w : Frm D.toPre F j g'.b) (w' : Frm D.toPre F j' g.b), w.IsGen → w'.IsGen → ∀ α, SumF I F (fun p : {p : D.toPre.X × D.toPre.X // E.h p.1 + p.2 = α} => coef s₁ g' w p.1.1 * coef s₂' g w' p.1.2 - coef s₂ g' w p.1.1 * coef s₁' g w' p.1.2) 0 := by
  first | exact @GlobalTheory.UT.MixedConv.sumF_conv_of_cross | exact GlobalTheory.UT.MixedConv.sumF_conv_of_cross | (intros; apply GlobalTheory.UT.MixedConv.sumF_conv_of_cross <;> assumption)
