module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionPullbackSectionEndomorphism
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

theorem _root_.GlobalTheory.T.expansion_pullback_section_endomorphism : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (E : EndU U.toUnifPre), Function.Injective E.h → ∀ (k' k : ℕ), 1 ≤ k → 1 ≤ k' → (∃ β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 _, E.aG.left] ![(k' : ℤ), -(k : ℤ)]), β.IsGen) → (∃ κ : LB.Gen (kapLB D.toPre E.aB k' k), Normd κ) ∧ ∀ (w₀ : W0 U.toUnifPre) (ρ), NormW U.toUnifPre w₀ ρ → ∀ (ψ : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)) (m : (TFK (R := R) F ⊗ A.A) ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ≫ E.aA → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![(k' : ℤ), -(k : ℤ)])), α.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := R) F) ((k' : ℤ) - k)) → ∀ (t : SecA A F k) (t' : SecA A F k') s s', U.ExpandsF F k w₀ t s → U.ExpandsF F k' w₀ t' s' → IsTwistPull A.A A.L ψ m hm k' k α t t' → ∀ κ : LB.Gen (kapLB D.toPre E.aB k' k), Normd κ → ∀ (g g' : GtPtF D.toPre F), E.Act g g' → ∀ (w' : Frm D.toPre F k' g.b) (w : Frm D.toPre F k g'.b), w'.IsGen → w.IsGen → (∀ z J, Good D.toPre.P.L z J → val w' (𝟙 _) z J * val κ g.b.left z J = val w (𝟙 _) z J) → (∀ χ, coef s' g w' (E.h χ) = coef s g' w χ) ∧ ∀ β, β ∉ Set.range E.h → coef s' g w' β = 0 := by
  first | exact @GlobalTheory.UT.PullExp.main | exact GlobalTheory.UT.PullExp.main | (intros; apply GlobalTheory.UT.PullExp.main <;> assumption)
