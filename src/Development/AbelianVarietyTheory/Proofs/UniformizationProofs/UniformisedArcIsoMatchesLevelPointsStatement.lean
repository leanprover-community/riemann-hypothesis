module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisedArcIsoMatchesLevelPoints
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.uniformisedArc_iso_matches_levelPoints : Laws → Laws2 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ') (hD : IsPullDeg (RingHom.id (PowerSeries k)) W'.P.D.toPre W.P.D.toPre), ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ = W.φ ∧ (∀ x, hD.xe (W.e x) = W'.e x) ∧ ∃ w₁ : LB.Iso W.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ)), HEq w₁ W.w ∧ Tri W'.w hD.w w₁) → ∀ (ψ : W.t.G ≅ W'.t.G) (bc : W.t.G ≅ (Over.pullback (specOf (RingHom.id (PowerSeries k)))).obj W'.t.G), IsMonHom ψ.hom → IsMonHom bc.hom → bc.hom.left ≫ pullback.fst W'.t.G.hom (specOf (RingHom.id (PowerSeries k))) = ψ.hom.left → IsPullUnif (RingHom.id (PowerSeries k)) hD bc W'.P.U W.P.U → (∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) → ∀ (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c), y ≫ Y.j = jK (PowerSeries k) ≫ χ → y' ≫ Y'.j = jK (PowerSeries k) ≫ χ' → y ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → y' ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → (∀ (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (σ' : 𝟙_ (Over (Xo.XF c)) ⟶ Y'.oF.t.G), ((∃ v, σ = Y.oF.etaA v ∧ σ' = Y'.oF.etaA v) ∨ ∃ v, σ = Y.oF.eta v ∧ σ' = Y'.oF.eta v) → ∀ g : Sp (FractionRing (PowerSeries k)) ⟶ W.t.G.left, g ≫ W.t.G.hom = jK (PowerSeries k) → g ≫ W.m.φ = y ≫ σ.left ≫ Y.m.φ → g ≫ ψ.hom.left ≫ W'.m.φ = y' ≫ σ'.left ≫ Y'.m.φ) := by
  first | exact @GlobalTheory.ArcLevel.level_match | exact GlobalTheory.ArcLevel.level_match | (intros; apply GlobalTheory.ArcLevel.level_match <;> assumption)
