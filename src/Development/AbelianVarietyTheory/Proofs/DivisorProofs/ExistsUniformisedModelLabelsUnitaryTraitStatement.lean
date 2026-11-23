module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedModelLabelsUnitaryTrait
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_uniformisedModel_labels_unitaryTrait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (u' : Sp (ratHull S.R) ⟶ Xo.XF cf) (G : Over (Sp (ratHull S.R))) (_ : GrpObj G) (α : G.left ⟶ ρ.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ.P.A (spMap (toRat S.R)) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ.P.L.pull α) (Xo.univ.t.PP.L.pull β) → ∀ (p : ℕ) [Fact p.Prime] (y₁ : ratHull S.R →+* PadicAlgCl p) (T : UTrait Xo cf) (ι : FractionRing T.V →+* PadicAlgCl p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) → spMap y₁ ≫ u' = spMap ι ≫ T.y → (∀ a : o, ‖y₁ (toRat S.R (algebraMap o S.R a))‖ ≤ 1) → ∃ (u : ρ.UTest p (y₁.comp (toRat S.R))) (lb : u.Lab) (j : u.D.toPre.X ≃+ T.P.D.toPre.X), (∀ χ, lb.q χ = -Real.log ‖ι (algebraMap T.V (FractionRing T.V) T.ϖ)‖ * (T.be (j χ) (j χ) : ℝ) / 2) ∧ ∀ (m : ℕ) (a : 𝓞 E) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (w w' : Sp (PadicAlgCl p) ⟶ G.left), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → w ≫ α = x.left ≫ u.φ → w' ≫ α = x'.left ≫ u.φ → w' ≫ β = w ≫ β ≫ (Xo.univ.t.act.act a).left → CongMod m (j pk'.y) (a • j pk.y) := by
  first | exact @GlobalTheory.UPoinc.uTraitLabels | exact GlobalTheory.UPoinc.uTraitLabels | (intros; apply GlobalTheory.UPoinc.uTraitLabels <;> assumption)
