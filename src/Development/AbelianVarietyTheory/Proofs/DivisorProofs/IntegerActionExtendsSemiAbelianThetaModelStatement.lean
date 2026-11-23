module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegerActionExtendsSemiAbelianThetaModel
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.integerAction_extends_semiAbelian_thetaModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → ∃ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) ∧ ∀ (K : Type) [Field K] (ξ₀ : Sp K ⟶ U₀.toScheme) (y : Sp K ⟶ Xo.XF c), X₁.Lies (ξ₀ ≫ out.u₀) y → ∀ (tK : SAB H (Sp K)), Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _)) → ∃ γ : tK.G.left ⟶ out.G.left, IsGrpPullback tK.G out.G (ξ₀ ≫ U₀.ι) γ ∧ LBIso tK.PP.L (out.L.L.pull γ) ∧ ∀ a, (tK.act.act a).left ≫ γ = γ ≫ (f a).left := by
  first | exact @GlobalTheory.UPoinc.act_extends_ratModel | exact GlobalTheory.UPoinc.act_extends_ratModel | (intros; apply GlobalTheory.UPoinc.act_extends_ratModel <;> assumption)
