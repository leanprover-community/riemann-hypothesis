module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryUniformisationBaseChangeInjective
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

theorem _root_.GlobalTheory.T.exists_unitaryUniformisation_baseChange_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (t : SAB H (Sp V)) (y : Sp (FractionRing V) ⟶ Xo.XF c) (P : PELUnif (maximalIdeal V) t), GenOf Xo c y t → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁) (fK : FractionRing V →+* FractionRing V₁), IsCN V₁ → Function.Injective ρ → IsLocalHom ρ → (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (ρ a)) → ∃ (t₁ : SAB H (Sp V₁)) (P₁ : PELUnif (maximalIdeal V₁) t₁) (p : IsPullDeg ρ P.D.toPre P₁.D.toPre), GenOf Xo c (spMap fK ≫ y) t₁ ∧ (∀ (a : 𝓞 E) x, p.xe (a • x) = a • p.xe x) ∧ ∀ x r, Formalism.L2.Pj.PsiCoord P.D.toPre (p.xe x) r → ∃ w : V₁ˣ, Formalism.L2.Pj.PsiCoord P₁.D.toPre x (w * ρ r) := by
  first | exact @GlobalTheory.USepBC.exists_pelUnif_baseChange_of_injective | exact GlobalTheory.USepBC.exists_pelUnif_baseChange_of_injective | (intros; apply GlobalTheory.USepBC.exists_pelUnif_baseChange_of_injective <;> assumption)
