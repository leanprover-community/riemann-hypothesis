module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalSiegelObjectExtensionAbelianLocus
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_principalSiegelObject_extension_abelianLocus : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R] (b : cycAway n →+* R) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → ∀ (p : Sp R) [p.asIdeal.IsPrime], IsAbelianScheme ((Over.pullback (spMap (algebraMap R (Localization.AtPrime p.asIdeal)))).obj G₁) → ∀ (κ : Sp (FractionRing R) ⟶ Sp (Localization.AtPrime p.asIdeal)) (s' : Sp (Localization.AtPrime p.asIdeal) ⟶ Sp (cycAway n)), κ ≫ spMap (algebraMap R (Localization.AtPrime p.asIdeal)) = jK R → κ ≫ s' = y ≫ F.s → ∃ (c : SiegPre g n (zetaAway n) s') (c' : SiegPre g n (zetaAway n) (y ≫ F.s)), c.Principal ∧ SiegPB c' c κ ∧ SiegPB c' F.univ y := by
  first | exact @GlobalTheory.SiegExtend.exists_principal_extension | exact GlobalTheory.SiegExtend.exists_principal_extension | (intros; apply GlobalTheory.SiegExtend.exists_principal_extension <;> assumption)
