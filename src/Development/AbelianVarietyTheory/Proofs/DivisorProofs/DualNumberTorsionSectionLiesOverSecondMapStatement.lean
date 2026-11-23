module

public import Mathlib.Algebra.DualNumber
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberTorsionSectionLiesOverSecondMap
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.dualNumber_torsionSection_lies_over_second_map : ∀ (k : Type) [Field k] {S : Scheme.{0}} (G' : Over (Sp (DualNumber k))) [GrpObj G'], IsAbelianScheme G' → ∀ (G : Over S) [GrpObj G] (g₁ g₂ : Sp (DualNumber k) ⟶ S) (φ₁ φ₂ : G'.left ⟶ G.left), IsGrpPullback G' G g₂ φ₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ G'.left) (y : Z ⟶ Sp k), x ≫ G'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ φ₁ = x ≫ φ₂) → spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ g₁ = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ g₂ → ∀ (n : ℕ), (n : k) ≠ 0 → ∀ (σ : 𝟙_ (Over S) ⟶ G), σ ^ n = 1 → ∀ (x : 𝟙_ (Over (Sp (DualNumber k))) ⟶ G'), x ^ n = 1 → x.left ≫ φ₁ = g₁ ≫ σ.left → x.left ≫ φ₂ = g₂ ≫ σ.left := by
  first | exact @GlobalTheory.UCanon.torsion_sec_over_second | exact GlobalTheory.UCanon.torsion_sec_over_second | (intros; apply GlobalTheory.UCanon.torsion_sec_over_second <;> assumption)
