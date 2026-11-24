module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantUnitPulledBackBundleAutomorphism
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_constant_unit_pulledBack_bundle_automorphism : ∀ (A : Type) [CommRing A] (B' : Over (Sp A)) [GrpObj B'], IsAbelianScheme B' → ∀ {X Y : Scheme.{0}} (L : LB X) (M₀ : LB Y) (β : X ⟶ Y) (wF : LB.Iso L (M₀.pull β)) (π₁ π₂ : B'.left ⟶ X) (w : LB.Iso (L.pull π₁) (L.pull π₂)), L.IsLB → M₀.IsLB → wF.IsGen → w.IsGen → π₁ ≫ β = π₂ ≫ β → ∃ u : Aˣ, ∀ (p : Sp A ⟶ B'.left), p ≫ B'.hom = 𝟙 _ → ∀ (zz : Sp A) (J : (Sp A ⟶ X) → L.ι) (J₀ : (Sp A ⟶ Y) → M₀.ι), Good L zz J → Good M₀ zz J₀ → gm (p ≫ π₂) zz _ (wF.s (fun _ => J₀ (p ≫ π₂ ≫ β), J (p ≫ π₂))) * gm p zz _ (w.s (fun _ => J (p ≫ π₂), fun _ => J (p ≫ π₁))) = gm (𝟙 _) zz ⊤ (unitOn u) * gm (p ≫ π₁) zz _ (wF.s (fun _ => J₀ (p ≫ π₁ ≫ β), J (p ≫ π₁))) := by
  first | exact @GlobalTheory.PullAutConst.exists_unit | exact GlobalTheory.PullAutConst.exists_unit | (intros; apply GlobalTheory.PullAutConst.exists_unit <;> assumption)
