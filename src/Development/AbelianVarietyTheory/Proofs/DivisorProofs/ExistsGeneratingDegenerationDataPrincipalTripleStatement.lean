module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingDegenerationDataPrincipalTriple
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_generating_degenerationData_principalTriple : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t : SAB H (Sp W)), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∃ g, SmoothOfRelativeDimension g t.G.hom) → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (x₀ : X → (𝟙_ (Over (Sp W)) ⟶ t.G)), (∀ y z, x₀ (y + z) = x₀ y * x₀ z) → (∀ (a : 𝓞 E) y, x₀ (a • y) = x₀ y ≫ t.act.act a) → ∃ (D : DegPre W) (_ : Module (𝓞 E) D.X) (oa : letI := H.starRing; D.OAct (𝓞 E)) (φB : t.G.left ⟶ D.P.A.left) (e : X ≃ₗ[𝓞 E] D.X), D.PsiEven ∧ D.TauBimult ∧ (∀ y, PsiUnitOn D y Set.univ) ∧ (letI := H.starRing; TraceFormTwistIso D oa H.w0) ∧ IsAbPart t D oa φB ∧ ∀ y, (x₀ y).left ≫ φB = (D.c (e y)).left := by
  first | exact @GlobalTheory.UBaseData.main | exact GlobalTheory.UBaseData.main | (intros; apply GlobalTheory.UBaseData.main <;> assumption)
