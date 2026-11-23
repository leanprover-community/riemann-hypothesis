module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPrimitiveScaling
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_primitive_scaling_alt : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V)) [GrpObj G], IsSemiAbelian G → ∀ (M : LB G.left), M.IsLB → ∀ (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (ψ : pullback G.hom (jK V) ⟶ Y) (w : LB.Iso (M.pull (pullback.fst G.hom (jK V))) (L.pull ψ)), w.IsGen → ∀ θ : LB.Sec L, (∃ z, ψ z ∈ nonzeroLocus θ) → ∃ (ϑ : H0 M 1) (c : FractionRing V), c ≠ 0 ∧ (∃ z ∈ nonzeroLocus ϑ, G.hom z = IsLocalRing.closedPoint V) ∧ ∀ x : Sp (FractionRing V) ⟶ pullback G.hom (jK V), x ≫ pullback.snd G.hom (jK V) = 𝟙 _ → ∀ (i : M.ι) (k : L.ι), ⊤ ≤ (x ≫ pullback.fst G.hom (jK V)) ⁻¹ᵁ M.U i → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U k → valR x _ (w.s (fun _ => k, fun _ => i)).val * valR (x ≫ pullback.fst G.hom (jK V)) _ (ϑ.f (fun _ => i)) = c * valR (x ≫ ψ) _ (θ.f k) := by
  first | exact @GlobalTheory.PrimScale.exists_primitive_scaling | exact GlobalTheory.PrimScale.exists_primitive_scaling | (intros; apply GlobalTheory.PrimScale.exists_primitive_scaling <;> assumption)
