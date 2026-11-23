module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueRelationSectionsThroughGeneratingIso
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.pointValue_relation_sections_through_generating_iso : ∀ (Y X₁ X₂ : Scheme.{0}) (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (k : ℕ) (σ' : SecM (𝟙 X₁) L₁ k) (s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ)))), (∀ (y : Y) (i : L₂.ι) (j : L₁.ι), f₂ y ∈ L₂.U i → f₁ y ∈ L₁.U j → gs (𝟙 Y) y _ (s.f fun _ => i) = (gs (𝟙 Y) y _ (w.s (fun _ => i, fun _ => j)).val) ^ k * gs f₁ y _ (σ'.f fun _ => j)) → ∀ (F : Type) [CommRing F] [IsLocalRing F] (ξ : Sp F ⟶ Y) (i : L₂.ι) (j : L₁.ι), ⊤ ≤ (ξ ≫ f₂) ⁻¹ᵁ L₂.U i → ⊤ ≤ (ξ ≫ f₁) ⁻¹ᵁ L₁.U j → valR ξ _ (s.f fun _ => i) = (valR ξ _ (w.s (fun _ => i, fun _ => j)).val) ^ k * valR (ξ ≫ f₁) _ (σ'.f fun _ => j) := by
  first | exact @GlobalTheory.GermVal.valR_linComb_germ | exact GlobalTheory.GermVal.valR_linComb_germ | (intros; apply GlobalTheory.GermVal.valR_linComb_germ <;> assumption)
