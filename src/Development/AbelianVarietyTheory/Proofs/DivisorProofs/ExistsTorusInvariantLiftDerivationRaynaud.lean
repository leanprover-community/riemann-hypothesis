module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFormSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationLiftRaynaudPreimageAffineStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldExtendingAffineDerivationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightPreservingLiftOfBaseDerivationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageProjectionAbelianPartStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPreservingVectorFieldOnSmallerPreimagesStatement
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

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.Heat.HxLift

theorem exists_invLift : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (D : Derivation ℤ R R), ∃ d : Fld Y.H.left, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V.1) d ∧ ∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V.1 → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d _ f) := by
  intro R _ _ Q O _ _ _ oa Y V D
  obtain ⟨δ₀, h0a, h0m, h0c⟩ := GlobalTheory.T.exists_derivation_lift_raynaud_preimage_affine R Q O oa Y V D
  obtain ⟨δ, ha, hm, hc, hw⟩ := GlobalTheory.T.exists_weight_preserving_lift_of_base_derivation R Q O oa Y V D δ₀ h0a h0m h0c
  obtain ⟨d, hd, hdU⟩ := GlobalTheory.T.exists_vectorField_extending_affineDerivation Y.H.left _ (GlobalTheory.T.isAffineOpen_preimage_projection_abelianPart R Q O oa Y V) δ ha hm
  refine ⟨d, ⟨hd, fun O' hO' r => ?_⟩, ?_⟩
  · rw [← GlobalTheory.ZH.FormSec.res_constFn Y.H.hom hO' r, ← GlobalTheory.ZH.FormSec.res_constFn Y.H.hom hO' (D r),
      hd.2.2 _ _ hO' le_rfl, hdU, hc]
  · refine GlobalTheory.T.weight_preserving_vectorField_on_smaller_preimages R Q O oa Y V d hd (fun α f hf => ?_)
    rw [hdU]
    exact hw α f hf

end GlobalTheory.Heat.HxLift
