module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB

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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ValInj

theorem valR_top_comp (R : Type) [CommRing R] (G : Over (Sp R)) (Ω : Type) [CommRing Ω] (φ : R →+* Ω)
    (x' : Sp Ω ⟶ G.left) (hx : x' ≫ G.hom = spMap φ) (r : R) :
    valR x' ⊤ (G.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = φ r := by
  have ht : ⊤ ≤ x' ⁻¹ᵁ (⊤ : G.left.Opens) := fun _ _ => trivial
  unfold valR
  rw [dite_eq_left ht]
  have h1 : (x'.appLE ⊤ ⊤ ht).hom (G.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
      (spMap φ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    rw [← hx]
    rw [Scheme.Hom.comp_appTop]
    rfl
  rw [h1]
  have h2 := congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.comp_apply] at h2
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, Iso.inv_hom_id_apply] at h2
  exact h2

theorem injective_of_val (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (Ω : Type) [CommRing Ω] (φ : R →+* Ω)
    (x' : Sp Ω ⟶ G.left) : x' ≫ G.hom = spMap φ →
    (∀ (O : G.left.Opens) (f : Γ(G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → Function.Injective φ := by
  intro hx hv
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro r hr
  have hf := hv ⊤ _ (fun _ _ => trivial) ((valR_top_comp R G Ω φ x' hx r).trans hr)
  have he : (η[G]).left ≫ G.hom = 𝟙 _ := by
    rw [Over.w (η[G])]
    rfl
  have h3 : (η[G]).left.appTop.hom (G.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, he]
    rfl
  rw [hf, map_zero] at h3
  have h4 := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom h3
  simpa using h4.symm

end GlobalTheory.ValInj
