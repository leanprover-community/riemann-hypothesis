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
namespace GlobalTheory.CocVal

theorem valR_pos {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : valR x U f = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE U ⊤ h).hom f) := dif_pos h

theorem valR_map_le {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U V : X.Opens} (hVU : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    valR x V ((X.presheaf.map (homOfLE hVU).op).hom f) = valR x U f := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := h.trans (x.preimage_mono hVU)
  rw [valR_pos x V h, valR_pos x U hU]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem valR_mul_pos {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f * g) = valR x U f * valR x U g := by
  simp only [valR_pos x U h, map_mul]

theorem top_le_inf {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U V : X.Opens}
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ (U ⊓ V) :=
  fun p _ => ⟨hU trivial, hV trivial⟩

theorem valR_cocycle : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (F : Type) [Field F] (ξ : Sp F ⟶ X)
    (j j' j'' : L.ι), ⊤ ≤ ξ ⁻¹ᵁ L.U j → ⊤ ≤ ξ ⁻¹ᵁ L.U j' → ⊤ ≤ ξ ⁻¹ᵁ L.U j'' →
    valR ξ (L.U j ⊓ L.U j') (L.g j j').val * valR ξ (L.U j' ⊓ L.U j'') (L.g j' j'').val =
      valR ξ (L.U j ⊓ L.U j'') (L.g j j'').val := by
  intro X L hL F _ ξ j j' j'' h1 h2 h3
  have h123 : ⊤ ≤ ξ ⁻¹ᵁ (L.U j ⊓ L.U j' ⊓ L.U j'') := top_le_inf ξ (top_le_inf ξ h1 h2) h3
  have e := congrArg (fun u : Γ(X, L.U j ⊓ L.U j' ⊓ L.U j'')ˣ => valR ξ _ u.val) (hL.cocycle j j' j'')
  simp only [Units.val_mul] at e
  rw [valR_mul_pos ξ _ h123] at e
  simp only [res, Units.coe_map, MonoidHom.coe_coe] at e
  rw [valR_map_le ξ _ h123, valR_map_le ξ _ h123, valR_map_le ξ _ h123] at e
  exact e

end GlobalTheory.CocVal
