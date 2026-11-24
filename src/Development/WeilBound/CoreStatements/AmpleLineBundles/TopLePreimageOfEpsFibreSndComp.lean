module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CoverDenseAlt

variable {Z : Scheme.{0}} {A A' : Type} [CommRing A] [CommRing A']

def val (z : Sp A ⟶ Z) (V : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ V) : Γ(Z, V) →+* A :=
  (z.appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom

theorem val_comp (φ : A →+* A') (z : Sp A ⟶ Z) (V : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ V) {z' : Sp A' ⟶ Z}
    (e : z' = spMap φ ≫ z) (h' : ⊤ ≤ z' ⁻¹ᵁ V) (s : Γ(Z, V)) :
    val z' V h' s = φ (val z V h s) := by
  subst e
  have h1 : (spMap φ ≫ z).appLE V ⊤ h' = z.appLE V ⊤ h ≫ (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have h2 : (spMap φ ≫ z).appLE V ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of A')).hom =
      z.appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom φ := by
    rw [h1, Category.assoc, Scheme.ΓSpecIso_naturality]
  unfold val
  rw [h2]
  rfl

theorem val_rep (z : Sp A ⟶ Z) {U : Z.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ z ⁻¹ᵁ U) :
    spMap (val z U h) ≫ hU.fromSpec = z := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec z hU (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at this
  change Spec.map (z.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom) ≫ hU.fromSpec = z
  rw [Spec.map_comp, Category.assoc, this, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.id_comp]

theorem val_ext {z z' : Sp A ⟶ Z} {U : Z.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ z ⁻¹ᵁ U)
    (h' : ⊤ ≤ z' ⁻¹ᵁ U) (e : ∀ s, val z U h s = val z' U h' s) : z = z' := by
  rw [← val_rep z hU h, ← val_rep z' hU h', RingHom.ext e]

theorem exists_affine {B : Type} [CommRing B] [IsLocalRing B] (z : Sp B ⟶ Z) :
    ∃ U : Z.Opens, IsAffineOpen U ∧ ⊤ ≤ z ⁻¹ᵁ U := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (z (IsLocalRing.closedPoint B))) isOpen_univ
  exact ⟨U, hU, (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of B) z hxU).ge⟩

theorem spMap_spMap {A'' : Type} [CommRing A''] (φ : A →+* A') (ψ : A' →+* A'') :
    spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  rw [← Spec.map_comp]; rfl

variable (J : Ideal A)

end CoverDenseAlt
