module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

theorem comp_opens_toSpecΓ_eq_valMap {C : Type} [CommRing C] {X : Scheme.{0}} (U : X.Opens)
    (eta : Sp C ⟶ U.toScheme) (h : ⊤ ≤ (eta ≫ U.ι) ⁻¹ᵁ U) :
    eta ≫ U.toSpecΓ = Spec.map (valMap (eta ≫ U.ι) U h) := by
  have e : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := fun z _ => z.2
  rw [← appLE_valMap eta U.ι e (le_preimage_top eta) h, Scheme.Opens.toSpecΓ, ← Category.assoc,
    Scheme.toSpecΓ_naturality, Spec.map_comp, valMap, Spec.map_comp]
  have h1 : (Sp C).toSpecΓ = Spec.map (Scheme.ΓSpecIso (CommRingCat.of C)).hom := by
    rw [← Scheme.isoSpec_Spec_hom]; rfl
  have h2 : U.topIso.inv = U.ι.appLE U ⊤ e := by
    rw [Scheme.Opens.ι_appLE]; rfl
  rw [h1, h2]
  rfl

theorem exists_hom_spec_of_le_ringOn :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (R : Subalgebra o Ω), (U₀ : Set M.Z).Nonempty → R ≤ M.ringOn U₀ → ∃ u₀ : U₀.toScheme ⟶ Sp R, ∀ eta : Sp Ω ⟶ U₀.toScheme, eta ≫ U₀.ι = M.pt → eta ≫ u₀ = spMap R.val.toRingHom := by
  intro o Ω _ _ _ M U R hU hR
  let ψ : R →+* Γ(M.Z, U) :=
    (M.sectionsEquiv U hU).symm.toRingHom.comp (Subalgebra.inclusion hR).toRingHom
  refine ⟨U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ), fun eta he => ?_⟩
  have h : ⊤ ≤ (eta ≫ U.ι) ⁻¹ᵁ U := he ▸ M.top_le_preimage_pt hU
  rw [← Category.assoc, comp_opens_toSpecΓ_eq_valMap U eta h, ← Spec.map_comp]
  congr 1
  ext a
  have e : (M.sectionsEquiv U hU (ψ a) : Ω) = a :=
    congrArg Subtype.val ((M.sectionsEquiv U hU).apply_symm_apply _)
  rw [coe_sectionsEquiv, ← he, valF_eq_valR, valR_eq _ U h] at e
  exact e

end GlobalTheory.ZH.RatModel
end
