module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.InnerAutActsTriviallyGroupHomology
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab.ConjMap

noncomputable def actHom {k G : Type} [CommRing k] [Group G] (B : Rep k G) (g : G) :
    B ⟶ Rep.res (MulAut.conj g).toMonoidHom B :=
  Rep.ofHom (X := B.V) (Y := B.V) (ρ := B.ρ) (σ := (Rep.res (MulAut.conj g).toMonoidHom B).ρ)
    ⟨B.ρ g, fun h => by ext x; simp [Rep.res]⟩

lemma actHom_apply {k G : Type} [CommRing k] [Group G] (B : Rep k G) (g : G) (x : B) :
    (actHom B g).hom x = B.ρ g x := rfl

end GlobalTheory.HomStab.ConjMap

open GlobalTheory.HomStab.ConjMap in
theorem GlobalTheory.HomStab.groupHomology_map_conj : ∀ (k G H : Type) [CommRing k] [Group G] [Group H] (A : Rep k H) (B : Rep k G) (f₁ f₂ : H →* G) (u₁ : A ⟶ Rep.res f₁ B) (u₂ : A ⟶ Rep.res f₂ B) (g : G), (∀ h, f₂ h = g * f₁ h * g⁻¹) → (∀ a, u₂.hom a = B.ρ g (u₁.hom a)) → ∀ n : ℕ, groupHomology.map f₂ u₂ n = groupHomology.map f₁ u₁ n := by
  intro k G H _ _ _ A B f₁ f₂ u₁ u₂ g hf hu n
  have hf' : f₂ = (MulAut.conj g).toMonoidHom.comp f₁ := by
    ext h; simp [hf h]
  have e : groupHomology.map f₂ u₂ n =
      groupHomology.map ((MulAut.conj g).toMonoidHom.comp f₁)
        (u₁ ≫ (Rep.resFunctor f₁).map (actHom B g)) n := by
    apply groupHomology.map_congr hf'
    ext a
    simp [hu a, actHom_apply]
    rfl
  rw [e, groupHomology.map_comp, GlobalTheory.T.innerAut_acts_trivially_groupHomology k G g n B (actHom B g) (fun a => rfl),
    Category.comp_id]

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
end
