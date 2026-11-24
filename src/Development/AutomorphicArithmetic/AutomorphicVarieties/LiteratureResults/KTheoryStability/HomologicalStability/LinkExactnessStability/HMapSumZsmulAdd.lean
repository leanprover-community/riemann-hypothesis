module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PermRepSingle
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

theorem chainsMap_id_add {k G : Type} [CommRing k] [Group G] {A B : Rep k G} (f g : A ⟶ B) :
    groupHomology.chainsMap (MonoidHom.id G) (f + g) =
      groupHomology.chainsMap (MonoidHom.id G) f + groupHomology.chainsMap (MonoidHom.id G) g := by
  ext n : 1
  apply groupHomology.inhomogeneousChains.ext
  intro x
  ext a : 2
  simp only [groupHomology.chainsMap_f_single, HomologicalComplex.add_f_apply]
  simp [groupHomology.chainsMap_f_single]
  rw [← Finsupp.single_add]
  rfl

theorem hMap_add {k G : Type} [CommRing k] [Group G] {A B : Rep k G} (f g : A ⟶ B) (n : ℕ) :
    hMap (f + g) n = hMap f n + hMap g n := by
  unfold hMap groupHomology.map
  rw [chainsMap_id_add, HomologicalComplex.homologyMap_add]

noncomputable def hMapHom {k G : Type} [CommRing k] [Group G] (A B : Rep k G) (n : ℕ) :
    (A ⟶ B) →+ (groupHomology A n ⟶ groupHomology B n) :=
  AddMonoidHom.mk' (fun f => hMap f n) fun f g => hMap_add f g n

theorem hMap_additive : ∀ (k G : Type) [CommRing k] [Group G] (A B : Rep k G) (n : ℕ), (∀ f g : A ⟶ B, hMap (f + g) n = hMap f n + hMap g n) ∧ hMap (0 : A ⟶ B) n = 0 ∧ (∀ (m : ℤ) (f : A ⟶ B), hMap (m • f) n = m • hMap f n) ∧ ∀ (ι : Type) (T : Finset ι) (f : ι → (A ⟶ B)), hMap (∑ i ∈ T, f i) n = ∑ i ∈ T, hMap (f i) n := by
  intro k G _ _ A B n
  refine ⟨fun f g => hMap_add f g n, ?_, ?_, ?_⟩
  · exact map_zero (hMapHom A B n)
  · intro m f
    exact map_zsmul (hMapHom A B n) m f
  · intro ι T f
    exact map_sum (hMapHom A B n) f T

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.hMap_sum_zsmul_add : ∀ (k G : Type) [CommRing k] [Group G] (A B : Rep k G) (n : ℕ), (∀ f g : A ⟶ B, hMap (f + g) n = hMap f n + hMap g n) ∧ hMap (0 : A ⟶ B) n = 0 ∧ (∀ (m : ℤ) (f : A ⟶ B), hMap (m • f) n = m • hMap f n) ∧ ∀ (ι : Type) (T : Finset ι) (f : ι → (A ⟶ B)), hMap (∑ i ∈ T, f i) n = ∑ i ∈ T, hMap (f i) n := by
  first
  | exact @GlobalTheory.HomStab.hMap_additive
  | exact @GlobalTheory.HomStab.hMap_add
  | exact @GlobalTheory.HomStab.chainsMap_id_add
end
