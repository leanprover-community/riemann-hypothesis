import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfRangeSubset
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory.AbelianNoTorsion

theorem finite_points_of_no_torsion : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ n : ℕ, 2 ≤ n → (n : k) ≠ 0 → (∀ x : 𝟙_ (Over (Sp k)) ⟶ A, x ^ n = 1 → x = 1) → Finite (𝟙_ (Over (Sp k)) ⟶ A) := by
  intro k _ _ A _ hA n hn hnk htor
  obtain ⟨p, hp, m, rfl⟩ := Nat.exists_prime_and_dvd (n := n) (by omega)
  have hpk : (p : k) ≠ 0 := fun h => hnk (by rw [Nat.cast_mul, h, zero_mul])
  have hfin : Finite (⊤ : Subgroup (𝟙_ (Over (Sp k)) ⟶ A)) :=
    GlobalTheory.AbelianSubgroupFinite.finite_of_no_torsion GlobalTheory.abMulN_holds k A p hA hp hpk ⊤ Set.univ
      isClosed_univ (fun x => ⟨fun _ => Set.subset_univ _, fun _ => Subgroup.mem_top x⟩)
      (fun x _ hx => htor x (by rw [pow_mul, hx, one_pow]))
  exact Finite.of_equiv _ Subgroup.topEquiv.toEquiv

end GlobalTheory.AbelianNoTorsion
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_points_abelianVariety_of_no_torsion : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ n : ℕ, 2 ≤ n → (n : k) ≠ 0 → (∀ x : 𝟙_ (Over (Sp k)) ⟶ A, x ^ n = 1 → x = 1) → Finite (𝟙_ (Over (Sp k)) ⟶ A) := by
  first | exact @GlobalTheory.AbelianNoTorsion.finite_points_of_no_torsion | exact GlobalTheory.AbelianNoTorsion.finite_points_of_no_torsion | (intros; apply GlobalTheory.AbelianNoTorsion.finite_points_of_no_torsion <;> assumption)
end
