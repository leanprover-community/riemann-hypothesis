import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyZeroStrictlyHenselianEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentKummerCupProductBijectiveStrictlyHenseliaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCohomologyVanishingOfNoetherianHenselianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentPolynomialTateTwistCohomologyVanishingInd

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentPolynomial_tateTwistCohomology_vanishing_inductive : ∀ (q : ℕ) [NeZero q] (n : ℤ), 2 ≤ n → (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) → ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Subsingleton (Ht q (sp (LaurentPolynomial A)) n i) := by
  first | (exact @GlobalTheory.EtC.GmStep.gm_vanishing_step) | (exact GlobalTheory.EtC.GmStep.gm_vanishing_step) | (intros; apply GlobalTheory.EtC.GmStep.gm_vanishing_step  <;> assumption)
end

section
namespace GlobalTheory.LaurentCohomologyVanishing

open GlobalTheory.EtC

theorem vanishing_below (q : ℕ) [NeZero q] (k : ℕ) :
    ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
      ∀ m i : ℤ, 2 ≤ m → m < 2 + (k : ℤ) → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i) := by
  induction k with
  | zero =>
    intro A _ _ _ _ m i h2 hm
    push_cast at hm
    omega
  | succ k ih =>
    intro A _ _ hA hq m i h2 hm
    push_cast at hm
    rcases lt_or_eq_of_le (show m ≤ 2 + (k : ℤ) by omega) with h | h
    · exact ih A hA hq m i h2 h
    · subst h
      exact GlobalTheory.T.laurentPolynomial_tateTwistCohomology_vanishing_inductive q (2 + k) (by omega) ih A hA hq i

theorem laurent_cohomology (q : ℕ) [NeZero q] (A : Type) [CommRing A] (hA : SH A) (hq : IsUnit (q : A))
    (n i : ℤ) :
    (2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i)) ∧
      Nonempty (Ht q (sp (LaurentPolynomial A)) 1 i ≃+ ZMod q) := by
  refine ⟨fun hn => GlobalTheory.T.laurentCohomology_vanishing_of_noetherian_henselian q (fun B _ _ hB hqB m j hm =>
    vanishing_below q m.toNat B hB hqB m j hm (by omega)) A hA hq n i hn, ?_⟩
  obtain ⟨e⟩ := GlobalTheory.T.nonempty_ht_zero_addEquiv_zmod_of_sh q A hA hq (i - 1)
  exact ⟨(AddEquiv.ofBijective (gmPhi q A i) (GlobalTheory.T.laurentKummerCupProduct_bijective_strictlyHenselian q A hA hq i)).symm.trans e⟩

end GlobalTheory.LaurentCohomologyVanishing
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem GlobalTheory.gm_cohomology_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
    ∀ n i : ℤ, (2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i)) ∧
      Nonempty (Ht q (sp (LaurentPolynomial A)) 1 i ≃+ ZMod q) := by
  first
  | exact @_root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology
  | exact _root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology
  | (apply _root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology <;> assumption)
  | (intros; apply _root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology ..)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicativeGroup_cohomology_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ n i : ℤ, (2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i)) ∧ Nonempty (Ht q (sp (LaurentPolynomial A)) 1 i ≃+ ZMod q) := by
  first | (exact @GlobalTheory.gm_cohomology_strictlyHenselian) | (exact GlobalTheory.gm_cohomology_strictlyHenselian) | (intros; apply GlobalTheory.gm_cohomology_strictlyHenselian  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem laurentPolynomial_cohomology_strictlyHenselian_vanishing : GlobalTheory.EtC.C5 := fun q _ A _ hA hq n i => GlobalTheory.T.multiplicativeGroup_cohomology_strictlyHenselian q A hA hq n i

end GlobalTheory.EtC
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_cohomology_locally_acyclic : GlobalTheory.EtC.C5 := by
  first | (exact @GlobalTheory.EtC.laurentPolynomial_cohomology_strictlyHenselian_vanishing) | (exact GlobalTheory.EtC.laurentPolynomial_cohomology_strictlyHenselian_vanishing) | (intros; apply GlobalTheory.EtC.laurentPolynomial_cohomology_strictlyHenselian_vanishing  <;> assumption)
end
