import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfSupPowEq
import BuildAid.ForwardExisting

section
namespace GlobalTheory

theorem iInf_sup_pow_eq_of_compatible :
    ∀ (C : Type) [CommRing C] (J : Ideal C), IsAdicComplete J C → ∀ u : ℕ → Ideal C,
      (∀ e, u e = u (e + 1) ⊔ J ^ (e + 1)) → ∀ e, (⨅ l, u l) ⊔ J ^ (e + 1) = u e := by
  first
  | exact @_root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq
  | exact _root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq
  | (apply _root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq ..)

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iInf_sup_pow_eq_of_adic_compatible_ideals : ∀ (C : Type) [CommRing C] (J : Ideal C), IsAdicComplete J C → ∀ u : ℕ → Ideal C, (∀ e, u e = u (e + 1) ⊔ J ^ (e + 1)) → ∀ e, (⨅ l, u l) ⊔ J ^ (e + 1) = u e := by
  atlas_forward_decl GlobalTheory.iInf_sup_pow_eq_of_compatible
