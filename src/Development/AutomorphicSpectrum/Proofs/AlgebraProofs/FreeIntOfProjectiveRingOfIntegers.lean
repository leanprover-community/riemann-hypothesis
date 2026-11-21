import Mathlib
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.CrtGood
import BuildAid.ForwardExisting
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGPadic
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwLift

section
section
open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem ProIso.nonempty_of_forall_prime : ∀ (O : Type) [CommRing O] (L L' : Type) [AddCommGroup L] [Module O L] [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L'), (∀ p : ℕ, p.Prime → Nonempty (ProIsoAt p O B B')) → Nonempty (ProIso O B B') :=
  @PositivityTheory.UnitarySelfGeneration.tw_crt

end GlobalTheory.CompanionTheory.Ar
end

open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pro_isometry_of_local_isometries : ∀ (O : Type) [CommRing O] (L L' : Type) [AddCommGroup L] [Module O L] [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L'), (∀ p : ℕ, p.Prime → Nonempty (ProIsoAt p O B B')) → Nonempty (ProIso O B B') := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.ProIso.nonempty_of_forall_prime
end

section
section
open NumberField TensorProduct

namespace GlobalTheory.CompanionTheory.TwGenus

theorem two_unimodular_isometric_padic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ (p : ℕ) [Fact p.Prime] (L L' : Type) [AddCommGroup L] [Module (𝓞 E) L] [Module.Finite (𝓞 E) L] [Module.Projective (𝓞 E) L] [AddCommGroup L'] [Module (𝓞 E) L'] [Module.Finite (𝓞 E) L'] [Module.Projective (𝓞 E) L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L'), Module.finrank (𝓞 E) L = Module.finrank (𝓞 E) L' → (∀ x, B x x = 0) → Function.Bijective B → (∀ (a : 𝓞 E) x y, B (a • x) y = B x (bar a • y)) → (∀ x, B' x x = 0) → Function.Bijective B' → (∀ (a : 𝓞 E) x y, B' (a • x) y = B' x (bar a • y)) → ∃ φ : (ℤ_[p] ⊗[ℤ] L) ≃ₗ[ℤ_[p]] (ℤ_[p] ⊗[ℤ] L'), (∀ (a : 𝓞 E) (x : L), φ (1 ⊗ₜ (a • x)) = LinearMap.baseChange ℤ_[p] (LinearMap.lsmul (𝓞 E) L' a).toAddMonoidHom.toIntLinearMap (φ (1 ⊗ₜ x))) ∧ ∀ u v, B'.baseChange ℤ_[p] (φ u) (φ v) = B.baseChange ℤ_[p] u v :=
  @PositivityTheory.UnitarySelfGeneration.tw_g_padic

end GlobalTheory.CompanionTheory.TwGenus
end

open NumberField TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_projective_module_pairing_p : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ (p : ℕ) [Fact p.Prime] (L L' : Type) [AddCommGroup L] [Module (𝓞 E) L] [Module.Finite (𝓞 E) L] [Module.Projective (𝓞 E) L] [AddCommGroup L'] [Module (𝓞 E) L'] [Module.Finite (𝓞 E) L'] [Module.Projective (𝓞 E) L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L'), Module.finrank (𝓞 E) L = Module.finrank (𝓞 E) L' → (∀ x, B x x = 0) → Function.Bijective B → (∀ (a : 𝓞 E) x y, B (a • x) y = B x (bar a • y)) → (∀ x, B' x x = 0) → Function.Bijective B' → (∀ (a : 𝓞 E) x y, B' (a • x) y = B' x (bar a • y)) → ∃ φ : (ℤ_[p] ⊗[ℤ] L) ≃ₗ[ℤ_[p]] (ℤ_[p] ⊗[ℤ] L'), (∀ (a : 𝓞 E) (x : L), φ (1 ⊗ₜ (a • x)) = LinearMap.baseChange ℤ_[p] (LinearMap.lsmul (𝓞 E) L' a).toAddMonoidHom.toIntLinearMap (φ (1 ⊗ₜ x))) ∧ ∀ u v, B'.baseChange ℤ_[p] (φ u) (φ v) = B.baseChange ℤ_[p] u v := by
  atlas_forward_decl GlobalTheory.CompanionTheory.TwGenus.two_unimodular_isometric_padic
end

section
section
open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem proIsoAt_of_padic_isometry : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (L L' : Type) [AddCommGroup L] [Module O L] [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L') [Module.Projective O L] [Module.Finite ℤ L] [Module.Free ℤ L] [Module.Finite ℤ L'] [Module.Free ℤ L'] (φ : (ℤ_[p] ⊗[ℤ] L) ≃ₗ[ℤ_[p]] (ℤ_[p] ⊗[ℤ] L')), (∀ (a : O) (x : L), φ (1 ⊗ₜ (a • x)) = LinearMap.baseChange ℤ_[p] (LinearMap.lsmul O L' a).toAddMonoidHom.toIntLinearMap (φ (1 ⊗ₜ x))) → (∀ u v, B'.baseChange ℤ_[p] (φ u) (φ v) = B.baseChange ℤ_[p] u v) → Nonempty (ProIsoAt p O B B') :=
  @PositivityTheory.UnitarySelfGeneration.tw_lift

end GlobalTheory.CompanionTheory.Ar
end

open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_isometry_equivariance : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (L L' : Type) [AddCommGroup L] [Module O L] [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L') [Module.Projective O L] [Module.Finite ℤ L] [Module.Free ℤ L] [Module.Finite ℤ L'] [Module.Free ℤ L'] (φ : (ℤ_[p] ⊗[ℤ] L) ≃ₗ[ℤ_[p]] (ℤ_[p] ⊗[ℤ] L')), (∀ (a : O) (x : L), φ (1 ⊗ₜ (a • x)) = LinearMap.baseChange ℤ_[p] (LinearMap.lsmul O L' a).toAddMonoidHom.toIntLinearMap (φ (1 ⊗ₜ x))) → (∀ u v, B'.baseChange ℤ_[p] (φ u) (φ v) = B.baseChange ℤ_[p] u v) → Nonempty (ProIsoAt p O B B') := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.proIsoAt_of_padic_isometry
end

section
open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem finite_int_of_finite_ringOfIntegers (E : Type) [Field E] [NumberField E] (L : Type) [AddCommGroup L]
    [Module (𝓞 E) L] [Module.Finite (𝓞 E) L] : Module.Finite ℤ L :=
  Module.Finite.trans (𝓞 E) L

theorem free_int_of_projective_ringOfIntegers (E : Type) [Field E] [NumberField E] (L : Type) [AddCommGroup L]
    [Module (𝓞 E) L] [Module.Finite (𝓞 E) L] [Module.Projective (𝓞 E) L] : Module.Free ℤ L := by
  haveI : Module.Finite ℤ L := finite_int_of_finite_ringOfIntegers E L
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective (𝓞 E) L)
  have hinj : Function.Injective s := fun x y hxy => by
    have := congrArg (Finsupp.linearCombination (𝓞 E) id) hxy
    simpa using (LinearMap.congr_fun hs x).symm.trans (this.trans (LinearMap.congr_fun hs y))
  haveI : Module.IsTorsionFree ℤ (L →₀ 𝓞 E) := inferInstance
  haveI : Module.IsTorsionFree ℤ L :=
    hinj.moduleIsTorsionFree (R := ℤ) s fun r m => by simp
  infer_instance


end GlobalTheory.CompanionTheory.Ar
end
