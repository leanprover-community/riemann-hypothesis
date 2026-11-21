import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.LenDirected
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CycZConjGal
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.GalOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.FnCycMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.IsCMOfConj

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base

namespace UpperTheory.V.Kum

section Lim

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

omit [IsAlgClosure F Ω] in
theorem levU_anti (U : Subgroup (G F Ω)) {m n : ℕ} (h : m ≤ n) : levU l U n ≤ levU l U m := by
  intro g hg
  simp only [levU, Subgroup.mem_inf, Subgroup.mem_comap, KStar.TotallyRealRoots.mem_princ] at hg ⊢
  exact ⟨hg.1, (pow_dvd_pow _ h).trans hg.2⟩

omit [IsAlgClosure F Ω] in

theorem len_le_of_layers (U : Subgroup (G F Ω)) (W : Submodule R (cycU l U → M)) (P : ∀ n, Submodule R (levU l U n → M))
    (hP : ∀ m n (h : m ≤ n), (P m).map (restr R M (levU_anti U h)) ≤ P n)
    (hW : ∀ φ ∈ W, ∃ n, ∃ ψ ∈ P n, restr R M (cycU_le_levU l U n) ψ = φ) (Bd : ℕ∞)
    (hB : ∀ n₀, ∃ n, n₀ ≤ n ∧ Module.length R (P n) ≤ Bd) : Module.length R W ≤ Bd := by
  refine lenDirected R _ W (fun n => (P n).map (restr R M (cycU_le_levU l U n))) Bd ?_ ?_ ?_
  · rintro m n h _ ⟨ψ, hψ, rfl⟩
    exact ⟨_, hP m n h ⟨ψ, hψ, rfl⟩, rfl⟩
  · intro φ hφ
    obtain ⟨n, ψ, hψ, rfl⟩ := hW φ hφ
    exact Submodule.mem_iSup_of_mem n ⟨ψ, hψ, rfl⟩
  · intro n₀
    obtain ⟨n, h, hn⟩ := hB n₀
    exact ⟨n, h, (Module.length_le_of_surjective _ (LinearMap.submoduleMap_surjective _ _)).trans hn⟩

theorem galOf_Fn (n : ℕ) : galOf F (Fn F Ω l n) Ω = Un F Ω l n := by
  have := (fnCyc F Ω l n).1
  rw [galOfCyc F Ω l n F (Fn F Ω l n), galOf_self]

omit [NumberField F] in
theorem length_map_le {X Y : Type} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] Y)
    (N : Submodule R X) : Module.length R (N.map f) ≤ Module.length R N :=
  Module.length_le_of_surjective _ (LinearMap.submoduleMap_surjective f N)




private theorem princ_smul_eq_self_of_pow_smul_eq_zero {k : ℕ} {x : QZ l} (hx : l ^ k • x = 0) {w : ℤ_[l]ˣ}
    (hw : w ∈ KStar.TotallyRealRoots.princ l k) : (w : ℤ_[l]) • x = x := by
  rw [KStar.TotallyRealRoots.mem_princ] at hw
  obtain ⟨c, hc⟩ := hw
  have h1 : ((w : ℤ_[l]) - 1) • x = 0 := by
    rw [hc, mul_comm ((l : ℤ_[l]) ^ k) c, mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hx, smul_zero]
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  exact h1

theorem locConst_qzG (e : ℤ) (m : QZ l) : IsLocallyConstant fun g => qzG F Ω l e g m := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g0
  obtain ⟨k, hk⟩ := (qzBasic l).2.1 m
  have hc : Continuous fun g => cycZ F Ω l g * (cycZ F Ω l g0)⁻¹ :=
    (continuous_cycZ F Ω l).mul continuous_const
  have hmem : ∀ᶠ g in nhds g0, cycZ F Ω l g * (cycZ F Ω l g0)⁻¹ ∈ KStar.TotallyRealRoots.princ l k := by
    apply hc.continuousAt.preimage_mem_nhds
    apply (KStar.TotallyRealRoots.isOpen_princ k).mem_nhds
    simp only [mul_inv_cancel]
    exact (KStar.TotallyRealRoots.princ l k).one_mem
  filter_upwards [hmem] with g hg
  show ((cycZ F Ω l g ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • m = ((cycZ F Ω l g0 ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • m
  have hw : (cycZ F Ω l g * (cycZ F Ω l g0)⁻¹) ^ (-e) ∈ KStar.TotallyRealRoots.princ l k := zpow_mem hg _
  have hx : l ^ k • (((cycZ F Ω l g0 ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • m) = 0 := by
    rw [smul_comm, hk, smul_zero]
  have key : cycZ F Ω l g ^ (-e) =
      (cycZ F Ω l g * (cycZ F Ω l g0)⁻¹) ^ (-e) * cycZ F Ω l g0 ^ (-e) := by
    rw [← mul_zpow, inv_mul_cancel_right]
  rw [key, Units.val_mul, mul_smul, princ_smul_eq_self_of_pow_smul_eq_zero hx hw]




variable [IsCMField F]





end Lim

end UpperTheory.V.Kum

end
