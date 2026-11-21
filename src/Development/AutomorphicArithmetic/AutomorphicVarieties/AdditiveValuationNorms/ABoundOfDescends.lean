import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ExistsCentresLevel
import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DinfNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.QzInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ZmodToQZ
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ShaLeV
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaLenEqShaInv

section
open UpperTheory.V UpperTheory.V.PropA Formalism.GaloisCohomology

theorem UpperTheory.V.PropA.dualDiv :
    ∀ (l : ℕ) [Fact l.Prime] (D : Type) [AddCommGroup D] [Module ℤ_[l] D] (x : D →ₗ[ℤ_[l]] QZ l), (∀ φ : D, (l : ℤ_[l]) • φ = 0 → x φ = 0) →
      ∃ y : D →ₗ[ℤ_[l]] QZ l, x = (l : ℤ_[l]) • y := by
  intro l _ D _ _ x hx
  let μ : D →ₗ[ℤ_[l]] D := (l : ℤ_[l]) • LinearMap.id
  have hker : LinearMap.ker μ ≤ LinearMap.ker x := by
    intro φ hφ
    exact hx φ (by simpa [μ] using hφ)
  let g : LinearMap.range μ →ₗ[ℤ_[l]] QZ l :=
    ((LinearMap.ker μ).liftQ x hker).comp (LinearMap.quotKerEquivRange μ).symm.toLinearMap
  obtain ⟨y, hy⟩ := (qzInj l).out (LinearMap.range μ).subtype Subtype.val_injective g
  refine ⟨y, ?_⟩
  ext φ
  have hmem : μ φ ∈ LinearMap.range μ := LinearMap.mem_range_self μ φ
  have h1 := hy ⟨μ φ, hmem⟩
  have h3 : (LinearMap.quotKerEquivRange μ).symm ⟨μ φ, hmem⟩ = Submodule.Quotient.mk φ := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  have h2 : g ⟨μ φ, hmem⟩ = x φ := by
    simp only [g, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [h3, Submodule.liftQ_apply]
  rw [h2] at h1
  simp only [Submodule.coe_subtype, μ, LinearMap.smul_apply, LinearMap.id_apply] at h1
  rw [LinearMap.smul_apply, ← h1, map_smul]
end

section
open UpperTheory.V UpperTheory.V.PropA Formalism.GaloisCohomology

theorem UpperTheory.V.PropA.torsFin :
    ∀ (l : ℕ) [Fact l.Prime] (D : Type) [AddCommGroup D] [Module ℤ_[l] D], Module.Finite ℤ_[l] (D →ₗ[ℤ_[l]] QZ l) →
      {φ : D | (l : ℤ_[l]) • φ = 0}.Finite := by
  intro l _ D _ _ hfin
  have hl : l.Prime := Fact.out
  obtain ⟨ι, hιinj, hιrange, -⟩ := UpperTheory.V.Kum.zmodToQZ l 1
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : Fact (1 < l ^ 1) := ⟨by rw [pow_one]; exact hl.one_lt⟩
  set Q : Set (QZ l) := {q | (l : ℤ_[l]) • q = 0} with hQ
  have hQfin : Q.Finite := by
    have : Q = Set.range ι := by
      ext q
      rw [hιrange q, pow_one]
      rfl
    rw [this]
    exact Set.finite_range ι
  have hι1 : ι 1 ≠ 0 := by
    intro h
    have h0 : ι 1 = ι 0 := by rw [h, map_zero]
    have := hιinj h0
    exact one_ne_zero this
  have hlι : (l : ℤ_[l]) • ι 1 = 0 := by
    have := (hιrange (ι 1)).mp ⟨1, rfl⟩
    simpa using this
  obtain ⟨s, hs⟩ := hfin.fg_top
  have hsep : ∀ t : D, (l : ℤ_[l]) • t = 0 → (∀ g ∈ s, g t = 0) → t = 0 := by
    intro t htl hg
    have hall : LinearMap.applyₗ (R := ℤ_[l]) (M₂ := QZ l) t = 0 :=
      LinearMap.ext_on hs (fun g hg' => by simpa using hg g hg')
    by_contra ht
    let μt : ℤ_[l] →ₗ[ℤ_[l]] D := LinearMap.toSpanSingleton ℤ_[l] D t
    let ν : ℤ_[l] →ₗ[ℤ_[l]] QZ l := LinearMap.toSpanSingleton ℤ_[l] (QZ l) (ι 1)
    have hker : LinearMap.ker μt ≤ LinearMap.ker ν := by
      intro a ha
      have ha' : a • t = 0 := by simpa [μt] using ha
      show a • ι 1 = 0
      by_cases hu : IsUnit a
      · exact absurd ((hu.smul_eq_zero).mp ha') ht
      · have hm : a ∈ IsLocalRing.maximalIdeal ℤ_[l] := (IsLocalRing.mem_maximalIdeal a).mpr hu
        rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hm
        obtain ⟨b, rfl⟩ := hm
        rw [mul_smul, hlι, smul_zero]
    let g0 : LinearMap.range μt →ₗ[ℤ_[l]] QZ l :=
      ((LinearMap.ker μt).liftQ ν hker).comp (LinearMap.quotKerEquivRange μt).symm.toLinearMap
    obtain ⟨y, hy⟩ := (qzInj l).out (LinearMap.range μt).subtype Subtype.val_injective g0
    have hmem : μt 1 ∈ LinearMap.range μt := LinearMap.mem_range_self μt 1
    have h3 : (LinearMap.quotKerEquivRange μt).symm ⟨μt 1, hmem⟩ = Submodule.Quotient.mk 1 := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    have h1 := hy ⟨μt 1, hmem⟩
    have h2 : g0 ⟨μt 1, hmem⟩ = ι 1 := by
      simp only [g0, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
      rw [h3, Submodule.liftQ_apply]
      simp [ν]
    rw [h2] at h1
    have hyt : y t = 0 := by
      have := LinearMap.congr_fun hall y
      simpa using this
    have : μt 1 = t := by simp [μt]
    simp only [Submodule.coe_subtype, this] at h1
    exact hι1 (h1 ▸ hyt)
  let f : D → (s → QZ l) := fun φ g => (g : D →ₗ[ℤ_[l]] QZ l) φ
  have hpi : (Set.pi Set.univ (fun _ : s => Q)).Finite := Set.Finite.pi (fun _ => hQfin)
  apply Set.Finite.of_finite_image (f := f) _ _
  · apply hpi.subset
    rintro _ ⟨φ, hφ, rfl⟩ g _
    show (l : ℤ_[l]) • (g : D →ₗ[ℤ_[l]] QZ l) φ = 0
    rw [← map_smul, show (l : ℤ_[l]) • φ = 0 from hφ, map_zero]
  · intro φ hφ ψ hψ hfe
    have hφ' : (l : ℤ_[l]) • φ = 0 := hφ
    have hψ' : (l : ℤ_[l]) • ψ = 0 := hψ
    have := hsep (φ - ψ) (by rw [smul_sub, hφ', hψ', sub_zero]) (fun g hg => by
      have := congr_fun hfe ⟨g, hg⟩
      simp only [f] at this
      rw [map_sub, this, sub_self])
    exact sub_eq_zero.mp this
end

section
open UpperTheory.V UpperTheory.V.PropA Formalism.GaloisCohomology

theorem UpperTheory.V.PropA.dualUnip :
    ∀ (l : ℕ) [Fact l.Prime] (D : Type) [AddCommGroup D] [Module ℤ_[l] D] (g : Module.End ℤ_[l] D) (t : Module.End ℤ_[l] (D →ₗ[ℤ_[l]] QZ l)),
      Module.Finite ℤ_[l] (D →ₗ[ℤ_[l]] QZ l) → (∀ x φ, t x φ = x (g φ)) → (∀ φ : D, ∃ k : ℕ, ((g - 1) ^ k) φ = 0) → Unip t := by
  intro l _ D _ _ g t hfin ht hnil
  classical
  have hT := torsFin l D hfin
  choose k hk using hnil
  have key : ∀ (n : ℕ) (x : D →ₗ[ℤ_[l]] QZ l) (φ : D), ((t - 1) ^ n) x φ = x (((g - 1) ^ n) φ) := by
    intro n
    induction n with
    | zero =>
      intro x φ
      simp
    | succ n ih =>
      intro x φ
      rw [pow_succ, Module.End.mul_apply, ih]
      rw [pow_succ' (g - 1), Module.End.mul_apply]
      simp [ht, map_sub]
  refine ⟨hT.toFinset.sup k, fun x => ?_⟩
  obtain ⟨y, hy⟩ := dualDiv l D (((t - 1) ^ (hT.toFinset.sup k)) x) (by
    intro φ hφ
    rw [key]
    have hmem : φ ∈ hT.toFinset := by simpa using hφ
    have hle : k φ ≤ hT.toFinset.sup k := Finset.le_sup hmem
    rw [← Nat.sub_add_cancel hle, pow_add, Module.End.mul_apply, hk, map_zero, map_zero])
  exact ⟨y, by simpa using hy⟩
end

section
open UpperTheory.V UpperTheory.V.PropA NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.PropA.xUnip :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (N : ℕ)
      (U : Subgroup (G k Ω)) [U.Normal], IsClosed (U : Set (G k Ω)) → Module.Finite ℤ_[l] (Xinf l N U) →
      ∀ γ ∈ levU l U 1, Unip (xRep l N U γ) := by
  intro k Ω _ _ _ _ _ l _ N U _ hU hfin γ hγ
  refine dualUnip l (Dinf l N U) (dRep l N U γ⁻¹) (xRep l N U γ) hfin (fun x φ => xRep_apply l N U γ x φ) fun φ => ?_
  obtain ⟨n, -, hn⟩ := (dinfNil k Ω l N U hU φ.1 φ.2).2 γ⁻¹ (inv_mem hγ)
  refine ⟨n, Subtype.ext ?_⟩
  have key : ∀ (m : ℕ) (ψ : Dinf l N U), (((dRep l N U γ⁻¹ - 1) ^ m) ψ).1 =
      ((funRep ℤ_[l] (QZ l) (cycU l U) γ⁻¹ - 1) ^ m) ψ.1 := by
    intro m
    induction m with
    | zero => intro ψ; rfl
    | succ m ih =>
      intro ψ
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      rfl
  rw [key, hn]
  rfl
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

namespace UpperTheory.V.PropA

variable (l : ℕ) [Fact l.Prime] (L₀ : Type) [Field L₀] [NumberField L₀]

def Descends (γ : G L₀ (AlgebraicClosure L₀)) : Prop :=
  ∀ e : ℕ, 1 ≤ e → ∀ (m : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁], IsLayer l m L₀ L₁ →
    shaInv L₁ l e = cokerLen (xTw l l (⊤ : Subgroup (G L₀ (AlgebraicClosure L₀))) e γ ^ l ^ m - 1)

variable {l L₀}

theorem mem_levU_one {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] {γ : G k Ω}
    (h : (l : ℤ_[l]) ∣ (cycZ k Ω l γ : ℤ_[l]) - 1) : γ ∈ levU l (⊤ : Subgroup (G k Ω)) 1 := by
  refine ⟨trivial, MonoidHom.mem_ker.2 (Units.ext ?_)⟩
  show PadicInt.toZModPow 1 (cycZ k Ω l γ : ℤ_[l]) = 1
  rw [← sub_eq_zero, ← map_one (PadicInt.toZModPow (p := l) 1), ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    pow_one, Ideal.mem_span_singleton]
  exact h

theorem Descends.eq_twLen {γ : G L₀ (AlgebraicClosure L₀)} (h : Descends l L₀ γ) {e : ℕ} (he : 1 ≤ e) {m : ℕ} {L₁ : Type}
    [Field L₁] [NumberField L₁] [Algebra L₀ L₁] (hL : IsLayer l m L₀ L₁) :
    shaInv L₁ l e = twLen (xRep l l (⊤ : Subgroup (G L₀ (AlgebraicClosure L₀))) γ) (cycZ L₀ _ l γ : ℤ_[l]) e m := by
  rw [h e he m L₁ hL, xTw_apply, zpow_natCast, Units.val_pow_eq_pow_val]
  rfl

theorem aBound_of_descends (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK) {R c : ℕ}
    (ht : IsTower l L₀ R) {γ : G L₀ (AlgebraicClosure L₀)} (hu : IsLevel l (cycZ L₀ _ l γ : ℤ_[l]) c)
    (hc : ∃ ζ : L₀, IsPrimitiveRoot ζ (l ^ c)) (h : Descends l L₀ γ) : Win.ABound l R L₀ := by
  have hX : GenBy l R (XP l L₀) := ht.gen
  have hγ := xUnip L₀ (AlgebraicClosure L₀) l l ⊤ isClosed_univ ht.gen.finite γ (mem_levU_one (lteNorm l _ c hu).2.1)
  refine ⟨?_, fun e he m L₁ _ _ _ h₁ L₂ _ _ _ h₂ Ω _ _ _ D => ?_⟩
  · obtain ⟨s, hs⟩ := exists_centres_norm hX hγ hu
    refine ⟨ℚ_[l], inferInstance, inferInstance, inferInstance, c, R, fun i => s i, le_rfl, hc,
      fun e he m L₁ _ _ _ h₁ B hB => ?_⟩
    rw [h.eq_twLen he h₁]
    refine hs e m B fun i => (hB i).trans (le_of_eq ?_)
    rw [PadicInt.norm_def]
    push_cast
    rfl
  · haveI := ht.complex
    haveI : IsTotallyComplex L₂ := isTotallyComplex_of_algebra L₀ L₂
    rw [h.eq_twLen he h₁]
    refine (twLen_le_growth hX hγ hu e m).trans (add_le_add ?_ le_rfl)
    rw [← h.eq_twLen he (m := jZero l R) h₂, ← shaLen_eq_shaInv D]
    exact shaLeV hP hF hT L₂ Ω l (ptCase_of_isTotallyComplex L₂ l) D e

end UpperTheory.V.PropA

end
end
