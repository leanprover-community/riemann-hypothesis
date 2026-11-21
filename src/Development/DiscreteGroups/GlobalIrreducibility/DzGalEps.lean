import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.GalUnitCompat
import Development.DiscreteGroups.GlobalIrreducibility.DzLTame
import Development.DiscreteGroups.GlobalIrreducibility.DzGalRes
import Development.DiscreteGroups.GlobalIrreducibility.DzGalFin
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
import Development.DiscreteGroups.GlobalIrreducibility.ExistsUniformizerValuation
import Development.DiscreteGroups.GlobalIrreducibility.DzGalUnr
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Development.DiscreteGroups.GlobalIrreducibility.DzGalKappa

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil Module

set_option linter.all false

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_H_eigen {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E']
    [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (g : ℕ) [Fact g.Prime]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (n : ℕ) (hn : 0 < n)
    (hg : ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2) (hN : normV w' = g ^ n)
    (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a')
    (K : Type) [Field K] [Algebra (ZMod g) K] (red : 𝓞 E' →+* K) (hr : Function.Surjective red)
    (hk : RingHom.ker red = w'.asIdeal)
    (m : ℕ) (b : WDRep h (Fin m → ℂ)) (hb : b.ρ.IsIrreducible)
    (htame : ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → b.ρ σ = 1) (hm : finrank ℂ (Fin m → ℂ) = n)
    (ξ : Kˣ →* ℂˣ)
    (hξf : ∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : Kˣ), red x = z →
        Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
        (WD.mk b).inePol (AlgEquiv.restrictScalars E (t : G E' Ω)) =
          ∏ j ∈ Finset.range n, (X - C ((ξ (z ^ g ^ j) : ℂˣ) : ℂ))) :
    ∃ (v₀ : Fin m → ℂ) (χH : Weil h → ℂ), v₀ ≠ 0 ∧
      (∀ σ : Weil h, (n : ℤ) ∣ deg σ → b.ρ σ v₀ = χH σ • v₀) ∧
      (∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : Kˣ), red x = z →
        Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
        χH (ineIncl h (resI t)) = ((ξ z : ℂˣ) : ℂ)) ∧
      Submodule.span ℂ (Set.range fun σ => b.ρ σ v₀) = ⊤ := by
  classical
  have hq : normV w = g := normV_eq_of_padic w g i hi
  have hq' : normV w' = normV w ^ n := by rw [hq, hN]
  let I : Subgroup (Weil h) := (Ine (F := E) A).comap (Weil h).subtype
  haveI hInorm : I.Normal := ⟨fun t ht g0 => by
    show ((g0 * t * g0⁻¹ : Weil h) : G E Ω) ∈ Ine (F := E) A
    exact conj_mem_Ine (Weil_le_Dec h g0.2) ht⟩
  have hgen : ∀ σ : Weil h, ∃ k : ℤ, ∃ t ∈ I, σ = frob h ^ k * t := fun σ => by
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
    exact ⟨deg σ, ineIncl h τ, τ.2, hτ⟩
  have hcomm : ∀ s ∈ I, ∀ t ∈ I, b.ρ s * b.ρ t = b.ρ t * b.ρ s := by
    intro s hs t ht
    let s' : Ine (F := E) A := ⟨s, hs⟩
    let t' : Ine (F := E) A := ⟨t, ht⟩
    have h1 : b.ρ (ineIncl h (s' * t' * s'⁻¹ * t'⁻¹)) = 1 := htame _ (isWild_commutator s' t')
    have h2 : ineIncl h (s' * t' * s'⁻¹ * t'⁻¹) = s * t * s⁻¹ * t⁻¹ := Subtype.ext rfl
    rw [h2] at h1
    have e : s * t = (s * t * s⁻¹ * t⁻¹) * (t * s) := by group
    rw [← map_mul, ← map_mul, e, map_mul, h1, one_mul]
  have hfrob : ∀ t ∈ I, b.ρ (frob h * t * (frob h)⁻¹) = b.ρ t ^ normV w := by
    intro t ht
    let t' : Ine (F := E) A := ⟨t, ht⟩
    let c' : Ine (F := E) A :=
      ⟨(frob h : G E Ω) * t' * (frob h : G E Ω)⁻¹, conj_mem_Ine (isFrob_frob (h := h)).1 t'.2⟩
    have h1 : b.ρ (ineIncl h (c' * (t' ^ normV w)⁻¹)) = 1 :=
      htame _ (isWild_frob (isFrob_frob (h := h)) t')
    have h2 : ineIncl h (c' * (t' ^ normV w)⁻¹) = frob h * t * (frob h)⁻¹ * (t ^ normV w)⁻¹ := Subtype.ext rfl
    rw [h2] at h1
    have e : frob h * t * (frob h)⁻¹ = (frob h * t * (frob h)⁻¹ * (t ^ normV w)⁻¹) * t ^ normV w := by group
    rw [e, map_mul, h1, one_mul, map_pow]
  obtain ⟨η, u, c, hu, huI, hφn, hchar, hper, hmin⟩ :=
    DzCliff.clifford b.ρ hb I (frob h) (normV w) n hm hn hgen hcomm hfrob
  rw [hq] at hchar hper
  have hc0 : c ≠ 0 := fun h0 => DzCliff.rho_ne_zero b.ρ (frob h ^ n) hu (by rw [hφn, h0, zero_smul])
  have hcinv : b.ρ (frob h ^ n)⁻¹ u = c⁻¹ • u := by
    have h1 := DzCliff.rho_inv_apply b.ρ (frob h ^ n) u
    rw [hφn, map_smul] at h1
    calc b.ρ (frob h ^ n)⁻¹ u = c⁻¹ • (c • b.ρ (frob h ^ n)⁻¹ u) := by
          rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • u := by rw [h1]
  have hz : ∀ k : ℤ, b.ρ ((frob h ^ n) ^ k) u = c ^ k • u := by
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [zpow_add_one, map_mul, Module.End.mul_apply, hφn, map_smul, ih, smul_smul, zpow_add_one₀ hc0, mul_comm]
    | pred k ih =>
      rw [zpow_sub_one, map_mul, Module.End.mul_apply, hcinv, map_smul, ih, smul_smul, zpow_sub_one₀ hc0,
        mul_comm]
  have huH : ∀ σ : Weil h, (n : ℤ) ∣ deg σ → ∃ e : ℂ, b.ρ σ u = e • u := by
    intro σ hσ
    obtain ⟨k, hk'⟩ := hσ
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
    rw [hτ, hk', map_mul, Module.End.mul_apply, huI (ineIncl h τ) τ.2, map_smul,
      show frob h ^ ((n : ℤ) * k) = (frob h ^ n) ^ k by rw [zpow_mul, zpow_natCast], hz, smul_smul]
    exact ⟨_, rfl⟩
  obtain ⟨R, hR⟩ := exists_resHom (A := A) ha' hk
  obtain ⟨β, hβ⟩ := exists_eigenChar b.ρ ((ineIncl h).comp (resI (E := E) (E' := E') (Ω := Ω) (A := A))) hu
    (fun t => ⟨_, huI (ineIncl h (resI t)) (resI t).2⟩)
  have hβη : ∀ t : Ine (F := E') A, ((β t : ℂˣ) : ℂ) = η (ineIncl h (resI t)) := fun t =>
    DzCliff.eig_unique hu (hβ t) (huI (ineIncl h (resI t)) (resI t).2)
  have hpos : 0 < g ^ n := pow_pos (Fact.out : g.Prime).pos n
  have hzK : ∀ z : Kˣ, z ^ g ^ n = z := pow_card_units w' g n hN K red hr hk hpos
  have hα : ∀ t, ((ξ.comp R) t) ^ (g ^ n - 1) = 1 := by
    intro t
    rw [MonoidHom.comp_apply, ← map_pow]
    have : R t ^ (g ^ n - 1) = 1 := by
      have h1 := hzK (R t)
      have h2 : R t ^ (g ^ n - 1) * R t = 1 * R t := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : g.Prime).pos), h1, one_mul]
      exact mul_right_cancel h2
    rw [this, map_one]
  have h1 : ∀ t, ∃ j : ℕ, β t = (ξ.comp R) t ^ g ^ j := by
    intro t
    obtain ⟨x, hx⟩ := exists_int_approx_compl w' _ (val_artin_ine ha' t).le
    have hRx : R t = Units.mk0 (red x) (red_ne_zero_of_approx ha' hk hx) := Units.ext (hR t x hx)
    have hp := hξf t x (R t) (hR t x hx).symm hx
    rw [WD.inePol_of_mem_Ine _ (res_mem_Ine t.2), WD.charPol_mk,
      show ineIncl h ⟨AlgEquiv.restrictScalars E (t : G E' Ω), res_mem_Ine t.2⟩ = ineIncl h (resI t) from rfl,
      hchar _ (resI t).2] at hp
    have hroot := congrArg (Polynomial.eval (η (ineIncl h (resI t)))) hp
    rw [Polynomial.eval_prod, Polynomial.eval_prod] at hroot
    have hl : ∏ j ∈ Finset.range n, Polynomial.eval (η (ineIncl h (resI t)))
        (X - C (η (ineIncl h (resI t)) ^ g ^ j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.mpr hn) (by simp)
    rw [hl, eq_comm, Finset.prod_eq_zero_iff] at hroot
    obtain ⟨j, -, hj⟩ := hroot
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hj
    refine ⟨j, Units.ext ?_⟩
    rw [hβη, hj, MonoidHom.comp_apply, map_pow, Units.val_pow_eq_pow_val]
  obtain ⟨j₀, hj₀⟩ := char_orbit (ξ.comp R) β (g ^ n - 1) (Nat.sub_pos_of_lt (Nat.one_lt_pow hn.ne'
    (Fact.out : g.Prime).one_lt)) hα g h1
  have hαn : ∀ k t, ((ξ.comp R) t) ^ g ^ (k * n) = (ξ.comp R) t := by
    intro k t
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul, pow_add, pow_mul, ih, MonoidHom.comp_apply, ← map_pow, hzK]
  set j : ℕ := n - j₀ % n with hj
  have hjn : j₀ + j = n * (j₀ / n + 1) := by
    have := Nat.div_add_mod j₀ n
    have := Nat.mod_lt j₀ hn
    rw [hj]; rw [Nat.mul_add, Nat.mul_one]; omega
  set v₀ := b.ρ (frob h ^ j)⁻¹ u with hv₀
  have hv₀0 : v₀ ≠ 0 := DzCliff.rho_ne_zero b.ρ _ hu
  have hv₀I : ∀ t ∈ I, b.ρ t v₀ = η t ^ g ^ j • v₀ :=
    DzCliff.eig_translate b.ρ I (frob h) g (by rw [← hq]; exact hfrob) huI j
  have hv₀H : ∀ σ : Weil h, ∃ e : ℂ, (n : ℤ) ∣ deg σ → b.ρ σ v₀ = e • v₀ := by
    intro σ
    by_cases hσ : (n : ℤ) ∣ deg σ
    · have hdeg : (n : ℤ) ∣ deg (frob h ^ j * σ * (frob h ^ j)⁻¹) := by simpa using hσ
      obtain ⟨e, he⟩ := huH _ hdeg
      refine ⟨e, fun _ => ?_⟩
      have e1 : σ * (frob h ^ j)⁻¹ = (frob h ^ j)⁻¹ * (frob h ^ j * σ * (frob h ^ j)⁻¹) := by group
      rw [hv₀, ← Module.End.mul_apply, ← map_mul, e1, map_mul, Module.End.mul_apply, he, map_smul]
    · exact ⟨0, fun h0 => absurd h0 hσ⟩
  choose χH hχH using hv₀H
  refine ⟨v₀, χH, hv₀0, fun σ hσ => hχH σ hσ, fun t x z hxz hx => ?_, ?_⟩
  · have hRz : R t = z := Units.ext (by rw [hR t x hx, hxz])
    have e1 := hχH (ineIncl h (resI t)) (by simp)
    have e2 := hv₀I (ineIncl h (resI t)) (resI t).2
    rw [DzCliff.eig_unique hv₀0 e1 e2, ← hβη]
    have h3 := hj₀ t
    have h4 : β t ^ g ^ j = (ξ.comp R) t := by
      rw [h3, ← pow_mul, ← pow_add, hjn, mul_comm, hαn]
    have h5 := congrArg Units.val h4
    rw [Units.val_pow_eq_pow_val] at h5
    rw [h5, MonoidHom.comp_apply, hRz]
  · apply DzCliff.eq_top_of_stable b.ρ hb
    · intro h0
      have hmem : b.ρ 1 v₀ ∈ Submodule.span ℂ (Set.range fun σ => b.ρ σ v₀) := Submodule.subset_span ⟨1, rfl⟩
      rw [h0, map_one, Module.End.one_apply, Submodule.mem_bot] at hmem
      exact hv₀0 hmem
    · intro τ v hv
      have hle : Submodule.span ℂ (Set.range fun σ => b.ρ σ v₀) ≤
          (Submodule.span ℂ (Set.range fun σ => b.ρ σ v₀)).comap (b.ρ τ) := by
        rw [Submodule.span_le]
        rintro _ ⟨σ, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul]
        exact Submodule.subset_span ⟨τ * σ, rfl⟩
      exact hle hv

end DiscreteGroups.sglob.DzType

end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil Module

set_option linter.all false

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem eps_ind_step {E L Ω : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra E L] [IsScalarTower E L Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) {v : HeightOneSpectrum (𝓞 L)}
    (hv : IsPlaceOver A v) (hL : IsLocalExt L h) {ε : EpsFamily A} (hε : IsDeligneEps ε)
    {ψ : AddChar (w.adicCompletion E) Circle} (hc : Continuous ψ) (h1 : ψ ≠ 1)
    {ψL : AddChar (v.adicCompletion L) Circle} (hcL : Continuous ψL)
    (hψL : ∀ z : L, ψL (algebraMap L _ z) = ψ (algebraMap E _ (Algebra.trace E L z)))
    (r : Weil hv →* Weil h) (hr : ∀ (σ : Weil hv) (z : Ω), (r σ : G E Ω) z = (σ : G L Ω) z)
    (hrs : ∀ (M : Type) [Monoid M] (f : Weil h →* M), IsSmooth f → IsSmooth (f.comp r))
    {m : ℕ} (hm : m = Module.finrank E L) (b : WDRep h (Fin m → ℂ)) (v₀ : Fin m → ℂ)
    (hsp : Submodule.span ℂ (Set.range fun σ => b.ρ σ v₀) = ⊤)
    (ξL₀ : Weil hv →* ℂˣ) (hξ : ∀ σ, b.ρ (r σ) v₀ = (ξL₀ σ : ℂ) • v₀)
    (ν₁ ν₂ : Weil h →* ℂˣ) (hν₁ : IsSmooth ν₁) (hν₂ : IsSmooth ν₂) :
    ∃ (hs₁ : IsSmooth (ξL₀ * ν₁.comp r)) (hs₂ : IsSmooth (ξL₀ * ν₂.comp r)),
      ε E w h ψ (WD.mk (b.twist ν₁ hν₁)) * ε L v hv ψL (WD.lpOfChar hv (ξL₀ * ν₂.comp r) hs₂) =
        ε E w h ψ (WD.mk (b.twist ν₂ hν₂)) * ε L v hv ψL (WD.lpOfChar hv (ξL₀ * ν₁.comp r) hs₁) := by
  have key : ∀ (ν : Weil h →* ℂˣ) (hν : IsSmooth ν), ∃ hs : IsSmooth (ξL₀ * ν.comp r),
      Induces (WD.lpOfChar hv (ξL₀ * ν.comp r) hs) (WD.mk (b.twist ν hν)) := by
    intro ν hν
    refine EpsUnique.induces_of_eigenvector E L Ω A w v h hv r hr hrs m (b.twist ν hν) v₀ (ξL₀ * ν.comp r) hm
      (fun σ => ?_) ?_
    · rw [WDRep.twist_ρ, LinearMap.smul_apply, hξ, smul_smul, MonoidHom.mul_apply, Units.val_mul,
        MonoidHom.comp_apply, mul_comm]
    · rw [eq_top_iff, ← hsp]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨σ, rfl⟩
      have e : b.ρ σ v₀ = ((ν σ)⁻¹ : ℂˣ) • ((b.twist ν hν).ρ σ v₀) := by
        rw [WDRep.twist_ρ, LinearMap.smul_apply, Units.smul_def, smul_smul, ← Units.val_mul, inv_mul_cancel,
          Units.val_one, one_smul]
      show b.ρ σ v₀ ∈ Submodule.span ℂ (Set.range fun σ => (b.twist ν hν).ρ σ v₀)
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ, rfl⟩)
  obtain ⟨hs₁, i₁⟩ := key ν₁ hν₁
  obtain ⟨hs₂, i₂⟩ := key ν₂ hν₂
  refine ⟨hs₁, hs₂, ?_⟩
  have d : (WD.lpOfChar hv (ξL₀ * ν₁.comp r) hs₁).lpDim = (WD.lpOfChar hv (ξL₀ * ν₂.comp r) hs₂).lpDim := by
    simp [WD.lpOfChar]
  exact hε.ind E L w v h hv hL ψ ψL hc h1 hcL hψL _ _ _ _ i₁ i₂ d

end DiscreteGroups.sglob.DzType

end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil Module

set_option linter.all false

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section W

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem lpTwist_lpTwist (x : WD h) (α β : Weil h →* ℂˣ) (hα : IsSmooth α) (hβ : IsSmooth β) (hαβ : IsSmooth (α * β)) :
    (x.lpTwist α hα).lpTwist β hβ = x.lpTwist (α * β) hαβ := by
  induction x using WD.ind with
  | hP m a =>
    rw [WD.lpTwist_mk, WD.lpTwist_mk, WD.lpTwist_mk]
    refine WD.sound ⟨LinearEquiv.refl ℂ _, fun σ v => ?_, fun v => rfl⟩
    simp [smul_smul, mul_comm]

variable (h) in

def degDvd (n : ℕ) : Subgroup (Weil h) where
  carrier := {σ | (n : ℤ) ∣ deg σ}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    show (n : ℤ) ∣ deg (a * b)
    rw [deg_mul]; exact dvd_add ha hb
  inv_mem' := fun {a} ha => by
    show (n : ℤ) ∣ deg a⁻¹
    rw [deg_inv]; exact (dvd_neg).mpr ha

theorem mem_degDvd {n : ℕ} {σ : Weil h} : σ ∈ degDvd h n ↔ (n : ℤ) ∣ deg σ := Iff.rfl

theorem index_degDvd {n : ℕ} (hn : 0 < n) : (degDvd h n).index = n := by
  haveI : NeZero n := ⟨hn.ne'⟩
  let f : Weil h →* Multiplicative (ZMod n) :=
    (AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod n))).comp (degHom h)
  have hker : f.ker = degDvd h n := by
    ext σ
    rw [MonoidHom.mem_ker, mem_degDvd]
    show Multiplicative.ofAdd ((deg σ : ℤ) : ZMod n) = 1 ↔ _
    rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff]
    exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨k, hk⟩ := ZMod.intCast_surjective (Multiplicative.toAdd z)
    obtain ⟨σ, hσ⟩ := deg_surjective (h := h) k
    refine ⟨σ, ?_⟩
    show Multiplicative.ofAdd ((deg σ : ℤ) : ZMod n) = z
    rw [hσ, hk]; rfl
  rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
  show Nat.card (ZMod n) = n
  exact Nat.card_zmod n

end W

theorem gs_scaled {g : ℕ} [Fact g.Prime] (ψ₀ : AddChar (ZMod g) Circle) {K : Type} [Field K] [Finite K]
    [Algebra (ZMod g) K] (η : Kˣ →* ℂˣ) (β : Kˣ) :
    ∑ᶠ z : Kˣ, (((η z)⁻¹ : ℂˣ) : ℂ) * (ψ₀ (Algebra.trace (ZMod g) K ((β : K) * z)) : ℂ) =
      (η β : ℂ) * gs ψ₀ η⁻¹ := by
  classical
  haveI := Fintype.ofFinite K
  haveI : Fintype Kˣ := inferInstance
  rw [gs, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [← Equiv.sum_comp (Equiv.mulLeft β⁻¹)]
  refine Finset.sum_congr rfl fun z _ => ?_
  have e1 : (β : K) * ((β⁻¹ * z : Kˣ) : K) = (z : K) := by
    rw [Units.val_mul, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  rw [Equiv.coe_mulLeft, e1]
  simp only [map_mul, map_inv, mul_inv, inv_inv, MonoidHom.inv_apply, Units.val_mul]
  ring

end DiscreteGroups.sglob.DzType

end
end

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem liftsChar_pow {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (χ₀ : (ZMod g)ˣ →* ℂˣ)
    (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hlc : LiftsChar i χ₀ χ) : ∀ x, χ x ^ (g - 1) = 1 := by
  intro x
  have hg0 : (g : ℚ_[g]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero
  have hgk : (g : w.adicCompletion E) ≠ 0 := by
    rw [← map_natCast i]; exact (map_ne_zero i).2 hg0
  set y : ℚ_[g] := i.symm (x : w.adicCompletion E) with hy
  have hy0 : y ≠ 0 := (map_ne_zero i.symm).2 x.ne_zero
  have hn : ‖y * (g : ℚ_[g]) ^ (-y.valuation)‖ = 1 := by
    rw [norm_mul, Padic.norm_eq_zpow_neg_valuation hy0, Padic.norm_p_zpow, neg_neg, ← zpow_add₀, neg_add_cancel,
      zpow_zero]
    exact Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero
  let γ : (w.adicCompletion E)ˣ := Units.mk0 _ hgk
  have hγ : χ γ = 1 := hlc.2 γ rfl
  have hu := hlc.1 (PadicInt.mkUnits hn) (x * γ ^ (-y.valuation)) (by
    rw [PadicInt.mkUnits_eq, map_mul, map_zpow₀, map_natCast, hy, RingEquiv.apply_symm_apply, Units.val_mul,
      Units.val_zpow_eq_zpow_val]
    rfl)
  rw [map_mul, map_zpow, hγ, one_zpow, mul_one] at hu
  rw [hu, ← map_pow, ZMod.units_pow_card_sub_one_eq_one, map_one]

theorem hasExponent_one_of_res {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ζ : kˣ →* ℂˣ) (ζb : 𝓀[k]ˣ →* ℂˣ)
    (hcompat : ∀ x : 𝒪[k]ˣ, ζ (Units.map (algebraMap 𝒪[k] k : 𝒪[k] →* k) x) =
      ζb (Units.map (IsLocalRing.residue 𝒪[k] : 𝒪[k] →* 𝓀[k]) x)) (hne : ζb ≠ 1) : HasExponent ζ 1 := by
  have hv := Valuation.integer.integers (valuation k)
  refine ⟨fun x hx => ?_, fun b hb => ?_⟩
  · let a : 𝒪[k] := ⟨x, (Valuation.mem_integer_iff _ _).2 hx.1.le⟩
    have ha : IsUnit a := hv.isUnit_iff_valuation_eq_one.2 hx.1
    have e : Units.map (algebraMap 𝒪[k] k : 𝒪[k] →* k) ha.unit = x := Units.ext rfl
    have e' : Units.map (IsLocalRing.residue 𝒪[k] : 𝒪[k] →* 𝓀[k]) ha.unit = 1 := by
      refine Units.ext ?_
      show IsLocalRing.residue 𝒪[k] a = 1
      rw [← map_one (IsLocalRing.residue 𝒪[k]), residue_eq_iff_valuation_lt]
      have h2 := hx.2
      rw [pow_one] at h2
      exact lt_of_le_of_lt h2 uniformizer_lt_one
    rw [← e, hcompat, e', map_one]
  · obtain rfl : b = 0 := by omega
    obtain ⟨z, hz⟩ : ∃ z, ζb z ≠ 1 := by
      by_contra h
      exact hne (MonoidHom.ext fun z => not_not.1 (not_exists.1 h z))
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (z : 𝓀[k])
    have hau : IsUnit a := (IsLocalRing.residue_ne_zero_iff_isUnit a).1 (ha ▸ z.ne_zero)
    have h1 : valuation k ((Units.map (algebraMap 𝒪[k] k : 𝒪[k] →* k) hau.unit : kˣ) : k) = 1 :=
      hv.isUnit_iff_valuation_eq_one.1 hau
    refine ⟨_, ⟨h1, ?_⟩, ?_⟩
    · rw [pow_zero]
      exact (Valuation.map_sub _ _ _).trans (by rw [h1, map_one, max_self])
    · rw [hcompat]
      have : Units.map (IsLocalRing.residue 𝒪[k] : 𝒪[k] →* 𝓀[k]) hau.unit = z := Units.ext ha
      rwa [this]

end DiscreteGroups.sglob.DzType
end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil Module ValuativeRel

set_option linter.all false

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def ResIso : Prop :=
  ∀ (L E' Ω : Type) [Field L] [NumberField L] [Field E'] [NumberField E'] [Field Ω] [Algebra L Ω] [Algebra E' Ω]
    [IsAlgClosure L Ω] [IsAlgClosure E' Ω] (g : ℕ) [Fact g.Prime] (n : ℕ) (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 L)) (hv : IsPlaceOver A v) (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w'),
    normV v = g ^ n → normV w' = g ^ n →
    ∀ (K : Type) [Field K] (red : 𝓞 E' →+* K), Function.Surjective red → RingHom.ker red = w'.asIdeal →
    ∃ κ : 𝓀[v.adicCompletion L] ≃+* K, ∀ (u : 𝒪[v.adicCompletion L]) (y : 𝓞 L) (x : 𝓞 E'),
      Valued.v ((u : v.adicCompletion L) - algebraMap L (v.adicCompletion L) (y : L)) < 1 →
      A.valuation (algebraMap L Ω (y : L) - algebraMap E' Ω (x : E')) < 1 →
      κ (IsLocalRing.residue 𝒪[v.adicCompletion L] u) = red x

theorem lpOfChar_congr {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) {χ χ' : Weil h →* ℂˣ} (e : χ = χ')
    (hχ : IsSmooth χ) (hχ' : IsSmooth χ') : WD.lpOfChar h χ hχ = WD.lpOfChar h χ' hχ' := by
  subst e; rfl

theorem regular_ne_one {g n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] {ξ : Kˣ →* ℂˣ}
    (hξ : GlobalTheory.Published.IsRegularChar g n ξ) : ξ ≠ 1 := by
  intro h1
  have := hξ 0 1 (by omega) (by omega) (by rw [h1, one_pow, one_pow])
  omega

theorem nmChar_pow {g : ℕ} [Fact g.Prime] {K : Type} [Field K] [Algebra (ZMod g) K] (χ₀ : (ZMod g)ˣ →* ℂˣ) :
    nmChar K χ₀ ^ g = nmChar K χ₀ := by
  ext z
  simp only [MonoidHom.pow_apply, nmChar, MonoidHom.comp_apply, ← map_pow]
  congr 2
  ext
  simp [ZMod.pow_card]

theorem regular_mul_nm_ne_one {g n : ℕ} [Fact g.Prime] (hn : 2 ≤ n) {K : Type} [Field K] [Algebra (ZMod g) K]
    {ξ : Kˣ →* ℂˣ} (hξ : GlobalTheory.Published.IsRegularChar g n ξ) (χ₀ : (ZMod g)ˣ →* ℂˣ) : ξ * nmChar K χ₀ ≠ 1 := by
  intro h1
  have hξe : ξ = (nmChar K χ₀)⁻¹ := eq_inv_of_mul_eq_one_left h1
  have := hξ 0 1 (by omega) (by omega) (by rw [hξe, pow_zero, pow_one, pow_one, inv_pow, nmChar_pow])
  omega

end DiscreteGroups.sglob.DzType

end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil Module ValuativeRel GlobalTheory.SmGL GlobalTheory.Whittaker

set_option linter.all false
set_option maxHeartbeats 4000000

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def ArtExists : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v), ∃ a : Weil h →* (v.adicCompletion L)ˣ, IsLocalArtin h a

theorem one_ratio (hQ : ResIso) (hA : ArtExists) (hTR : TameRec) {E E' Ω : Type} [Field E] [NumberField E]
    [IsTotallyComplex E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E'] [Algebra E Ω] [Algebra E' Ω]
    [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (g : ℕ) [Fact g.Prime]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (n : ℕ) (hn2 : 2 ≤ n)
    (hg : ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2) (hN : normV w' = g ^ n)
    (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a')
    (K : Type) [Field K] [Algebra (ZMod g) K] (red : 𝓞 E' →+* K) (hr : Function.Surjective red)
    (hk : RingHom.ker red = w'.asIdeal)
    (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (ε : EpsFamily A) (hε : IsDeligneEps ε)
    (ψ₀ : AddChar (ZMod g) Circle) (h₀ : ψ₀ ≠ 1) (ψ : AddChar (w.adicCompletion E) Circle) (hψc : Continuous ψ)
    (hψ1 : ψ ≠ 1) (y : WD h) (hirr : IsIrrWD y) (htame : IsTameWD y) (hdim : y.lpDim = n)
    (ξ : Kˣ →* ℂˣ) (hξ : GlobalTheory.Published.IsRegularChar g n ξ)
    (hξf : ∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : Kˣ), red x = z →
        Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
        y.inePol (AlgEquiv.restrictScalars E (t : G E' Ω)) =
          ∏ j ∈ Finset.range n, (X - C ((ξ (z ^ g ^ j) : ℂˣ) : ℂ)))
    (χ₀ : (ZMod g)ˣ →* ℂˣ) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ) (hlc : LiftsChar i χ₀ χ)
    (c : ℂˣ) :
    ∃ r : ℕ, 0 < r ∧
      ((ε E w h ψ ((y.lpTwist (χ.comp a) (ha.smooth hχ)).lpTwist (unrChar h c) (isSmooth_unrChar h c)) : ℂ) *
        gs ψ₀ ξ⁻¹) ^ r =
      ((ε E w h ψ (y.lpTwist (unrChar h c) (isSmooth_unrChar h c)) : ℂ) * gs ψ₀ (ξ * nmChar K χ₀)⁻¹) ^ r := by
  classical
  have hn : 0 < n := by omega
  have hq : normV w = g := normV_eq_of_padic w g i hi
  have hgw2 : ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 := g_not_mem_sq w g i hi
  have hcardK : Nat.card K = g ^ n := by
    have e : (𝓞 E' ⧸ w'.asIdeal) ≃+* K :=
      (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hr)
    rw [← hN, normV, Nat.card_congr e.toEquiv]
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hcardK]; exact (pow_pos (Fact.out : g.Prime).pos n).ne')
  haveI : IsTotallyComplex E' := isTotallyComplex_of_algebra (E := E) (L := E')

  set μ := unrChar h c with hμdef
  have hμ : IsSmooth μ := isSmooth_unrChar h c
  set χ' := χ.comp a with hχ'def
  have hχ' : IsSmooth χ' := ha.smooth hχ
  have hν₂ : IsSmooth (χ' * μ) := IsSmooth.of_le₂ hχ' hμ fun σ h1 h2 => by simp [h1, h2]
  rw [lpTwist_lpTwist y χ' μ hχ' hμ hν₂]

  obtain ⟨m, b, hyb, hbirr⟩ := hirr
  obtain ⟨m2, b2, hyb2, htame2⟩ := htame
  have hiso : b2.Iso b := WD.mk_eq_mk.mp (hyb2.trans hyb.symm)
  have htame_b : ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → b.ρ σ = 1 :=
    fun σ hσ => hiso.ρ_eq_one (htame2 σ hσ)
  have hm : finrank ℂ (Fin m → ℂ) = n := by rw [← hdim, ← hyb, WD.lpDim_mk]
  have hmn : m = n := by simpa using hm
  subst hyb
  obtain ⟨v₀, χH, hv₀, hH, hIne, hsp⟩ := exists_H_eigen g A w h w' h' i hi n hn hg hN a' ha' K red hr hk m b hbirr
    htame_b hm ξ hξf

  set H := degDvd h n with hHdef
  have hHidx : H.index = n := index_degDvd hn
  haveI hFI : H.FiniteIndex := ⟨by rw [hHidx]; exact hn.ne'⟩
  have hHo : IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H} := by
    convert isOpen_univ
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    rw [mem_degDvd, deg_ineIncl]
    exact dvd_zero _
  obtain ⟨L, hfin, hL, hHL⟩ := GlobalTheory.T.exists_localExtension_of_finiteIndex_weilSubgroup E Ω A w h H hFI hHo
  haveI : NumberField L := NumberField.of_module_finite E L
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) L⟩
  haveI : IsTotallyComplex L := isTotallyComplex_of_algebra (E := E) (L := L)
  obtain ⟨v, hv⟩ := EpsUnique.exists_place h L
  obtain ⟨ψL, hcL, h1L, hψL⟩ := EpsUnique.exists_addChar L hv hL hψc hψ1
  obtain ⟨r, hrr, hrs⟩ := GlobalTheory.T.weil_group_restriction E L Ω A w v h hv
  have hnL : n = Module.finrank E L := hHidx.symm.trans (EpsUnique.index_eq_finrank E L Ω A w h hL H hHL)
  have hrH : ∀ σ, (n : ℤ) ∣ deg (r σ) := fun σ =>
    (hHL _).2 fun x => by rw [hrr]; exact (σ : G L Ω).commutes x
  have hIfix : ∀ σ ∈ Ine (F := E) A, ∀ x : L, (σ : G E Ω) (algebraMap L Ω x) = algebraMap L Ω x := by
    intro σ hσ x
    have h1 : ineIncl h ⟨σ, hσ⟩ ∈ H := by rw [mem_degDvd, deg_ineIncl]; exact dvd_zero _
    exact (hHL _).1 h1 x
  obtain ⟨hgv, hgv2, hvN⟩ := unram_place g A w h v hv hL hIfix hgw2 hq
  rw [← hnL] at hvN

  obtain ⟨ξL₀, hξL₀⟩ := exists_eigenChar b.ρ r hv₀ (fun σ => ⟨χH (r σ), hH _ (hrH σ)⟩)
  have hξLv : ∀ σ, ((ξL₀ σ : ℂˣ) : ℂ) = χH (r σ) := fun σ =>
    DzCliff.eig_unique hv₀ (hξL₀ σ) (hH _ (hrH σ))
  obtain ⟨hs₁, hs₂, hind⟩ := eps_ind_step h hv hL hε hψc hψ1 hcL hψL r hrr hrs (hmn.trans hnL) b v₀ hsp ξL₀ hξL₀
    μ (χ' * μ) hμ hν₂

  obtain ⟨aL, haL⟩ := hA L Ω A v hv
  obtain ⟨ζ₁, hζ₁, hζ₁e⟩ := haL.factor (ξL₀ * μ.comp r) hs₁
  obtain ⟨ζ₂, hζ₂, hζ₂e⟩ := haL.factor (ξL₀ * (χ' * μ).comp r) hs₂
  have T₁ := hε.char L v hv ψL hcL h1L aL haL ζ₁ hζ₁
  have T₂ := hε.char L v hv ψL hcL h1L aL haL ζ₂ hζ₂
  rw [← lpOfChar_congr hv hζ₁e hs₁] at T₁
  rw [← lpOfChar_congr hv hζ₂e hs₂] at T₂
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (k := Ω) ((g : ℕ) : Ω)
    (Nat.sub_pos_of_lt (Nat.one_lt_pow hn.ne' (Fact.out : g.Prime).one_lt))
  obtain ⟨κ, hκ⟩ := hQ L E' Ω g n A v hv w' h' hvN hN K red hr hk
  obtain ⟨cL, ψb, hψb, htate⟩ := tate_exp_one (k := v.adicCompletion L) ψL hcL h1L

  set ζb₁ : 𝓀[v.adicCompletion L]ˣ →* ℂˣ := ξ.comp (Units.map (κ : 𝓀[v.adicCompletion L] →* K)) with hζb₁
  set ζb₂ : 𝓀[v.adicCompletion L]ˣ →* ℂˣ := (ξ * nmChar K χ₀).comp (Units.map (κ : 𝓀[v.adicCompletion L] →* K))
    with hζb₂
  have hκs : Function.Surjective (Units.map (κ : 𝓀[v.adicCompletion L] →* K)) := fun z =>
    ⟨Units.map (κ.symm : K →* 𝓀[v.adicCompletion L]) z, Units.ext (by simp)⟩
  have hζb₁1 : ζb₁ ≠ 1 := by
    intro h1
    apply regular_ne_one hn2 hξ
    ext z
    obtain ⟨z', rfl⟩ := hκs z
    have := congrArg (fun f : 𝓀[v.adicCompletion L]ˣ →* ℂˣ => ((f z' : ℂˣ) : ℂ)) h1
    simpa [hζb₁] using this
  have hζb₂1 : ζb₂ ≠ 1 := by
    intro h1
    apply regular_mul_nm_ne_one hn2 hξ χ₀
    ext z
    obtain ⟨z', rfl⟩ := hκs z
    have := congrArg (fun f : 𝓀[v.adicCompletion L]ˣ →* ℂˣ => ((f z' : ℂˣ) : ℂ)) h1
    simpa [hζb₂] using this
  have hcomp := fun x => gal_unit_compat hTR g n hn A w h w' h' v hv i hi hg hN hgv hgv2 hvN a ha a' ha' aL haL K red hr hk
    π hπ r hrr κ hκ χ₀ χ hlc x
  have hμr : ∀ t : Ine (F := E') A, μ (ineIncl h (resI t)) = 1 := fun t => by
    rw [hμdef, GlobalTheory.WeilDeligne.unrChar_apply, deg_ineIncl, zpow_zero]
  have hξr : ∀ (t : Ine (F := L) A) (t' : Ine (F := E') A) (x' : 𝓞 E') (hx0 : red x' ≠ 0),
      r (ineIncl hv t) = ineIncl h (resI t') →
      Valued.v ((a' (ineIncl h' t') : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x' : E')) < 1 →
      ξL₀ (ineIncl hv t) = ξ (Units.mk0 (red x') hx0) := by
    intro t t' x' hx0 hrt hx'
    apply Units.ext
    rw [hξLv, hrt]
    exact hIne t' x' _ rfl hx'
  have hc₁ : ∀ x : 𝒪[v.adicCompletion L]ˣ,
      ζ₁ (Units.map (algebraMap 𝒪[v.adicCompletion L] (v.adicCompletion L) :
        𝒪[v.adicCompletion L] →* v.adicCompletion L) x) =
      ζb₁ (Units.map (IsLocalRing.residue 𝒪[v.adicCompletion L] :
        𝒪[v.adicCompletion L] →* 𝓀[v.adicCompletion L]) x) := by
    intro x
    obtain ⟨t, t', x', hx0, hat, hrt, hx', hκz, -⟩ := hcomp x
    rw [← hat, ← MonoidHom.comp_apply, ← hζ₁e, hζb₁, MonoidHom.comp_apply, hκz, MonoidHom.mul_apply,
      MonoidHom.comp_apply, hrt, hμr, mul_one, hξr t t' x' hx0 hrt hx']
  have hc₂ : ∀ x : 𝒪[v.adicCompletion L]ˣ,
      ζ₂ (Units.map (algebraMap 𝒪[v.adicCompletion L] (v.adicCompletion L) :
        𝒪[v.adicCompletion L] →* v.adicCompletion L) x) =
      ζb₂ (Units.map (IsLocalRing.residue 𝒪[v.adicCompletion L] :
        𝒪[v.adicCompletion L] →* 𝓀[v.adicCompletion L]) x) := by
    intro x
    obtain ⟨t, t', x', hx0, hat, hrt, hx', hκz, hχz⟩ := hcomp x
    rw [← hat, ← MonoidHom.comp_apply, ← hζ₂e, hζb₂, MonoidHom.comp_apply, hκz, MonoidHom.mul_apply,
      MonoidHom.comp_apply, MonoidHom.mul_apply, hχ'def, MonoidHom.comp_apply, hχz, hrt, hμr, mul_one,
      hξr t t' x' hx0 hrt hx', MonoidHom.mul_apply]
    rfl
  have hE₁ := htate ζ₁ ζb₁ (hasExponent_one_of_res ζ₁ ζb₁ hc₁ hζb₁1) hc₁ _ T₁
  have hE₂ := htate ζ₂ ζb₂ (hasExponent_one_of_res ζ₂ ζb₂ hc₂ hζb₂1) hc₂ _ T₂

  let ψK : AddChar K Circle := ψb.compAddMonoidHom (κ.symm : K ≃+* 𝓀[v.adicCompletion L]).toAddMonoidHom
  obtain ⟨β, hβ⟩ := addChar_eq_trace ψ₀ h₀ ψK
  have hψbK : ∀ z : 𝓀[v.adicCompletion L], ψb z = ψ₀ (Algebra.trace (ZMod g) K (β * κ z)) := fun z => by
    rw [← hβ]; simp [ψK]
  have hβ0 : β ≠ 0 := by
    intro h0
    apply hψb
    ext z
    rw [hψbK, h0, zero_mul, map_zero, AddChar.map_zero_eq_one]
    rfl
  set β' : Kˣ := Units.mk0 β hβ0 with hβ'
  have key : ∀ η : Kˣ →* ℂˣ, ∑ᶠ z : 𝓀[v.adicCompletion L]ˣ,
      ((((η.comp (Units.map (κ : 𝓀[v.adicCompletion L] →* K))) z)⁻¹ : ℂˣ) : ℂ) * (ψb (z : 𝓀[v.adicCompletion L]) : ℂ) =
      (η β' : ℂ) * gs ψ₀ η⁻¹ := by
    intro η
    let e : 𝓀[v.adicCompletion L]ˣ ≃ Kˣ := (Units.mapEquiv (κ : 𝓀[v.adicCompletion L] ≃* K)).toEquiv
    have hfe := finsum_comp_equiv e (f := fun z' : Kˣ => (((η z')⁻¹ : ℂˣ) : ℂ) *
      (ψ₀ (Algebra.trace (ZMod g) K ((β' : K) * (z' : K))) : ℂ))
    refine (finsum_congr fun z => ?_).trans (hfe.trans (gs_scaled ψ₀ η β'))
    have he : e z = Units.map (κ : 𝓀[v.adicCompletion L] →* K) z := rfl
    simp only [MonoidHom.comp_apply, he, hψbK, hβ', Units.val_mk0, Units.coe_map, MonoidHom.coe_coe]
  have hS₁ : ∑ᶠ z : 𝓀[v.adicCompletion L]ˣ, (((ζb₁ z)⁻¹ : ℂˣ) : ℂ) * (ψb (z : 𝓀[v.adicCompletion L]) : ℂ) =
      (ξ β' : ℂ) * gs ψ₀ ξ⁻¹ := by rw [hζb₁]; exact key ξ
  have hS₂ : ∑ᶠ z : 𝓀[v.adicCompletion L]ˣ, (((ζb₂ z)⁻¹ : ℂˣ) : ℂ) * (ψb (z : 𝓀[v.adicCompletion L]) : ℂ) =
      ((ξ * nmChar K χ₀) β' : ℂ) * gs ψ₀ (ξ * nmChar K χ₀)⁻¹ := by rw [hζb₂]; exact key (ξ * nmChar K χ₀)
  rw [hS₁] at hE₁
  rw [hS₂] at hE₂

  obtain ⟨σc, hσc⟩ := haL.surj cL
  have hz1 : ζ₁ cL = ξL₀ σc * μ (r σc) := by
    rw [← hσc, ← MonoidHom.comp_apply, ← hζ₁e, MonoidHom.mul_apply, MonoidHom.comp_apply]
  have hz2 : ζ₂ cL = ζ₁ cL * χ' (r σc) := by
    rw [hz1, ← hσc, ← MonoidHom.comp_apply, ← hζ₂e, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.mul_apply]
    rw [mul_comm (χ' (r σc)) (μ (r σc)), mul_assoc]

  have hind' := congrArg (fun u : ℂˣ => (u : ℂ)) hind
  simp only [Units.val_mul] at hind'
  rw [hE₁, hE₂] at hind'
  rw [WD.lpTwist_mk, WD.lpTwist_mk]
  set Q := (resCard (v.adicCompletion L) : ℂ) ^ (-(1 : ℂ) / 2) with hQdef
  have hQ0 : Q ≠ 0 := by
    rw [hQdef, Ne, Complex.cpow_eq_zero_iff, not_and_or]
    left
    rw [resCard_eq_normV v, hvN]
    exact_mod_cast (pow_pos (Fact.out : g.Prime).pos n).ne'
  have hz2' : ((ζ₂ cL : ℂˣ) : ℂ) = ((ζ₁ cL : ℂˣ) : ℂ) * ((χ' (r σc) : ℂˣ) : ℂ) := by rw [hz2, Units.val_mul]
  have hη2 : (((ξ * nmChar K χ₀) β' : ℂˣ) : ℂ) = ((ξ β' : ℂˣ) : ℂ) * ((nmChar K χ₀ β' : ℂˣ) : ℂ) := by
    rw [MonoidHom.mul_apply, Units.val_mul]
  simp only [Units.val_inv_eq_inv_val] at hind'
  rw [hz2', hη2] at hind'
  have hz10 : ((ζ₁ cL : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hca0 : ((χ' (r σc) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hxb0 : ((ξ β' : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hρ0 := liftsChar_pow i hi χ₀ χ hlc (a (r σc))
  have hnb : (nmChar K χ₀ β') ^ (g - 1) = 1 := by
    rw [nmChar, MonoidHom.comp_apply, ← map_pow, ZMod.units_pow_card_sub_one_eq_one, map_one]
  generalize (ε E w h ψ (WD.mk (b.twist μ hμ)) : ℂ) = A1 at hind' ⊢
  generalize (ε E w h ψ (WD.mk (b.twist (χ' * μ) hν₂)) : ℂ) = A2 at hind' ⊢
  generalize gs ψ₀ ξ⁻¹ = G1 at hind' ⊢
  generalize gs ψ₀ (ξ * nmChar K χ₀)⁻¹ = G2 at hind' ⊢
  have hca1 : ((χ' (r σc) : ℂˣ) : ℂ) ^ (g - 1) = 1 := by
    have := congrArg (fun u : ℂˣ => (u : ℂ)) hρ0
    simpa [hχ'def, Units.val_pow_eq_pow_val] using this
  have hnb1 : ((nmChar K χ₀ β' : ℂˣ) : ℂ) ^ (g - 1) = 1 := by
    have := congrArg (fun u : ℂˣ => (u : ℂ)) hnb
    simpa [Units.val_pow_eq_pow_val] using this
  generalize ((ζ₁ cL : ℂˣ) : ℂ) = z1 at hind' hz10
  generalize ((χ' (r σc) : ℂˣ) : ℂ) = ca at hind' hca0 hca1
  generalize ((ξ β' : ℂˣ) : ℂ) = xb at hind' hxb0
  generalize ((nmChar K χ₀ β' : ℂˣ) : ℂ) = nb at hind' hnb1
  have hQ' : Q * z1⁻¹ * xb ≠ 0 := mul_ne_zero (mul_ne_zero hQ0 (inv_ne_zero hz10)) hxb0
  have e3 : A2 * (Q * z1⁻¹ * (xb * G1)) = (Q * z1⁻¹ * xb) * (A2 * G1) := by ring
  have e4 : A1 * (Q * (z1 * ca)⁻¹ * (xb * nb * G2)) = (Q * z1⁻¹ * xb) * (ca⁻¹ * nb * (A1 * G2)) := by
    rw [mul_inv]; ring
  rw [e3, e4] at hind'
  have keyr : A2 * G1 = ca⁻¹ * nb * (A1 * G2) := (mul_left_cancel₀ hQ' hind').symm
  have hg2 : 2 ≤ g := (Fact.out : g.Prime).two_le
  refine ⟨g - 1, by omega, ?_⟩
  have hρ : (ca⁻¹ * nb) ^ (g - 1) = 1 := by
    rw [mul_pow, inv_pow, hca1, hnb1, inv_one, one_mul]
  rw [keyr, mul_pow, hρ, one_mul]

end DiscreteGroups.sglob.DzType

end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands TensorProduct Module

namespace DiscreteGroups.sglob.DzType

section Split

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem gsplit_tensor_sum {V V' V'' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] [AddCommGroup V''] [Module ℂ V'']
    [FiniteDimensional ℂ V''] (a : WDRep h V) (b : WDRep h V') (c : WDRep h V'') :
    (a.tensor (b.sum c)).Iso ((a.tensor b).sum (a.tensor c)) := by
  refine ⟨TensorProduct.prodRight ℂ ℂ V V' V'', fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y => obtain ⟨y1, y2⟩ := y; simp
    | add x y hx hy => simp only [map_add, hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y => obtain ⟨y1, y2⟩ := y; simp
    | add x y hx hy => simp only [map_add, hx, hy]

theorem gsplit_lpChar_lpSum (x y z : WD h) :
    x.lpChar (y.lpSum z) = (x.lpChar y).lpSum (x.lpChar z) := by
  obtain ⟨n1, a, rfl⟩ := x.exists_rep
  obtain ⟨n2, b, rfl⟩ := y.exists_rep
  obtain ⟨n3, c, rfl⟩ := z.exists_rep
  rw [WD.lpSum_mk, WD.lpChar_mk, WD.lpChar_mk, WD.lpChar_mk, WD.lpSum_mk]
  exact WD.sound (gsplit_tensor_sum a b c)

def gsplitEquiv (n : ℕ) : (Fin (n + 1) → ℂ) ≃ₗ[ℂ] (Fin 1 → ℂ) × (Fin n → ℂ) where
  toFun v := (fun _ => v 0, fun j => v j.succ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun p := Fin.cons (p.1 0) p.2
  left_inv v := Fin.cons_self_tail v
  right_inv p := by
    obtain ⟨p1, p2⟩ := p
    refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
    · rw [Subsingleton.elim i 0]
      simp
    · simp

theorem gsplitEquiv_apply (n : ℕ) (v : Fin (n + 1) → ℂ) :
    gsplitEquiv n v = (fun _ => v 0, fun j => v j.succ) := rfl

theorem gsplit_diag_succ {n : ℕ} (c : Fin (n + 1) → ℂˣ) :
    WD.mk (WDRep.diag h c) =
      (WD.lpOfChar h (unrChar h (c 0)) (isSmooth_unrChar h _)).lpSum
        (WD.mk (WDRep.diag h fun j : Fin n => c j.succ)) := by
  rw [WD.lpOfChar, WD.lpSum_mk]
  refine WD.sound ⟨gsplitEquiv n, fun σ v => ?_, fun v => ?_⟩
  · refine Prod.ext (funext fun i => ?_) (funext fun j => ?_) <;> simp [gsplitEquiv_apply]
  · simp only [gsplitEquiv_apply, WDRep.diag_N, WDRep.sum_N, WDRep.ofChars_N, LinearMap.zero_apply,
      LinearMap.prodMap_apply]
    rfl

theorem lpSum_self_of_dim_zero (y : WD h) (hy : y.lpDim = 0) : y.lpSum y = y := by
  obtain ⟨m, a, rfl⟩ := y.exists_rep
  rw [WD.lpDim_mk, Module.finrank_fin_fun] at hy
  subst hy
  rw [WD.lpSum_mk]
  exact WD.sound ⟨LinearEquiv.ofFinrankEq _ _ (by simp), fun _ _ => Subsingleton.elim _ _,
    fun _ => Subsingleton.elim _ _⟩

theorem epsilon_eq_one_of_dim_zero {ε : EpsFamily A} (hε : IsDeligneEps ε) (ψ : AddChar (w.adicCompletion E) Circle)
    (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (y : WD h) (hy : y.lpDim = 0) : ε E w h ψ y = 1 := by
  have h1 := hε.add E w h ψ hψ hψ1 y y
  rw [lpSum_self_of_dim_zero y hy] at h1
  exact mul_left_cancel (a := ε E w h ψ y) (by rw [mul_one]; exact h1.symm)

theorem lpChar_diag_dim_zero (x : WD h) (c : Fin 0 → ℂˣ) : (x.lpChar (WD.mk (WDRep.diag h c))).lpDim = 0 := by
  obtain ⟨m, a, rfl⟩ := x.exists_rep
  rw [WD.lpChar_mk, WD.lpDim_mk, Module.finrank_tensorProduct]
  simp

theorem gsplit_eps {ε : EpsFamily A} (hε : IsDeligneEps ε) (ψ : AddChar (w.adicCompletion E) Circle)
    (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (x : WD h) :
    ∀ (n : ℕ) (c : Fin n → ℂˣ), ε E w h ψ (x.lpChar (WD.mk (WDRep.diag h c))) =
      ∏ j, ε E w h ψ (x.lpTwist (unrChar h (c j)) (isSmooth_unrChar h (c j)))
  | 0, c => by
    rw [Fin.prod_univ_zero]
    exact epsilon_eq_one_of_dim_zero hε ψ hψ hψ1 _ (lpChar_diag_dim_zero x c)
  | n + 1, c => by
    rw [gsplit_diag_succ, gsplit_lpChar_lpSum, hε.add E w h ψ hψ hψ1, lpChar_lpOfChar,
      gsplit_eps hε ψ hψ hψ1 x n, Fin.prod_univ_succ]

end Split

theorem eps_unr_split {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) (u : WD h) (hu : u.unr) :
    ∃ c : Fin u.lpDim → ℂˣ, ∀ ε : EpsFamily A, IsDeligneEps ε →
      ∀ ψ : AddChar (w.adicCompletion E) Circle, Continuous ψ → ψ ≠ 1 →
      ∀ x : WD h, ε E w h ψ (x.lpChar u) =
        ∏ j, ε E w h ψ (x.lpTwist (unrChar h (c j)) (isSmooth_unrChar h (c j))) := by
  obtain ⟨n, c, rfl⟩ := Unram.exists_diag hu
  have hn : (WD.mk (WDRep.diag h c)).lpDim = n := by rw [WD.lpDim_mk, Module.finrank_fin_fun]
  refine ⟨fun j => c (Fin.cast hn j), fun ε hε ψ hψ hψ1 x => ?_⟩
  rw [gsplit_eps hε ψ hψ hψ1 x n c]
  exact (Fintype.prod_equiv (finCongr hn) _ _ fun j => rfl).symm

end DiscreteGroups.sglob.DzType
end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil Module ValuativeRel GlobalTheory.SmGL GlobalTheory.Whittaker

set_option linter.all false

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem resIso_holds : ResIso :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ g _ n A v hv w' h' hvN hwN K _ red hr hk =>
    exists_resIso g n A v hv w' h' hvN hwN K red hr hk

theorem pow_prod_eq {ι : Type*} [Fintype ι] (R : ι → ℕ) (F1 F2 : ι → ℂ) (hF : ∀ j, F1 j ^ R j = F2 j ^ R j) :
    (∏ j, F1 j) ^ (∏ j, R j) = (∏ j, F2 j) ^ (∏ j, R j) := by
  rw [← Finset.prod_pow, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun j _ => ?_
  obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem R (Finset.mem_univ j)
  rw [hd, pow_mul, pow_mul, hF]

theorem galEps_of_art (hA : ArtExists) (hT : TameRec) : GalEps := by
  intro E E' Ω _ _ _ _ _ _ _ _ _ _ _ _ g _ A w h w' h' i hi n hn2 hg hN a' ha' K _ _ red hr hk a ha ε hε ψ₀ h₀ ψ
    hψc hψ1 y hirr htame hdim ξ hξ hξf u hu χ₀ χ hχ hlc
  obtain ⟨c, hc⟩ := eps_unr_split h u hu
  rw [hc ε hε ψ hψc hψ1, hc ε hε ψ hψc hψ1]
  have hj := fun j => one_ratio resIso_holds hA hT g A w h w' h' i hi n hn2 hg hN a' ha' K red hr hk a ha ε hε ψ₀ h₀
    ψ hψc hψ1 y hirr htame hdim ξ hξ hξf χ₀ χ hχ hlc (c j)
  choose R hR0 hR using hj
  refine ⟨∏ j, R j, Finset.prod_pos fun j _ => hR0 j, ?_⟩
  have e : ∀ (e' : Fin u.lpDim → ℂˣ) (G : ℂ), ((∏ j, e' j : ℂˣ) : ℂ) * G ^ u.lpDim = ∏ j, ((e' j : ℂ) * G) := by
    intro e' G
    rw [Units.coe_prod, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [e, e]
  exact pow_prod_eq R _ _ hR



end DiscreteGroups.sglob.DzType

end
end
