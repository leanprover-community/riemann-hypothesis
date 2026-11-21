import Mathlib
import Formalism.LocalToGlobal.Columns.AtTOwedU

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Moves

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem Deco.Ok.up_rep {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (q : 𝓞 E) {Q : HeightOneSpectrum (𝓞 E)}
    (hQ : Q ≠ P.1) {x : Sp E n} (hx : x ∈ d.N) (hfx : d.f P x = 1) :
    ∃ y ∈ Q.asIdeal • d.N, y ∈ d.N ∧ d.f P y = 1 ∧ d.up P q x = d.up P q y := by
  obtain ⟨a, ha, b, hb, hab⟩ := exists_coprime hQ
  have hmk : Ideal.Quotient.mk P.1.asIdeal a = 1 := by
    rw [← map_one (Ideal.Quotient.mk P.1.asIdeal), Ideal.Quotient.eq, ← hab]
    simpa using Ideal.neg_mem_iff _ |>.2 hb
  refine ⟨a • x, Submodule.smul_mem_smul ha hx, d.N.smul_mem a hx, ?_, ?_⟩
  · rw [hd.f_smul P a x (le_locP _ _ hx), hmk, hfx, one_mul]
  · apply Deco.up_congr
    have : x - a • x = b • x := by
      rw [show b = 1 - a by rw [← hab]; ring, sub_smul, one_smul]
    rw [this]
    exact Submodule.smul_mem_smul hb hx

theorem Deco.IsUp.sameAt {d d' : Deco E n ST SG} (hd : d.Ok) {P : ST} (hP : MoveHyp ST SG P) {q : 𝓞 E}
    (h : Deco.IsUp P q d d') {Q : HeightOneSpectrum (𝓞 E)} (hQ : Q ≠ P.1) (hQ' : Q ≠ conjPrime₂ P.1) :
    SameAt Q d.N d'.N := by
  obtain ⟨x, hx, -, rfl⟩ := h
  exact (upN_spec hd.lat hd.uni P.1 hP.ne hx).2.2.1 Q hQ hQ'

theorem Deco.IsUp.f_ne {d d' : Deco E n ST SG} {P : ST} {q : 𝓞 E} (h : Deco.IsUp P q d d') {Q : ST}
    (hQ : Q ≠ P) : d'.f Q = d.f Q := by
  obtain ⟨x, _, _, rfl⟩ := h
  simp only [Deco.up, Function.update, dif_neg hQ]

theorem Deco.IsUp.be_eq {d d' : Deco E n ST SG} {P : ST} {q : 𝓞 E} (h : Deco.IsUp P q d d') : d'.be = d.be := by
  obtain ⟨x, _, _, rfl⟩ := h
  rfl

theorem Deco.IsUp.pushout {d₀ d d₂ : Deco E n ST SG} (hd₀ : d₀.Ok) {P P' : ST} (hP : MoveHyp ST SG P)
    (hP' : MoveHyp ST SG P') (hne : P ≠ P') {q q' : 𝓞 E} (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2)
    (hq' : q' ∈ P'.1.asIdeal) (hq2' : q' ∉ P'.1.asIdeal ^ 2) (h1 : Deco.IsUp P' q' d₀ d)
    (h2 : Deco.IsUp P q d₀ d₂) : ∃ d₁ : Deco E n ST SG, d₁.Ok ∧ Deco.IsUp P q d d₁ ∧ Deco.IsUp P' q' d₂ d₁ := by
  obtain ⟨x₀', hx₀', hfx₀', rfl⟩ := h1
  obtain ⟨x₀, hx₀, hfx₀, rfl⟩ := h2
  obtain ⟨x, hxQ, hx, hfx, e⟩ := hd₀.up_rep P q (hP'.st P).symm hx₀ hfx₀
  obtain ⟨x', hxQ', hx', hfx', e'⟩ := hd₀.up_rep P' q' (hP.st P').symm hx₀' hfx₀'
  rw [e, e']
  obtain ⟨-, -, -, -, ge⟩ := upN_spec hd₀.lat hd₀.uni P.1 hP.ne hx
  obtain ⟨-, -, -, -, ge'⟩ := upN_spec hd₀.lat hd₀.uni P'.1 hP'.ne hx'
  have hx1 : x ∈ upN P'.1.asIdeal d₀.N x' :=
    ge' (Submodule.smul_mono le_rfl (le_sup_left : d₀.N ≤ upA P'.1.asIdeal d₀.N x') hxQ)
  have hx1' : x' ∈ upN P.1.asIdeal d₀.N x :=
    ge (Submodule.smul_mono le_rfl (le_sup_left : d₀.N ≤ upA P.1.asIdeal d₀.N x) hxQ')
  have ok2 : (d₀.up P q x).Ok := hd₀.up P hP hq hq2 hx hfx
  have f2 : (d₀.up P q x).f P' x' = 1 := by
    rw [Deco.up_f_ne _ _ _ _ hne.symm]
    exact hfx'
  have f1 : (d₀.up P' q' x').f P x = 1 := by
    rw [Deco.up_f_ne _ _ _ _ hne]
    exact hfx
  exact ⟨(d₀.up P q x).up P' q' x', ok2.up P' hP' hq' hq2' hx1' f2,
    ⟨x, hx1, f1, hd₀.up_up_comm hP hP' hne q q' hx hx' hx1 hx1'⟩, ⟨x', hx1', f2, rfl⟩⟩

theorem locP_kerAt_eq_of_sameAt {d d₁ : Deco E n ST SG} (hd : d.Ok) (hd₁ : d₁.Ok) (P' : ST)
    (hs : SameAt P'.1 d.N d₁.N) (hf : d₁.f P' = d.f P') :
    localization₂ P'.1.asIdeal (d.kerAt P') = localization₂ P'.1.asIdeal (d₁.kerAt P') := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := hs
  apply le_antisymm
  · refine localization_le_of_smul_mem ha' fun x hx => ?_
    obtain ⟨hxN, hx0⟩ := (hd.mem_kerAt P' x).1 hx
    rw [hd₁.mem_kerAt, hf, hd.f_smul P' a' x (le_locP _ _ hxN), hx0, mul_zero]
    exact ⟨h2 x hxN, rfl⟩
  · refine localization_le_of_smul_mem ha fun x hx => ?_
    obtain ⟨hxN, hx0⟩ := (hd₁.mem_kerAt P' x).1 hx
    rw [hd.mem_kerAt, ← hf, hd₁.f_smul P' a x (le_locP _ _ hxN), hx0, mul_zero]
    exact ⟨h1 x hxN, rfl⟩

theorem Deco.IsUp.pullback {d d₁ d₂ : Deco E n ST SG} (hd : d.Ok) (hd₂ : d₂.Ok) {P P' : ST}
    (hP : MoveHyp ST SG P) (hP' : MoveHyp ST SG P') (hne : P ≠ P') {q q' : 𝓞 E} (hq : q ∈ P.1.asIdeal)
    (hq2 : q ∉ P.1.asIdeal ^ 2) (hq' : q' ∈ P'.1.asIdeal) (hq2' : q' ∉ P'.1.asIdeal ^ 2)
    (h1 : Deco.IsUp P q d d₁) (h2 : Deco.IsUp P' q' d₂ d₁) :
    ∃ d₀ : Deco E n ST SG, d₀.Ok ∧ Deco.IsUp P' q' d₀ d ∧ Deco.IsUp P q d₀ d₂ := by
  classical
  have hne1 : P'.1 ≠ P.1 := fun h => hne (Subtype.ext h).symm
  have hd₁ : d₁.Ok := by
    obtain ⟨x, hx, hfx, rfl⟩ := h1
    exact hd.up P hP hq hq2 hx hfx
  have hs : SameAt P'.1 d.N d₁.N := h1.sameAt hd hP hne1 (hP.st P')
  have hf : d₁.f P' = d.f P' := h1.f_ne hne.symm
  obtain ⟨dn1, dn2⟩ := h2.isDn hd₂ hP' hq' hq2'
  have hN2 : d₂.N = d₁.dnN P' := congrArg Deco.N dn1
  have hloc : localization₂ P'.1.asIdeal (d.dnN P') = localization₂ P'.1.asIdeal d₂.N := by
    rw [hN2, (hd.dnN_spec P' hP'.ne).2.2.2, (hd₁.dnN_spec P' hP'.ne).2.2.2]
    exact locP_kerAt_eq_of_sameAt hd hd₁ P' hs hf
  have ok0 : (d.dn P' (d₂.f P')).Ok := by
    refine hd.dn P' hP' ?_ ?_ ?_ ?_
    · intro x hx y hy
      rw [hloc] at hx hy
      exact hd₂.f_add P' x hx y hy
    · intro a x hx
      rw [hloc] at hx
      exact hd₂.f_smul P' a x hx
    · intro x hx
      rw [hloc] at hx
      exact hd₂.f_off P' x hx
    · obtain ⟨x, hx, hx0⟩ := hd₂.f_ne P'
      have hx' : x ∈ localization₂ P'.1.asIdeal (d.dnN P') := by
        rw [hloc]
        exact le_locP _ _ hx
      obtain ⟨s, hs, hsx⟩ := (mem_locP _ _ _).1 hx'
      refine ⟨s • x, hsx, ?_⟩
      rw [hd₂.f_smul P' s x (le_locP _ _ hx)]
      exact mul_ne_zero (mk_ne_zero hs) hx0
  have f0 : (d.dn P' (d₂.f P')).f P' = d₂.f P' := by simp [Deco.dn]
  have dn0 : Deco.IsDn P' q' d (d.dn P' (d₂.f P')) := by
    refine ⟨by rw [f0], ?_⟩
    intro e he hfe
    rw [f0]
    obtain ⟨a, ha, a', ha', k1, k2⟩ := hs

    have := P'.1.isMaximal
    obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv (mk_ne_zero ha')
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hmem : (t * a') • e ∈ d₁.N := by
      rw [mul_smul]
      exact d₁.N.smul_mem t (k2 e he)
    have hmk : Ideal.Quotient.mk P'.1.asIdeal (t * a') = 1 := by
      rw [map_mul, mul_comm]
      exact hb
    have hval : d₁.f P' ((t * a') • e) = 1 := by
      rw [hf, hd.f_smul P' _ e (le_locP _ _ he), hmk, hfe, one_mul]
    have h3 := dn2 _ hmem hval
    have hqe : q' • e ∈ d₂.at P'.1 := by
      refine (mem_locP _ _ _).2 ⟨t * a', ?_, ?_⟩
      · intro hm
        have : Ideal.Quotient.mk P'.1.asIdeal (t * a') = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
        rw [hmk] at this
        exact one_ne_zero this
      · rw [smul_comm, hN2]
        refine (le_sup_left : d₁.kerAt P' ≤ d₁.dnN P') ?_
        rw [hd₁.mem_kerAt]
        refine ⟨d₁.N.smul_mem q' hmem, ?_⟩
        rw [hd₁.f_smul P' q' _ (le_locP _ _ hmem), Ideal.Quotient.eq_zero_iff_mem.2 hq', zero_mul]
    rw [smul_comm, hd₂.f_smul P' _ _ hqe, hmk, one_mul] at h3
    exact h3
  have up0 : Deco.IsUp P' q' (d.dn P' (d₂.f P')) d := dn0.isUp ok0 hd hP' hq' hq2'
  obtain ⟨e₂, oke, k1, k2⟩ := Deco.IsUp.diamond ok0 hP' hP hne.symm hq' hq2' hq hq2 up0 h1
  have he : e₂ = d₂ := by
    have a := (k2.isDn oke hP' hq' hq2').1
    have b : e₂.f P' = d₂.f P' := (k1.f_ne hne.symm).trans f0
    rw [a, b]
    exact dn1.symm
  exact ⟨_, ok0, up0, he ▸ k1⟩

theorem Deco.IsUp.top_unique {d d₂ d₁ e₁ : Deco E n ST SG} (hd : d.Ok) (hd₂ : d₂.Ok) (hd₁ : d₁.Ok) (he₁ : e₁.Ok)
    {P P' : ST} (hP : MoveHyp ST SG P) (hP' : MoveHyp ST SG P') (hne : P ≠ P') {q q' : 𝓞 E}
    (h1 : Deco.IsUp P q d d₁) (h2 : Deco.IsUp P' q' d₂ d₁) (k1 : Deco.IsUp P q d e₁)
    (k2 : Deco.IsUp P' q' d₂ e₁) : d₁ = e₁ := by
  have hne1 : P'.1 ≠ P.1 := fun h => hne (Subtype.ext h).symm
  have atP' : SameAt P'.1 d₁.N e₁.N := (h1.sameAt hd hP hne1 (hP.st P')).symm.trans (k1.sameAt hd hP hne1 (hP.st P'))
  ext1
  · refine isUnimodular_eq_of_sameAt hd₁.uni he₁.uni fun Q => ?_
    by_cases c1 : Q = P'.1
    · exact Or.inl (c1 ▸ atP')
    · by_cases c2 : Q = conjPrime₂ P'.1
      · right
        rw [c2, conjP_conjP_eq]
        exact atP'
      · exact Or.inl ((h2.sameAt hd₂ hP' c1 c2).symm.trans (k2.sameAt hd₂ hP' c1 c2))
  · funext Q
    by_cases c : Q = P'
    · subst c
      rw [h1.f_ne hne.symm, k1.f_ne hne.symm]
    · rw [h2.f_ne c, k2.f_ne c]
  · rw [h1.be_eq, k1.be_eq]

theorem Deco.IsUp.bot_unique {d d₂ d₀ e₀ : Deco E n ST SG} (hd₀ : d₀.Ok) (he₀ : e₀.Ok) {P P' : ST}
    (hP' : MoveHyp ST SG P') (hne : P ≠ P') {q q' : 𝓞 E} (hq' : q' ∈ P'.1.asIdeal)
    (hq2' : q' ∉ P'.1.asIdeal ^ 2) (h1 : Deco.IsUp P' q' d₀ d) (h2 : Deco.IsUp P q d₀ d₂)
    (k1 : Deco.IsUp P' q' e₀ d) (k2 : Deco.IsUp P q e₀ d₂) : d₀ = e₀ := by
  have a1 := (h1.isDn hd₀ hP' hq' hq2').1
  have a2 := (k1.isDn he₀ hP' hq' hq2').1
  rw [a1, a2, ← h2.f_ne hne.symm, ← k2.f_ne hne.symm]


end Moves

section Ops

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG)


end Ops

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)


end Cols

end Formalism.L2.Col
