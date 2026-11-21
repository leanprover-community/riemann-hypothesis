import Formalism.LocalToGlobal.Columns.OcbPhiFIdxFPos
import Formalism.LocalToGlobal.Columns.FirstUnfoldingEqZeroOfNotIntegral
import Formalism.LocalToGlobal.Columns.RecLevelSym

section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section E1

variable {E K L : Type} [Field E] [NumberField E] [Field K] [CharZero K] [Field L] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

variable (P) in

def ookRed {n' n : ℕ} (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) :
    (Fin n' → 𝓞 E ⧸ P.asIdeal) →ₗ[𝓞 E ⧸ P.asIdeal] (Fin n → 𝓞 E ⧸ P.asIdeal) :=
  Matrix.toLin' (Matrix.of fun (l : Fin n) (s : Fin n') => redP P (Loc.atN (xj (Loc.eN E n' s.1)) l.1))

theorem ookRed_spec {n' n : ℕ} (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) : ocbXRed P xj (ookRed P xj) := by
  intro l s hl hs
  unfold ookRed
  rw [ocbS_atN_toLin' _ hl hs]
  rfl

theorem ookAtN_add {N : ℕ} (v w : Fin N → E) (l : ℕ) : Loc.atN (v + w) l = Loc.atN v l + Loc.atN w l := by
  unfold Loc.atN
  split_ifs
  · rfl
  · rw [add_zero]

theorem xInt_of_firstUnfolding_ne_zero {n' c' n c : ℕ} (hc' : c' = c + 1) (Ψ : Loc.SF E K (n' + c') (n + c))
    (hsupp : ∀ y, Ψ y ≠ 0 → ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s))
    (psi : E → K) (vals : Finset E) (wt : K) (xj : (Fin n' → E) →ₗ[E] (Fin n → E))
    (h : Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi vals wt Ψ xj ≠ 0) : ocbXInt P xj := by
  by_contra hx
  exact h (firstUnfolding_eq_zero_of_not_integral hc' Ψ hsupp psi vals wt xj hx)

theorem firstUnfolding_reduction_independent (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hp : q.Prime)
    (hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = q) {n' c' n c : ℕ} (hc' : c' = c + 1) (σ : K →+* L)
    (Ψ : Loc.SF E K (n' + c') (n + c)) (Ψr : Loc.SF (𝓞 E ⧸ P.asIdeal) L (n' + (c + 1)) (n + c))
    (hsupp : ∀ y, Ψ y ≠ 0 → ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s))
    (hred : ∀ y ybar, (∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s)) →
      (∀ l s, l < n + c → s < n' + c' → Loc.atN (ybar (Loc.eN _ _ s)) l = redP P (ocbBEnt n' n q y l s)) → σ (Ψ y) = Ψr ybar)
    (psi : E → K) (ψ₀ : 𝓞 E ⧸ P.asIdeal → L) (hpsi : ∀ a, IntAt P a → σ (psi (a / (q : E))) = ψ₀ (redP P a))
    {A B A' B' : ℕ} (hA : c + 1 ≤ A) (hB : 1 ≤ B) (hA' : c + 1 ≤ A') (hB' : 1 ≤ B') (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) :
    Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi (LocE.valsQ E q A' B') ((q : K) ^ B')⁻¹ Ψ xj =
      Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi (LocE.valsQ E q A B) ((q : K) ^ B)⁻¹ Ψ xj := by
  by_cases hx : ocbXInt P xj
  · apply σ.injective
    rw [firstUnfolding_reduction_eq hq hu hp hcard hc' σ Ψ Ψr hsupp hred psi ψ₀ hpsi hA' hB' xj (ookRed P xj) hx (ookRed_spec xj),
      firstUnfolding_reduction_eq hq hu hp hcard hc' σ Ψ Ψr hsupp hred psi ψ₀ hpsi hA hB xj (ookRed P xj) hx (ookRed_spec xj)]
  · rw [firstUnfolding_eq_zero_of_not_integral hc' Ψ hsupp psi _ _ xj hx, firstUnfolding_eq_zero_of_not_integral hc' Ψ hsupp psi _ _ xj hx]

theorem firstUnfolding_add_eq_self_of_intAt_div (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hp : q.Prime)
    (hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = q) {n' c' n c : ℕ} (hc' : c' = c + 1) (σ : K →+* L)
    (Ψ : Loc.SF E K (n' + c') (n + c)) (Ψr : Loc.SF (𝓞 E ⧸ P.asIdeal) L (n' + (c + 1)) (n + c))
    (hsupp : ∀ y, Ψ y ≠ 0 → ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s))
    (hred : ∀ y ybar, (∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s)) →
      (∀ l s, l < n + c → s < n' + c' → Loc.atN (ybar (Loc.eN _ _ s)) l = redP P (ocbBEnt n' n q y l s)) → σ (Ψ y) = Ψr ybar)
    (psi : E → K) (ψ₀ : 𝓞 E ⧸ P.asIdeal → L) (hpsi : ∀ a, IntAt P a → σ (psi (a / (q : E))) = ψ₀ (redP P a))
    {A B : ℕ} (hA : c + 1 ≤ A) (hB : 1 ≤ B) (xj z : (Fin n' → E) →ₗ[E] (Fin n → E))
    (hz : ∀ l s, l < n → s < n' → IntAt P (Loc.atN (z (Loc.eN E n' s)) l / (q : E))) :
    Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi (LocE.valsQ E q A B) ((q : K) ^ B)⁻¹ Ψ (xj + z) =
      Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi (LocE.valsQ E q A B) ((q : K) ^ B)⁻¹ Ψ xj := by
  have hq0 : (q : E) ≠ 0 := ciQ_ne_zero hu
  have hD : ∀ l s, l < n → s < n' → Loc.atN ((xj + z) (Loc.eN E n' s)) l =
      Loc.atN (xj (Loc.eN E n' s)) l + (q : E) * (Loc.atN (z (Loc.eN E n' s)) l / (q : E)) := by
    intro l s _ _
    rw [LinearMap.add_apply, ookAtN_add, mul_div_cancel₀ _ hq0]
  have hint : ocbXInt P (xj + z) ↔ ocbXInt P xj := by
    constructor
    · intro h l s hl hs
      have h1 := h l s hl hs
      rw [hD l s hl hs] at h1
      exact (ciIntAt_add_iff ((ciIntAt_q (q := q)).mul (hz l s hl hs))).1 h1
    · intro h l s hl hs
      rw [hD l s hl hs]
      exact (ciIntAt_add_iff ((ciIntAt_q (q := q)).mul (hz l s hl hs))).2 (h l s hl hs)
  by_cases hx : ocbXInt P xj
  · have hred' : ocbXRed P (xj + z) (ookRed P xj) := by
      intro l s hl hs
      rw [ookRed_spec xj l s hl hs, hD l s hl hs, redP_add_natCast_mul hq (hz l s hl hs)]
    apply σ.injective
    rw [firstUnfolding_reduction_eq hq hu hp hcard hc' σ Ψ Ψr hsupp hred psi ψ₀ hpsi hA hB (xj + z) (ookRed P xj) (hint.2 hx) hred',
      firstUnfolding_reduction_eq hq hu hp hcard hc' σ Ψ Ψr hsupp hred psi ψ₀ hpsi hA hB xj (ookRed P xj) hx (ookRed_spec xj)]
  · rw [firstUnfolding_eq_zero_of_not_integral hc' Ψ hsupp psi _ _ xj hx, firstUnfolding_eq_zero_of_not_integral hc' Ψ hsupp psi _ _ (xj + z) (fun h => hx (hint.1 h))]

end E1

section Cong

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem ookLamGvS_congr (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ r t j a : ℕ} (M M' : ℕ → ℕ → E)
    (hkr : k₀ ≤ r) (hra : r ≤ a) (hja : r + j * t ≤ a)
    (h : ∀ p p', p < a → p' < a → IntAt P (M p p') ∧ IntAt P (M' p p') ∧ redP P (M' p p') = redP P (M p p')) :
    LocE.lamGvS ψ₀ χ k₀ r t j M' = LocE.lamGvS ψ₀ χ k₀ r t j M := by
  unfold LocE.lamGvS
  congr 1
  · congr 1
    have hb1 : ∀ i ∈ Finset.range (k₀ - 1), i < a ∧ i + 1 < a := fun i hi => by simp at hi; omega
    have hb2 : ∀ i ∈ Finset.range (r - k₀ - 1), k₀ + i < a ∧ k₀ + i + 1 < a := fun i hi => by simp at hi; omega
    rw [reduction_add (ciIntAt_sum _ _ fun i hi => (h i (i + 1) (hb1 i hi).1 (hb1 i hi).2).2.1)
        (ciIntAt_sum _ _ fun i hi => (h (k₀ + i) (k₀ + i + 1) (hb2 i hi).1 (hb2 i hi).2).2.1),
      reduction_add (ciIntAt_sum _ _ fun i hi => (h i (i + 1) (hb1 i hi).1 (hb1 i hi).2).1)
        (ciIntAt_sum _ _ fun i hi => (h (k₀ + i) (k₀ + i + 1) (hb2 i hi).1 (hb2 i hi).2).1),
      redP_sum _ _ (fun i hi => (h i (i + 1) (hb1 i hi).1 (hb1 i hi).2).2.1),
      redP_sum _ _ (fun i hi => (h (k₀ + i) (k₀ + i + 1) (hb2 i hi).1 (hb2 i hi).2).2.1),
      redP_sum _ _ (fun i hi => (h i (i + 1) (hb1 i hi).1 (hb1 i hi).2).1),
      redP_sum _ _ (fun i hi => (h (k₀ + i) (k₀ + i + 1) (hb2 i hi).1 (hb2 i hi).2).1)]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun i hi => (h i (i + 1) (hb1 i hi).1 (hb1 i hi).2).2.2)
      (Finset.sum_congr rfl fun i hi => (h (k₀ + i) (k₀ + i + 1) (hb2 i hi).1 (hb2 i hi).2).2.2)
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hi' : i < j := by simpa using hi
    have hb : ∀ s : Fin t, r + i * t + s.1 < a := fun s => by
      have h1 := s.2
      have h2 : (i + 1) * t ≤ j * t := Nat.mul_le_mul_right _ hi'
      nlinarith
    apply ciUnitV_congr
    rw [redP_det (Matrix.of fun s s' : Fin t => M' (r + i * t + s.1) (r + i * t + s'.1)) (fun s s' => (h _ _ (hb s) (hb s')).2.1),
      redP_det (Matrix.of fun s s' : Fin t => M (r + i * t + s.1) (r + i * t + s'.1)) (fun s s' => (h _ _ (hb s) (hb s')).1)]
    congr 1
    ext s s'
    exact (h _ _ (hb s) (hb s')).2.2

open Classical in

theorem ookPhiGS_congr (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K)
    (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ rS r t j c' n' c n : ℕ} (x x' : HomE E (n' + c') (n + c))
    (hkr : k₀ ≤ r) (han : r + (j - 1) * t ≤ n + c)
    (hD : ∀ p p', p < n + c → p' < r + (j - 1) * t → ∃ d, IntAt P d ∧
      LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x' p p' =
        LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p p' + q * d) :
    LocE.PhiGS (P := P) q ψ₀ χ k₀ rS r t j c' n' c n x' = LocE.PhiGS (P := P) q ψ₀ χ k₀ rS r t j c' n' c n x := by
  rw [phiGS_eq, phiGS_eq]
  set M := LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x with hM
  set M' := LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x' with hM'
  set a := r + (j - 1) * t with ha
  have hra : r ≤ a := Nat.le_add_right _ _
  have k1 : ∀ p p', p < n + c → p' < a → (IntAt P (M' p p') ↔ IntAt P (M p p')) := by
    intro p p' hp hp'
    obtain ⟨d, hd, he⟩ := hD p p' hp hp'
    rw [he]
    exact ciIntAt_add_iff ((ciIntAt_q (q := q)).mul hd)
  have k2 : ∀ p p', p < n + c → p' < a → (IntAt P (M' p p' / q) ↔ IntAt P (M p p' / q)) := by
    intro p p' hp hp'
    obtain ⟨d, hd, he⟩ := hD p p' hp hp'
    rw [he, add_div, mul_div_cancel_left₀ _ hq0]
    exact ciIntAt_add_iff hd
  have k3 : ∀ p p', p < n + c → p' < a → redP P (M' p p') = redP P (M p p') := by
    intro p p' hp hp'
    obtain ⟨d, hd, he⟩ := hD p p' hp hp'
    rw [he]
    exact redP_add_natCast_mul hq hd
  have hc : symPhiCond P q k₀ rS r t j c n M' ↔ symPhiCond P q k₀ rS r t j c n M := by
    unfold symPhiCond
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨fun p p' hp hp' => (k1 p p' hp hp').1 (h1 p p' hp hp'), fun p p' h0 hp hp' => (k2 p p' hp hp').1 (h2 p p' h0 hp hp'),
        fun p' hp' => ⟨?_, fun p hp hne hc => ?_⟩, fun p p' h0 hp' hp hpp => ?_⟩
      · rw [← k3 p' p' (by omega) (by omega)]; exact (h3 p' hp').1
      · rw [← k3 p p' (by omega) (by omega)]; exact (h3 p' hp').2 p hp hne hc
      · rw [← k3 p p' (by omega) hp']; exact h4 p p' h0 hp' hp hpp
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨fun p p' hp hp' => (k1 p p' hp hp').2 (h1 p p' hp hp'), fun p p' h0 hp hp' => (k2 p p' hp hp').2 (h2 p p' h0 hp hp'),
        fun p' hp' => ⟨?_, fun p hp hne hc => ?_⟩, fun p p' h0 hp' hp hpp => ?_⟩
      · rw [k3 p' p' (by omega) (by omega)]; exact (h3 p' hp').1
      · rw [k3 p p' (by omega) (by omega)]; exact (h3 p' hp').2 p hp hne hc
      · rw [k3 p p' (by omega) hp']; exact h4 p p' h0 hp' hp hpp
  by_cases hC : symPhiCond P q k₀ rS r t j c n M
  · rw [if_pos (hc.2 hC), if_pos hC]
    have htrip : ∀ p p', p < a → p' < a → IntAt P (M p p') ∧ IntAt P (M' p p') ∧ redP P (M' p p') = redP P (M p p') :=
      fun p p' hp hp' => ⟨hC.1 p p' (by omega) hp', (hc.2 hC).1 p p' (by omega) hp', k3 p p' (by omega) hp'⟩
    congr 1
    · exact ookLamGvS_congr ψ₀ χ M M' hkr hra (le_refl _) htrip
    · congr 1
      apply ciUnitV_congr
      rw [redP_det (Matrix.of fun s s' : Fin a => M' s.1 s'.1) (fun s s' => (htrip s.1 s'.1 s.2 s'.2).2.1),
        redP_det (Matrix.of fun s s' : Fin a => M s.1 s'.1) (fun s s' => (htrip s.1 s'.1 s.2 s'.2).1)]
      congr 1
      ext s s'
      exact (htrip s.1 s'.1 s.2 s'.2).2.2
  · rw [if_neg (fun h => hC (hc.1 h)), if_neg hC]

theorem ookEntB_joinX (q : ℕ) {k₀ n' c' n c : ℕ} (hc' : c' = 1) (hc : c = 0) (hk : k₀ ≤ n') (x₀ : HomE E n' n) (y' : Sp E n)
    {p s : ℕ} (hp : p < n) (hs : s < n') :
    LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) (joinCol (c' := c') (c := c) x₀ y') p (LocE.fPos k₀ c' n' s) =
      x₀ (Pi.single ⟨s, hs⟩ 1) ⟨p, hp⟩ := by
  subst hc' hc
  have f1 : LocE.fIdx k₀ 1 n' (LocE.fPos k₀ 1 n' s) = s := ocbPhi_fIdx_fPos hk (by omega)
  have f2 : LocE.fIdx k₀ 0 n p = p := ciFIdx (Or.inl rfl) (by omega)
  unfold LocE.entB joinCol atNL
  rw [f1, f2, ciScE_lt _ hp, ciScE_lt _ hs, dif_pos (show n' < n' + 1 by omega)]
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
  rw [ciAtN_inX hp]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e1 : (LinearMap.funLeft E E (Fin.castAdd 1)) (Loc.eN E (n' + 1) s) = (Pi.single ⟨s, hs⟩ 1 : Fin n' → E) := by
    funext i
    show Loc.eN E (n' + 1) s (Fin.castAdd 1 i) = _
    unfold Loc.eN
    simp only [Fin.val_castAdd, Pi.single_apply, Fin.ext_iff]
  have e2 : Loc.eN E (n' + 1) s ⟨n', by omega⟩ = 0 := by
    unfold Loc.eN
    rw [if_neg (by simp; omega)]
  rw [e1, e2, zero_mul, add_zero, sub_zero, zpow_zero, mul_one]

theorem ookFIdx_lt {k₀ c' n' p' : ℕ} (hc' : c' = 1) (hk : k₀ ≤ n') (hp' : p' < n' + c') (hne : p' ≠ k₀) :
    LocE.fIdx k₀ c' n' p' < n' ∧ LocE.fPos k₀ c' n' (LocE.fIdx k₀ c' n' p') = p' := by
  subst hc'
  exact ⟨by unfold LocE.fIdx; split_ifs <;> omega, symFPos_fIdx hk hp'⟩

theorem ookPrX_le {k₀ rS r t n c : ℕ} :
    Loc.prX (Loc.Cbe (LocE.JGsym P q k₀ rS r t n c) 1) ≤ GLint E n P := by
  rintro g ⟨ρ, hr, hg⟩ x
  have hr' : ρ ∈ LocE.JGsym P q k₀ rS r t n c := by
    have := hr.2
    simpa [MulAut.conj_apply] using this
  rw [← ciMem_lamY (P := P) (q := q) (c := c) (fun i => i + 1) (g x), ← hg]
  exact (hr'.1 _).trans (ciMem_lamY _ _)

end Cong

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Glob

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S)

theorem ookC {m2 i : ℕ} (hm : R.m = m2 + 2) (hi : i < m2) : cOf R i = cOf R (i + 1) + 1 := by
  unfold cOf
  omega

theorem ookJat (j : ℕ) {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vGs) :
    Jat (Pr := Pr) (R := R) true j w = LocE.JGsym w (qOf w) R.k R.rS R.r R.t (R.N j) (cOf R j) := by
  unfold Jat
  rw [if_pos hw]
  rfl

def ookKap (c : LocCst X (rowSG Pr sel mu)) (i : ℕ) (P : rowSG Pr sel mu) : X.K :=
  muAt Ch sel mu c i P 1 * (muAt Ch sel mu c i P 1)⁻¹ *
    c.sq P ^ (-(LocE.vP P.1 (qOf P.1) 1) * ((R.N (i + 1) + cOf R (i + 1) : ℕ) : ℤ)) *
    c.sq P ^ (LocE.vP P.1 (qOf P.1) 1 * ((R.N i + cOf R i : ℕ) : ℤ))

theorem ookOmPhi_eq (c : LocCst X (rowSG Pr sel mu)) (hs : c.sharp = true) (i : ℕ) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    (y : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))) :
    omPhi Ch sel mu c i P 1 1 y = ookKap Ch sel mu c i P *
      LocE.PhiGS (P := P.1) (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k R.rS R.r R.t (i + 1) (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1)) y := by
  unfold omPhi
  rw [ciOm_one]
  unfold PhiAt
  rw [if_pos hP, hs, if_pos rfl]
  rfl

theorem ookSupp (c : LocCst X (rowSG Pr sel mu)) (hs : c.sharp = true) {m2 i : ℕ} (hm : R.m = m2 + 2) (hi : i < m2)
    (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) :
    ∀ y, omPhi Ch sel mu c i P 1 1 y ≠ 0 → ∀ l s, l < R.N (i + 1) + cOf R (i + 1) → s < R.N i + cOf R i →
      IntAt P.1 (ocbBEnt (R.N i) (R.N (i + 1)) (qOf P.1) y l s) := by
  intro y hy
  rw [ookOmPhi_eq Ch sel mu c hs i P hP] at hy
  exact ocbPhiGS_supp (psi0P Ch P.1) (chiP Ch P.1) (ocbRanks_step hm hi) (ookC hm hi) y (right_ne_zero_of_mul hy)

theorem ookRedPsi (hX : X.Ok) (hPr : Pr.Ok) (c : LocCst X (rowSG Pr sel mu)) (hs : c.sharp = true) {m2 i : ℕ} (hm : R.m = m2 + 2)
    (hi : i < m2) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) (σ : X.K →+* ℂ) :
    ∃ Ψr : Loc.SF (𝓞 X.E ⧸ P.1.asIdeal) ℂ (R.N i + (cOf R (i + 1) + 1)) (R.N (i + 1) + cOf R (i + 1)),
      ∀ y ybar, (∀ l s, l < R.N (i + 1) + cOf R (i + 1) → s < R.N i + cOf R i → IntAt P.1 (ocbBEnt (R.N i) (R.N (i + 1)) (qOf P.1) y l s)) →
        (∀ l s, l < R.N (i + 1) + cOf R (i + 1) → s < R.N i + cOf R i →
          Loc.atN (ybar (Loc.eN _ _ s)) l = redP P.1 (ocbBEnt (R.N i) (R.N (i + 1)) (qOf P.1) y l s)) →
        σ (omPhi Ch sel mu c i P 1 1 y) = Ψr ybar := by
  refine ⟨fun ybar => σ (ookKap Ch sel mu c i P) *
    @ocbPhiS (𝓞 X.E ⧸ P.1.asIdeal) (resField P.1) ((σ : X.K →* ℂ).compAddChar (psi0P Ch P.1))
      (fun s => (Units.map (σ : X.K →* ℂ)).comp (chiP Ch P.1 s)) R.k R.m R.t (i + 1) (R.N i) (cOf R (i + 1)) (R.N (i + 1)) ybar, ?_⟩
  intro y ybar hint hred
  rw [ookOmPhi_eq Ch sel mu c hs i P hP, map_mul]
  exact congrArg (σ (ookKap Ch sel mu c i P) * ·)
    (ocbPhiGS_red (ciQ_mem P.1) (ciQ_notMem_sq hX hPr hP) σ (psi0P Ch P.1) (chiP Ch P.1) (ocbRanks_step hm hi) (ookC hm hi) y ybar hint hred)

theorem ookE1at_indep (hX : X.Ok) (hPr : Pr.Ok) (c : LocCst X (rowSG Pr sel mu)) (hs : c.sharp = true) {m2 i : ℕ} (hm : R.m = m2 + 2)
    (hi : i < m2) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    (hψ : ∀ a, IntAt P.1 a → c.psi P (a / (qOf P.1 : X.E)) = psi0P Ch P.1 (redP P.1 a)) (σ : X.K →+* ℂ) {A' B' : ℕ}
    (hA : R.m ≤ c.A) (hB : 1 ≤ c.B) (hA' : R.m ≤ A') (hB' : 1 ≤ B') :
    E1at Ch sel mu { c with A := A', B := B' } i P 1 1 = E1at Ch sel mu c i P 1 1 := by
  funext xj
  obtain ⟨Ψr, hred⟩ := ookRedPsi Ch sel mu hX hPr c hs hm hi P hP σ
  have hAc : cOf R (i + 1) + 1 ≤ c.A := by unfold cOf; omega
  have hAc' : cOf R (i + 1) + 1 ≤ A' := by unfold cOf; omega
  exact firstUnfolding_reduction_independent (ciQ_mem P.1) (ciQ_notMem_sq hX hPr hP) (ciQOf_prime hPr hP) (ciCard P.1) (ookC hm hi) σ
    (omPhi Ch sel mu c i P 1 1) Ψr (ookSupp Ch sel mu c hs hm hi P hP) hred (c.psi P) (fun u => σ (psi0P Ch P.1 u))
    (fun a ha => by rw [hψ a ha]) hAc hB hAc' hB' xj

theorem ookXiSupp (c : LocCst X (rowSG Pr sel mu)) (hs : c.sharp = true) {m2 i : ℕ} (hm : R.m = m2 + 2) (hi : i < m2)
    (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) (x : HomE X.E (R.N i) (R.N (i + 1))) (h : XiAt Ch sel mu c i P 1 1 x ≠ 0)
    (s : Fin (R.N i)) (l : Fin (R.N (i + 1))) : IntAt P.1 ((qOf P.1 : X.E) ^ c.A * x (Pi.single s 1) l) := by
  unfold XiAt at h
  have h1 := right_ne_zero_of_mul h
  have hx := xInt_of_firstUnfolding_ne_zero (ookC hm hi) (omPhi Ch sel mu c i P 1 1) (ookSupp Ch sel mu c hs hm hi P hP) _ _ _ x h1
  have h2 := hx l.1 s.1 l.2 s.2
  rw [ocbS_eN_single s.2, ocbS_atN_of_lt _ l.2] at h2
  refine IntAt.mul ?_ h2
  rw [← Nat.cast_pow]
  exact ocbS_intAt_natCast _

theorem ookXiInv (hX : X.Ok) (hPr : Pr.Ok) (c : LocCst X (rowSG Pr sel mu)) (hs : c.sharp = true) {m2 i : ℕ} (hm : R.m = m2 + 2)
    (hi : i < m2) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    (hψ : ∀ a, IntAt P.1 a → c.psi P (a / (qOf P.1 : X.E)) = psi0P Ch P.1 (redP P.1 a)) (σ : X.K →+* ℂ)
    (hA : R.m ≤ c.A) (hB : c.B = 1) (x z : HomE X.E (R.N i) (R.N (i + 1)))
    (hz : ∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ c.B)⁻¹ * z (Pi.single s 1) l)) :
    XiAt Ch sel mu c i P 1 1 (x + z) = XiAt Ch sel mu c i P 1 1 x := by
  obtain ⟨Ψr, hred⟩ := ookRedPsi Ch sel mu hX hPr c hs hm hi P hP σ
  have hAc : cOf R (i + 1) + 1 ≤ c.A := by unfold cOf; omega
  have hz' : ∀ l s, l < R.N (i + 1) → s < R.N i → IntAt P.1 (Loc.atN (z (Loc.eN X.E (R.N i) s)) l / (qOf P.1 : X.E)) := by
    intro l s hl hs
    have h1 := hz ⟨s, hs⟩ ⟨l, hl⟩
    rw [hB, pow_one, inv_mul_eq_div] at h1
    rw [ocbS_eN_single hs, ocbS_atN_of_lt _ hl]
    exact h1
  unfold XiAt
  congr 1
  exact firstUnfolding_add_eq_self_of_intAt_div (ciQ_mem P.1) (ciQ_notMem_sq hX hPr hP) (ciQOf_prime hPr hP) (ciCard P.1) (ookC hm hi) σ
    (omPhi Ch sel mu c i P 1 1) Ψr (ookSupp Ch sel mu c hs hm hi P hP) hred (c.psi P) (fun u => σ (psi0P Ch P.1 u))
    (fun a ha => by rw [hψ a ha]) hAc (by rw [hB]) x z hz'

theorem ookLast {m2 : ℕ} (hm : R.m = m2 + 2) :
    cOf R m2 = 1 ∧ cOf R (m2 + 1) = 0 ∧ R.k ≤ R.N m2 ∧ R.k ≤ R.r ∧ R.r + (m2 + 1 - 1) * R.t = R.N m2 + cOf R m2 ∧
      R.r + (m2 + 1 - 1) * R.t ≤ R.N (m2 + 1) + cOf R (m2 + 1) := by
  have h1 : cOf R m2 = 1 := by unfold cOf; omega
  have h2 : cOf R (m2 + 1) = 0 := by unfold cOf; omega
  have h3 := Y_eq_X_add (R := R) (j := m2) (by omega)
  have h4 : R.N (m2 + 1) = R.N m2 + R.t + 1 := by unfold Ranks.N; ring
  have h5 : R.k ≤ R.N m2 := by unfold Ranks.N; omega
  have h6 : R.k ≤ R.r := by unfold Ranks.r; omega
  have h7 : R.m - 1 - m2 = 1 := by omega
  rw [h7] at h3
  refine ⟨h1, h2, h5, h6, ?_, ?_⟩
  · rw [Nat.add_sub_cancel, h1]; exact h3
  · rw [Nat.add_sub_cancel, h3, h4, h2]; omega

theorem ookPsiSuppX (c : LocCst X (rowSG Pr sel mu)) (hs : c.sharp = true) {m2 : ℕ} (hm : R.m = m2 + 2) (P : rowSG Pr sel mu)
    (hP : P.1 ∈ Pr.vGs) (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1)))
    (h : PsiAt Ch sel mu c m2 P 1 x₀ y' ≠ 0) (s : Fin (R.N m2)) (l : Fin (R.N (m2 + 1))) :
    IntAt P.1 ((qOf P.1 : X.E) ^ c.A * x₀ (Pi.single s 1) l) := by
  classical
  obtain ⟨hc', hc, hk, -, ha, -⟩ := ookLast (R := R) hm
  unfold PsiAt at h
  rw [ookOmPhi_eq Ch sel mu c hs m2 P hP] at h
  have h' := right_ne_zero_of_mul h
  rw [phiGS_eq] at h'
  have hC := (ite_ne_right_iff.1 h').1
  have hp' : LocE.fPos R.k (cOf R m2) (R.N m2) s.1 < R.r + (m2 + 1 - 1) * R.t := by
    rw [ha]; exact ocbPhi_fPos_lt hk (Nat.lt_of_lt_of_le s.2 (Nat.le_add_right _ _))
  have h1 := hC.1 l.1 _ (Nat.lt_of_lt_of_le l.2 (Nat.le_add_right _ _)) hp'
  rw [ookEntB_joinX (qOf P.1) hc' hc hk x₀ y' l.2 s.2] at h1
  refine IntAt.mul ?_ h1
  rw [← Nat.cast_pow]
  exact ocbS_intAt_natCast _

theorem ookPsiInv (hX : X.Ok) (hPr : Pr.Ok) (c : LocCst X (rowSG Pr sel mu)) (hs : c.sharp = true) {m2 : ℕ} (hm : R.m = m2 + 2)
    (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' z : Sp X.E (R.N (m2 + 1)))
    (hz : ∀ i, IntAt P.1 (z i)) : PsiAt Ch sel mu c m2 P 1 x₀ (y' + z) = PsiAt Ch sel mu c m2 P 1 x₀ y' := by
  obtain ⟨hc', hc, hk, hkr, ha, han⟩ := ookLast (R := R) hm
  unfold PsiAt
  rw [ookOmPhi_eq Ch sel mu c hs m2 P hP, ookOmPhi_eq Ch sel mu c hs m2 P hP]
  congr 1
  refine ookPhiGS_congr (ciQ_mem P.1) (ciQ_ne_zero (ciQ_notMem_sq hX hPr hP)) _ _ _ _ hkr han fun p p' hp hp' => ?_
  have hp0 : p < R.N (m2 + 1) := by omega
  by_cases hpk : p' = R.k
  · rw [hpk, symEntB_join_col _ hc' hc x₀ (y' + z) hp0, symEntB_join_col _ hc' hc x₀ y' hp0]
    exact ⟨z ⟨p, hp0⟩, hz _, by rw [Pi.add_apply, mul_add]⟩
  · obtain ⟨hsl, hfp⟩ := ookFIdx_lt hc' hk (by omega) hpk
    rw [← hfp, ookEntB_joinX _ hc' hc hk x₀ (y' + z) hp0 hsl, ookEntB_joinX _ hc' hc hk x₀ y' hp0 hsl]
    exact ⟨0, ciIntAt_zero, by rw [mul_zero, add_zero]⟩

theorem ookPsiInvX (hX : X.Ok) (hPr : Pr.Ok) (c : LocCst X (rowSG Pr sel mu)) (hs : c.sharp = true) {m2 : ℕ} (hm : R.m = m2 + 2)
    (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) (hB : c.B = 1) (x₀ z : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1)))
    (hz : ∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ c.B)⁻¹ * z (Pi.single s 1) l)) :
    PsiAt Ch sel mu c m2 P 1 (x₀ + z) y' = PsiAt Ch sel mu c m2 P 1 x₀ y' := by
  obtain ⟨hc', hc, hk, hkr, ha, han⟩ := ookLast (R := R) hm
  have hq0 : (qOf P.1 : X.E) ≠ 0 := ciQ_ne_zero (ciQ_notMem_sq hX hPr hP)
  unfold PsiAt
  rw [ookOmPhi_eq Ch sel mu c hs m2 P hP, ookOmPhi_eq Ch sel mu c hs m2 P hP]
  congr 1
  refine ookPhiGS_congr (ciQ_mem P.1) hq0 _ _ _ _ hkr han fun p p' hp hp' => ?_
  have hp0 : p < R.N (m2 + 1) := by omega
  by_cases hpk : p' = R.k
  · rw [hpk, symEntB_join_col _ hc' hc (x₀ + z) y' hp0, symEntB_join_col _ hc' hc x₀ y' hp0]
    exact ⟨0, ciIntAt_zero, by rw [mul_zero, add_zero]⟩
  · obtain ⟨hsl, hfp⟩ := ookFIdx_lt hc' hk (by omega) hpk
    rw [← hfp, ookEntB_joinX _ hc' hc hk (x₀ + z) y' hp0 hsl, ookEntB_joinX _ hc' hc hk x₀ y' hp0 hsl]
    have h1 := hz ⟨_, hsl⟩ ⟨p, hp0⟩
    rw [hB, pow_one] at h1
    refine ⟨_, h1, ?_⟩
    rw [LinearMap.add_apply, Pi.add_apply, ← mul_assoc, mul_inv_cancel₀ hq0, one_mul]

end Glob

section Cst

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)

def ookCst (SB : Finset (HeightOneSpectrum (𝓞 X.E))) (mq : ℕ → SB → X.K) (A : ℕ) : LocCst X SB :=
  { ciCst Ch SB mq with A := A, sharp := true }

variable {Ch}


theorem ookXiUnit (hCh : Ch.Ok) {σ₀ : X.K →+* ℂ} {xi0 : X.E} (hW : Ch.WeilTied σ₀ xi0) (w : HeightOneSpectrum (𝓞 X.E))
    (hw : w ∈ Pr.vGs) : IntAt w xi0 ∧ redP w xi0 ≠ 0 := by
  have hne : redP w xi0 ≠ 0 := by
    intro h0
    apply hCh.psi_zero_nontrivial_character ⟨w, hw⟩
    ext c
    apply σ₀.injective
    rw [hW ⟨w, hw⟩ c 0 (by rw [h0, zero_mul, Int.cast_zero]), AddChar.one_apply, map_one]
    simp
  exact ⟨intAt_of_redP_ne_zero₂ hne, hne⟩

end Cst

section Ok

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)

def ookCstR (G : ChGlob X R.m) : LocCst X (rowSG Pr sel (mu0 X.F X.E X.K S)) :=
  ookCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S)) (ciMuq G ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)) R.m

variable {Ch}




end Ok

end Formalism.L2.Col
end
end
