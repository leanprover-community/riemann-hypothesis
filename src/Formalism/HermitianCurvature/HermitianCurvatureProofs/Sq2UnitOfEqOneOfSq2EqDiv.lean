import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CompRB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.PolynomialBound
import Mathlib.Geometry.Manifold.PartitionOfUnity

section
open Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma dif {E₁ F₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    {f : E₁ → F₁} (hf : ContDiff ℝ ∞ f) : Differentiable ℝ f := by
  exact hf.differentiable (by simp)

lemma hdx (x : Bool × Mat k r) {f : Mat k r → E} (hf : Differentiable ℝ f) (g : Mat k r) :
    HasDerivAt (fun t : ℝ => f (crv x g t)) (fderiv ℝ f g (dirv x g)) 0 := by
  have hd : HasFDerivAt f (fderiv ℝ f g) (crv x g 0) := by
    rw [crv_zero]
    exact (hf g).hasFDerivAt
  exact hd.comp_hasDerivAt 0 (crv_hasDerivAt x g)

private theorem dx_eq_deriv_crv (x : Bool × Mat k r) (f : Mat k r → E) (g : Mat k r) :
    Dx x f g = deriv (fun t : ℝ => f (crv x g t)) 0 := by
  rcases x with ⟨b, X⟩
  cases b <;> rfl

private theorem dirL_eq_dirv (x : Bool × Mat k r) (g : Mat k r) : dirL x g = dirv x g := by
  rcases x with ⟨b, X⟩
  cases b <;> first | rfl | simp [dirL, dirv]

lemma dx_fd (x : Bool × Mat k r) {f : Mat k r → E} (hf : Differentiable ℝ f) :
    Dx x f = fun g => fderiv ℝ f g (dirL x g) := by
  funext g
  rw [dx_eq_deriv_crv, (hdx x hf g).deriv, dirL_eq_dirv]

lemma cdx (x : Bool × Mat k r) {f : Mat k r → E} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (Dx x f) := by
  rw [dx_fd x (dif hf)]
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply (dirL x).contDiff

lemma cdw (w : List (Bool × Mat k r)) {f : Mat k r → E} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (Dw w f) := by
  induction w with
  | nil => simpa [Dw] using hf
  | cons a w ih => simpa [Dw] using cdx a ih

lemma dx_add (x : Bool × Mat k r) {a b : Mat k r → E} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    Dx x (fun g => a g + b g) = fun g => Dx x a g + Dx x b g := by
  rw [dx_fd x (f := fun g => a g + b g) (ha.add hb), dx_fd x ha, dx_fd x hb]
  funext g
  exact congrArg (fun T => T (dirL x g)) (fderiv_add (ha g) (hb g))

lemma dw_add (w : List (Bool × Mat k r)) {a b : Mat k r → E} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    Dw w (fun g => a g + b g) = fun g => Dw w a g + Dw w b g := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show Dx x (Dw w fun g => a g + b g) = fun g => Dx x (Dw w a) g + Dx x (Dw w b) g
    rw [ih]
    exact dx_add x (dif (cdw w ha)) (dif (cdw w hb))

lemma dx_clm {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] (L : E →L[ℝ] E₂) (x : Bool × Mat k r)
    {f : Mat k r → E} (hf : Differentiable ℝ f) : Dx x (fun g => L (f g)) = fun g => L (Dx x f g) := by
  rw [dx_fd x (f := fun g => L (f g)) (L.differentiable.comp hf), dx_fd x hf]
  funext g
  have h := (L.hasFDerivAt.comp g (hf g).hasFDerivAt).fderiv
  rw [show (fun g => L (f g)) = ⇑L ∘ f from rfl]
  exact congrArg (fun T => T (dirL x g)) h

lemma dw_clm {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] (L : E →L[ℝ] E₂) (w : List (Bool × Mat k r))
    {f : Mat k r → E} (hf : ContDiff ℝ ∞ f) : Dw w (fun g => L (f g)) = fun g => L (Dw w f g) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show Dx x (Dw w fun g => L (f g)) = fun g => L (Dx x (Dw w f) g)
    rw [ih]
    exact dx_clm L x (dif (cdw w hf))

section app

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma dx_app (x : Bool × Mat k r) {a : Mat k r → (F →L[ℝ] E)} {b : Mat k r → F} (ha : Differentiable ℝ a)
    (hb : Differentiable ℝ b) :
    Dx x (fun g => a g (b g)) = fun g => Dx x a g (b g) + a g (Dx x b g) := by
  rw [dx_fd x (ha.clm_apply hb), dx_fd x ha, dx_fd x hb]
  funext g
  have h2 := congrArg (fun T => T (dirL x g)) (fderiv_clm_apply (ha g) (hb g))
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply] at h2
  exact h2.trans (add_comm _ _)

lemma cd_app {a : Mat k r → (F →L[ℝ] E)} {b : Mat k r → F} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (fun g => a g (b g)) := ha.clm_apply hb

private lemma dw_append_singleton' {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] (w : List (Bool × Mat k r))
    (x : Bool × Mat k r) (f : Mat k r → E') : Dw (w ++ [x]) f = Dw w (Dx x f) := by
  unfold Dw
  rw [List.foldr_append]
  rfl

lemma leibA (g : Mat k r) (M : ℝ) (w : List (Bool × Mat k r)) :
    ∀ (a : Mat k r → (F →L[ℝ] E)) (b : Mat k r → F), ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      (∀ w₁ w₂, Spl w w₁ w₂ → ‖Dw w₁ a g‖ * ‖Dw w₂ b g‖ ≤ M) →
      ‖Dw w (fun g => a g (b g)) g‖ ≤ 2 ^ w.length * M := by
  induction w using List.reverseRecOn with
  | nil =>
    intro a b ha hb h
    have h0 := h [] [] ⟨List.Sublist.slnil, List.Sublist.slnil, List.Perm.nil⟩
    simp only [Dw, List.foldr_nil, List.length_nil, pow_zero, one_mul] at h0 ⊢
    exact (ContinuousLinearMap.le_opNorm _ _).trans h0
  | append_singleton w x ih =>
    intro a b ha hb h
    have splL : ∀ {w₁ w₂ : List (Bool × Mat k r)}, Spl w w₁ w₂ → Spl (w ++ [x]) (w₁ ++ [x]) w₂ := by
      intro w₁ w₂ hs
      refine ⟨hs.1.append (List.Sublist.refl [x]), hs.2.1.trans (List.sublist_append_left w [x]), ?_⟩
      have hp : (w₁ ++ [x] ++ w₂).Perm (w₁ ++ w₂ ++ [x]) := by
        simpa [List.append_assoc] using (List.perm_append_comm (l₁ := [x]) (l₂ := w₂)).append_left w₁
      exact hp.trans (hs.2.2.append_right [x])
    have splR : ∀ {w₁ w₂ : List (Bool × Mat k r)}, Spl w w₁ w₂ → Spl (w ++ [x]) w₁ (w₂ ++ [x]) := by
      intro w₁ w₂ hs
      refine ⟨hs.1.trans (List.sublist_append_left w [x]), hs.2.1.append (List.Sublist.refl [x]), ?_⟩
      rw [← List.append_assoc]
      exact hs.2.2.append_right [x]
    have h1 : ‖Dw w (fun g => Dx x a g (b g)) g‖ ≤ 2 ^ w.length * M :=
      ih (Dx x a) b (cdx x ha) hb fun w₁ w₂ hs => by
        have h' := h (w₁ ++ [x]) w₂ (splL hs)
        rwa [dw_append_singleton'] at h'
    have h2 : ‖Dw w (fun g => a g (Dx x b g)) g‖ ≤ 2 ^ w.length * M :=
      ih a (Dx x b) ha (cdx x hb) fun w₁ w₂ hs => by
        have h' := h w₁ (w₂ ++ [x]) (splR hs)
        rwa [dw_append_singleton'] at h'
    rw [dw_append_singleton', dx_app x (dif ha) (dif hb), dw_add w (cd_app (cdx x ha) hb) (cd_app ha (cdx x hb))]
    beta_reduce
    refine (norm_add_le _ _).trans ?_
    rw [List.length_append, List.length_singleton, pow_succ]
    linarith

lemma dx_comp (x : Bool × Mat k r) {ψ : Mat k r → F} {Φ : F → E} (hψ : Differentiable ℝ ψ)
    (hΦ : Differentiable ℝ Φ) : Dx x (fun g => Φ (ψ g)) = fun g => fderiv ℝ Φ (ψ g) (Dx x ψ g) := by
  rw [dx_fd x (f := fun g => Φ (ψ g)) (hΦ.comp hψ), dx_fd x hψ]
  funext g
  rw [show (fun g => Φ (ψ g)) = Φ ∘ ψ from rfl]
  exact congrArg (fun T => T (dirL x g)) (fderiv_comp g (hΦ (ψ g)) (hψ g))

lemma spl_len {w w₁ w₂ : List (Bool × Mat k r)} (h : Spl w w₁ w₂) : w₁.length + w₂.length = w.length := by
  obtain ⟨-, -, hp⟩ := h
  rw [← List.length_append]
  exact hp.length_eq

private theorem adm_of_sublist {n : ℕ} {w w' : List (Bool × Mat k r)} (h : admitted n w)
    (hw : w'.Sublist w) : admitted n w' := by
  obtain ⟨u, v, hu, hv, hlen, rfl⟩ := h
  obtain ⟨l₁, l₂, rfl, h1, h2⟩ := List.sublist_append_iff.1 hw
  unfold wL at h1
  unfold wR at h2
  obtain ⟨u', hu', rfl⟩ := List.sublist_map_iff.1 h1
  obtain ⟨v', hv', rfl⟩ := List.sublist_map_iff.1 h2
  exact ⟨u', v', fun X hX => hu X (hu'.subset hX), fun X hX => hv X (hv'.subset hX),
    by have := hu'.length_le; have := hv'.length_le; omega, rfl⟩

theorem fdb (ψ : Mat k r → F) (hψ : ContDiff ℝ ∞ ψ) (S : Set (Mat k r)) (K : Set F) (hK : ∀ g ∈ S, ψ g ∈ K)
    (Y : Mat k r → ℝ) (hY : ∀ g ∈ S, 1 ≤ Y g) (α β : ℕ) (M : ℝ) (n : ℕ)
    (H : ∀ w, admitted n w → w ≠ [] → ∀ g ∈ S, ‖Dw w ψ g‖ ≤ M * Y g ^ (α * w.length + β)) :
    ∀ m : ℕ, ∀ (E₁ : Type) [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] (Φ : F → E₁), ContDiff ℝ ∞ Φ →
      (∀ j : ℕ, ∃ B : ℝ, ∀ y ∈ K, ‖iteratedFDeriv ℝ j Φ y‖ ≤ B) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ w, admitted n w → w.length ≤ m → ∀ g ∈ S,
        ‖Dw w (fun g => Φ (ψ g)) g‖ ≤ C * Y g ^ ((α + β) * w.length) := by
  intro m
  induction m with
  | zero =>
    intro E₁ _ _ Φ hΦ hB
    obtain ⟨B0, hB0⟩ := hB 0
    refine ⟨max B0 0, le_max_right _ _, fun w _ hw g hg => ?_⟩
    have hw0 : w = [] := List.length_eq_zero_iff.1 (by omega)
    subst hw0
    simp only [Dw, List.foldr_nil, List.length_nil, mul_zero, pow_zero, mul_one]
    have h0 := hB0 (ψ g) (hK g hg)
    rw [norm_iteratedFDeriv_zero] at h0
    exact h0.trans (le_max_left _ _)
  | succ m ih =>
    intro E₁ _ _ Φ hΦ hB
    obtain ⟨C', hC'0, hC'⟩ := ih (F →L[ℝ] E₁) (fderiv ℝ Φ) (hΦ.fderiv_right (m := ∞) (by simp))
      (fun j => by
        obtain ⟨B, hB'⟩ := hB (j + 1)
        exact ⟨B, fun y hy => by rw [norm_iteratedFDeriv_fderiv]; exact hB' y hy⟩)
    obtain ⟨B0, hB0⟩ := hB 0
    have hM' : 0 ≤ max M 0 := le_max_right _ _
    refine ⟨max B0 0 + 2 ^ m * (C' * max M 0),
      add_nonneg (le_max_right _ _) (mul_nonneg (pow_nonneg (by norm_num) _) (mul_nonneg hC'0 hM')),
      fun w hwA hw g hg => ?_⟩
    have hY1 := hY g hg
    have hY0 : 0 ≤ Y g := by linarith
    have hrest : 0 ≤ 2 ^ m * (C' * max M 0) :=
      mul_nonneg (pow_nonneg (by norm_num) _) (mul_nonneg hC'0 hM')
    rcases List.eq_nil_or_concat w with rfl | ⟨w', x, rfl⟩
    · simp only [Dw, List.foldr_nil, List.length_nil, mul_zero, pow_zero, mul_one]
      have h0 := hB0 (ψ g) (hK g hg)
      rw [norm_iteratedFDeriv_zero] at h0
      linarith [le_max_left B0 0]
    · rw [List.concat_eq_append] at hwA hw ⊢
      rw [dw_append_singleton', dx_comp x (dif hψ) (dif hΦ)]
      have hlen : w'.length ≤ m := by
        rw [List.length_append, List.length_singleton] at hw
        omega
      have key := leibA g (C' * max M 0 * Y g ^ ((α + β) * (w'.length + 1))) w'
        (fun g => fderiv ℝ Φ (ψ g)) (Dx x ψ) ((hΦ.fderiv_right (m := ∞) (by simp)).comp hψ) (cdx x hψ)
        (fun w₁ w₂ hs => by
          have hl := spl_len hs
          have h1 : ‖Dw w₁ (fun g => fderiv ℝ Φ (ψ g)) g‖ ≤ C' * Y g ^ ((α + β) * w₁.length) :=
            hC' w₁ (adm_of_sublist hwA (hs.1.trans (List.sublist_append_left _ _))) (by omega) g hg
          have h2 : ‖Dw w₂ (Dx x ψ) g‖ ≤ max M 0 * Y g ^ (α * (w₂ ++ [x]).length + β) := by
            rw [← dw_append_singleton']
            exact (H (w₂ ++ [x]) (adm_of_sublist hwA (hs.2.1.append_right [x])) (by simp) g hg).trans
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hY0 _))
          have hexp : (α + β) * w₁.length + (α * (w₂ ++ [x]).length + β) ≤
              (α + β) * (w'.length + 1) := by
            rw [List.length_append, List.length_singleton]
            nlinarith
          calc ‖Dw w₁ (fun g => fderiv ℝ Φ (ψ g)) g‖ * ‖Dw w₂ (Dx x ψ) g‖
              ≤ (C' * Y g ^ ((α + β) * w₁.length)) * (max M 0 * Y g ^ (α * (w₂ ++ [x]).length + β)) :=
                mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hC'0 (pow_nonneg hY0 _))
            _ = C' * max M 0 * Y g ^ ((α + β) * w₁.length + (α * (w₂ ++ [x]).length + β)) := by
                rw [pow_add]
                ring
            _ ≤ C' * max M 0 * Y g ^ ((α + β) * (w'.length + 1)) :=
                mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hY1 hexp) (mul_nonneg hC'0 hM'))
      have hP : 0 ≤ C' * max M 0 * Y g ^ ((α + β) * (w'.length + 1)) :=
        mul_nonneg (mul_nonneg hC'0 hM') (pow_nonneg hY0 _)
      calc _ ≤ 2 ^ w'.length * (C' * max M 0 * Y g ^ ((α + β) * (w'.length + 1))) := key
        _ ≤ 2 ^ m * (C' * max M 0 * Y g ^ ((α + β) * (w'.length + 1))) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hlen) hP
        _ ≤ (max B0 0 + 2 ^ m * (C' * max M 0)) * Y g ^ ((α + β) * (w' ++ [x]).length) := by
            rw [List.length_append, List.length_singleton]
            have : 0 ≤ max B0 0 * Y g ^ ((α + β) * (w'.length + 1)) :=
              mul_nonneg (le_max_right _ _) (pow_nonneg hY0 _)
            nlinarith

end app

end Formalism.FourierDecayAlt.P.AdmissibleLieWords
end
end

section
open Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def sc (ε x : ℝ) : ℝ := Real.smoothTransition ((x - ε / 4) / (ε / 4))

lemma sc_zero {ε x : ℝ} (hε : 0 < ε) (hx : x ≤ ε / 4) : sc ε x = 0 := by
  unfold sc
  exact Real.smoothTransition.zero_of_nonpos (div_nonpos_iff.2 (Or.inr ⟨by linarith, by linarith⟩))

lemma sc_one {ε x : ℝ} (hε : 0 < ε) (hx : ε / 2 ≤ x) : sc ε x = 1 := by
  unfold sc
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by linarith)]
  linarith

lemma sc_cd (ε : ℝ) : ContDiff ℝ ∞ (sc ε) := by
  show ContDiff ℝ ∞ (fun x => Real.smoothTransition ((x - ε / 4) / (ε / 4)))
  exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

def hh (ε x : ℝ) : ℝ := sc ε x * x ^ (-(1 / 2 : ℝ))

lemma hh_cd {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (hh ε) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : ε / 8 < x
  · have hx0 : 0 < x := by linarith
    show ContDiffAt ℝ ∞ (fun y => sc ε y * y ^ (-(1 / 2 : ℝ))) x
    exact ((sc_cd ε).contDiffAt).mul (Real.contDiffAt_rpow_const_of_ne hx0.ne')
  · have h0 : hh ε =ᶠ[nhds x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show x < ε / 4 by linarith)] with y hy
      simp [hh, sc_zero hε (le_of_lt hy)]
    exact contDiffAt_const.congr_of_eventuallyEq h0

lemma hh_ev {ε x : ℝ} (hε : 0 < ε) (hx : ε / 2 < x) :
    hh ε =ᶠ[nhds x] fun y => y ^ (-(1 / 2 : ℝ)) := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  simp only [hh, sc_one hε (le_of_lt hy), one_mul]

lemma hh_bound {ε : ℝ} (hε : 0 < ε) (j : ℕ) {x : ℝ} (hx : ε ≤ x) :
    ‖iteratedFDeriv ℝ j (hh ε) x‖ ≤ |(descPochhammer ℝ j).eval (-(1 / 2 : ℝ))| * ε ^ (-(1 / 2 : ℝ) - j) := by
  have hx0 : 0 < x := lt_of_lt_of_le hε hx
  have h2 : ε / 2 < x := by linarith
  have heq : iteratedFDeriv ℝ j (hh ε) x = iteratedFDeriv ℝ j (fun y : ℝ => y ^ (-(1 / 2 : ℝ))) x := by
    first
    | exact ((hh_ev hε h2).iteratedFDeriv ℝ j).eq_of_nhds
    | exact (hh_ev hε h2).iteratedFDeriv_eq j
  rw [heq, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate]
  simp only [Real.iter_deriv_rpow_const]
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hexp : -(1 / 2 : ℝ) - j ≤ 0 := by linarith
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  first
  | exact Real.rpow_le_rpow_of_exponent_nonpos hε hx hexp
  | exact Real.rpow_le_rpow_of_nonpos hε hx hexp

def Phh (ε : ℝ) (z : ℂ) : ℂ := ((hh ε z.re : ℝ) : ℂ)

lemma Phh_cd {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (Phh ε) := by
  show ContDiff ℝ ∞ (fun z : ℂ => ((hh ε z.re : ℝ) : ℂ))
  exact Complex.ofRealCLM.contDiff.comp ((hh_cd hε).comp Complex.reCLM.contDiff)

lemma Phh_bound {ε : ℝ} (hε : 0 < ε) (j : ℕ) :
    ∃ B : ℝ, ∀ z ∈ {z : ℂ | ε ≤ z.re}, ‖iteratedFDeriv ℝ j (Phh ε) z‖ ≤ B := by
  refine ⟨‖Complex.ofRealCLM‖ * (|(descPochhammer ℝ j).eval (-(1 / 2 : ℝ))| * ε ^ (-(1 / 2 : ℝ) - j) *
    ‖Complex.reCLM‖ ^ j), fun z hz => ?_⟩
  have hh' : ContDiff ℝ ∞ (hh ε ∘ Complex.reCLM) := (hh_cd hε).comp Complex.reCLM.contDiff
  have e : Phh ε = Complex.ofRealCLM ∘ (hh ε ∘ Complex.reCLM) := rfl
  rw [e]
  calc ‖iteratedFDeriv ℝ j (Complex.ofRealCLM ∘ (hh ε ∘ Complex.reCLM)) z‖
      ≤ ‖Complex.ofRealCLM‖ * ‖iteratedFDeriv ℝ j (hh ε ∘ Complex.reCLM) z‖ :=
        by
          first
          | exact Complex.ofRealCLM.norm_iteratedFDeriv_comp_left hh'.contDiffAt (by exact_mod_cast le_top)
          | exact Complex.ofRealCLM.norm_iteratedFDeriv_comp_left hh' z (by exact_mod_cast le_top)
          | exact Complex.ofRealCLM.norm_iteratedFDeriv_comp_left hh'.contDiffAt z (by exact_mod_cast le_top)
    _ ≤ _ := by
        gcongr
        calc ‖iteratedFDeriv ℝ j (hh ε ∘ Complex.reCLM) z‖
            = ‖(iteratedFDeriv ℝ j (hh ε) (Complex.reCLM z)).compContinuousLinearMap
                fun _ => Complex.reCLM‖ := by
              first
              | rw [Complex.reCLM.iteratedFDeriv_comp_right (hh_cd hε) z (by exact_mod_cast le_top)]
              | rw [Complex.reCLM.iteratedFDeriv_comp_right (hh_cd hε).contDiffAt (by exact_mod_cast le_top)]
              | rw [Complex.reCLM.iteratedFDeriv_comp_right (hh_cd hε) (by exact_mod_cast le_top)]
          _ ≤ ‖iteratedFDeriv ℝ j (hh ε) (Complex.reCLM z)‖ * ∏ _i : Fin j, ‖Complex.reCLM‖ :=
              ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
          _ = ‖iteratedFDeriv ℝ j (hh ε) (Complex.reCLM z)‖ * ‖Complex.reCLM‖ ^ j := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          _ ≤ _ := by
              gcongr
              exact hh_bound hε j hz

lemma sqrt_div_eq {T x : ℝ} (hT : 0 < T) (hx : 0 < x) : Real.sqrt (T / x) = Real.sqrt T * x ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_div hT.le x, Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]

end Formalism.FourierDecayAlt.P.AdmissibleLieWords

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma admissible_of_unit_words {k r i : ℕ} {u v : List (Mat k r)} (h : C6.UnitWords k r u v i) : admitted i (wL u ++ wR v) := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨u, v, h1, h2, h3.le, rfl⟩

lemma poly_adm {k r d n : ℕ} {P : Mat k r → ℂ} (hP : U.IsPolyDeg d P) :
    ContDiff ℝ ∞ P ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ w, admitted n w → ∀ g ∈ GV k r, ‖Dw w P g‖ ≤ C * gN g ^ d := by
  obtain ⟨hc, hb⟩ := PI.UnitaryCorollaryDerivatives.polynomial_bound k r d P hP
  refine ⟨hc, ?_⟩
  obtain ⟨C, hC⟩ := hb n
  refine ⟨max C 0, le_max_right _ _, fun w hw g hg => ?_⟩
  obtain ⟨u, v, hu, hv, hl, rfl⟩ := hw
  have := hC u v hu hv hl g hg
  simp only [List.map_const', List.sum_replicate, smul_zero, Nat.cast_zero, add_zero, Real.rpow_natCast] at this
  rw [← dLR_eq]
  exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by have := gN_pos hg; positivity))

theorem fibre_unit_normalization : C6.FibUnit := by
  intro k r m om Gp T hom hGp hT _ ε hε i
  set ψ : Mat k r → ℂ := fun g => ((Gp g : ℝ) : ℂ) with hψdef
  obtain ⟨hψc, CG, hCG0, hCG⟩ := poly_adm (n := i) hGp
  have hGpc : Continuous Gp := by
    have : Gp = fun g => (ψ g).re := by funext g; simp [hψdef]
    rw [this]; exact Complex.continuous_re.comp hψc.continuous

  obtain ⟨C₁, hC₁0, hC₁⟩ := fdb ψ hψc {g | g ∈ GV k r ∧ ε ≤ Gp g} {z : ℂ | ε ≤ z.re}
    (fun g hg => by simpa [hψdef] using hg.2) gN (fun g hg => gN_ge_one hg.1) (2 * r + 2) 0 CG i
    (by
      intro w hw hne g hg
      have h1 := hCG w hw g hg.1
      have hl : 1 ≤ w.length := List.length_pos_iff.mpr hne
      refine h1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (gN_ge_one hg.1) ?_) hCG0)
      nlinarith)
    i ℂ (Phh ε) (Phh_cd hε) (Phh_bound hε)

  have hoa : ∀ a, ContDiff ℝ ∞ (fun g => om g a) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ w, admitted i w → ∀ g ∈ GV k r,
      ‖Dw w (fun g => om g a) g‖ ≤ C * gN g ^ (r + 1) := fun a => poly_adm (hom a)
  choose hoc Co hCo0 hCo using hoa
  set C₂ : ℝ := ∑ a, Co a with hC₂
  have hC₂0 : 0 ≤ C₂ := Finset.sum_nonneg fun a _ => hCo0 a
  have hCoa : ∀ a, Co a ≤ C₂ := fun a => Finset.single_le_sum (fun b _ => hCo0 b) (Finset.mem_univ a)
  refine ⟨Real.sqrt T * (2 ^ i * (C₁ * C₂)), fun u v huv g hg hεg => ?_⟩
  set w := wL u ++ wR v with hw
  have hwA : admitted i w := admissible_of_unit_words huv
  have hwl : w.length = i := by rw [hw, len_LR]; exact huv.2.2
  have hlie : ∀ x ∈ w, inLie k r x.2 := lie_LR (unit_lie huv.1) (unit_lie huv.2.1)

  set Ut : Mat k r → (Fin m → ℂ) := fun g a => (Real.sqrt T : ℂ) * (Phh ε (ψ g) * om g a) with hUt
  have hUtc : ContDiff ℝ ∞ Ut :=
    contDiff_pi.2 fun a => contDiff_const.mul (((Phh_cd hε).comp hψc).mul (hoc a))
  have hO : IsOpen {g : Mat k r | ε / 2 < Gp g} := isOpen_lt continuous_const hGpc
  have heq : ∀ g' ∈ GV k r, g' ∈ {g : Mat k r | ε / 2 < Gp g} →
      (fun g' => C6.unitOf T (Gp g') (om g')) g' = Ut g' := by
    intro g' _ hg'
    have hp : 0 < Gp g' := by simp only [Set.mem_setOf_eq] at hg'; linarith
    funext a
    simp only [C6.unitOf, hUt, Phh, hψdef, Complex.ofReal_re, Pi.smul_apply, smul_eq_mul]
    rw [AdmissibleLieWords.hh, sc_one hε (le_of_lt hg'), one_mul, sqrt_div_eq hT hp]
    push_cast; ring
  rw [dLR_eq, Dw_congr_loc hlie hO heq g hg (by show ε / 2 < Gp g; linarith)]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by positivity) (mul_nonneg hC₁0 hC₂0))) (pow_nonneg (gN_pos hg).le _))).2
  intro a
  have e1 : Dw w Ut g a = Dw w (fun g => Ut g a) g := by
    have := dw_clm (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℂ) a) w hUtc
    exact (congrFun this g).symm
  rw [e1]
  have e2 : (fun g => Ut g a) = fun g => (Real.sqrt T : ℂ) • (Phh ε (ψ g) * om g a) := by
    funext g; simp [hUt, smul_eq_mul]
  rw [e2, Dw_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  have hL := leibB g (C₁ * C₂ * gN g ^ ((r + 1) * (2 * i + 1))) w (fun g => Phh ε (ψ g)) (fun g => om g a)
    ((Phh_cd hε).comp hψc) (hoc a) (by
      intro w₁ w₂ hs
      have hlen := spl_len hs
      obtain ⟨h₁, h₂, _⟩ := hs
      have b1 := hC₁ w₁ (Adm_sub h₁ hwA) (by have := h₁.length_le; omega) g ⟨hg, hεg⟩
      have b2 := (hCo a w₂ (Adm_sub h₂ hwA) g hg).trans
        (mul_le_mul_of_nonneg_right (hCoa a) (pow_nonneg (gN_pos hg).le _))
      have hexp : (2 * r + 2 + 0) * w₁.length + (r + 1) ≤ (r + 1) * (2 * i + 1) := by
        have := h₁.length_le; rw [hwl] at this; nlinarith
      calc ‖Dw w₁ (fun g => Phh ε (ψ g)) g‖ * ‖Dw w₂ (fun g => om g a) g‖
          ≤ (C₁ * gN g ^ ((2 * r + 2 + 0) * w₁.length)) * (C₂ * gN g ^ (r + 1)) :=
            mul_le_mul b1 b2 (norm_nonneg _) (mul_nonneg hC₁0 (pow_nonneg (gN_pos hg).le _))
        _ = C₁ * C₂ * gN g ^ ((2 * r + 2 + 0) * w₁.length + (r + 1)) := by rw [pow_add]; ring
        _ ≤ C₁ * C₂ * gN g ^ ((r + 1) * (2 * i + 1)) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (gN_ge_one hg) hexp) (mul_nonneg hC₁0 hC₂0))
  rw [hwl] at hL
  calc ‖Dw w (fun g => Phh ε (ψ g) * om g a) g‖ ≤ 2 ^ i * (C₁ * C₂ * gN g ^ ((r + 1) * (2 * i + 1))) := hL
    _ = 2 ^ i * (C₁ * C₂) * gN g ^ ((r + 1) * (2 * i + 1)) := by ring

end Formalism.FourierDecayAlt.P
end
end

section
open Matrix Set
open scoped ComplexConjugate ContDiff Manifold Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def utv {k r m : ℕ} (ε T : ℝ) (Gp : Mat k r → ℝ) (om : Mat k r → Fin m → ℂ) (g : Mat k r) : Fin m → ℂ :=
  fun a => (Real.sqrt T : ℂ) * (Phh ε ((Gp g : ℝ) : ℂ) * om g a)

lemma utv_eq {k r m : ℕ} {ε T : ℝ} (hε : 0 < ε) (hT : 0 < T) (Gp : Mat k r → ℝ) (om : Mat k r → Fin m → ℂ)
    {g : Mat k r} (hg : ε / 2 < Gp g) : C6.unitOf T (Gp g) (om g) = utv ε T Gp om g := by
  have hx : 0 < Gp g := by linarith
  funext a
  simp only [C6.unitOf, utv, Phh, hh, Complex.ofReal_re, sc_one hε hg.le, one_mul, Pi.smul_apply,
    smul_eq_mul, sqrt_div_eq hT hx, Complex.ofReal_mul]
  ring

lemma utv_cd {k r m : ℕ} {ε T : ℝ} (hε : 0 < ε) {Gp : Mat k r → ℝ} {om : Mat k r → Fin m → ℂ}
    (hG : ContDiff ℝ ∞ (fun g => ((Gp g : ℝ) : ℂ))) (ho : ∀ a, ContDiff ℝ ∞ (fun g => om g a)) :
    ContDiff ℝ ∞ (utv ε T Gp om) := by
  refine contDiff_pi.2 fun a => ?_
  simp only [utv]
  exact contDiff_const.mul (((Phh_cd hε).comp hG).mul (ho a))

lemma sq2_unitOf_eq_one_of_sq2_eq_div {m : ℕ} {T Gv : ℝ} (hT : 0 < T) (hG : 0 < Gv) {v : Fin m → ℂ} (hv : C6.sq2 v = Gv / T) :
    C6.sq2 (C6.unitOf T Gv v) = 1 := by
  unfold C6.sq2 C6.unitOf at *
  simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_ofReal]
  rw [← Finset.mul_sum, hv, Real.mul_self_sqrt (div_nonneg hT.le hG.le), div_mul_div_comm, mul_comm T Gv,
    div_self (mul_pos hG hT).ne']

lemma continuous_sum_squares (m : ℕ) : Continuous (C6.sq2 (m := m)) := by
  unfold C6.sq2
  exact continuous_finset_sum _ fun a _ => Complex.continuous_normSq.comp (continuous_apply a)

lemma norm_le_one_of_sq2_eq_one {m : ℕ} {v : Fin m → ℂ} (h : C6.sq2 v = 1) : ‖v‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => ?_
  have h1 : Complex.normSq (v a) ≤ 1 := by
    rw [← h]
    unfold C6.sq2
    exact Finset.single_le_sum (f := fun a => Complex.normSq (v a)) (fun i _ => Complex.normSq_nonneg _)
      (Finset.mem_univ a)
  have h2 : ‖v a‖ ^ 2 ≤ 1 := by rw [← Complex.normSq_eq_norm_sq]; exact h1
  nlinarith [norm_nonneg (v a)]

lemma spheres_compact (m m' : ℕ) :
    IsCompact {w : (Fin m → ℂ) × (Fin m' → ℂ) | C6.sq2 w.1 = 1 ∧ C6.sq2 w.2 = 1} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact (isClosed_eq ((continuous_sum_squares m).comp continuous_fst) continuous_const).inter
      (isClosed_eq ((continuous_sum_squares m').comp continuous_snd) continuous_const)
  · refine (Metric.isBounded_closedBall (x := (0 : (Fin m → ℂ) × (Fin m' → ℂ))) (r := 1)).subset ?_
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_prod_le_iff.2 ⟨norm_le_one_of_sq2_eq_one hw.1, norm_le_one_of_sq2_eq_one hw.2⟩

lemma bump_ext {F E : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (K O : Set F) (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (Pi : F → E) (hPi : ContDiffOn ℝ ∞ Pi O) :
    ∃ Φ : F → E, ContDiff ℝ ∞ Φ ∧ (∀ y ∈ K, Φ y = Pi y) ∧
      ∀ j : ℕ, ∃ B : ℝ, ∀ y ∈ K, ‖iteratedFDeriv ℝ j Φ y‖ ≤ B := by
  obtain ⟨V, hVo, hKV, hVO, -⟩ := exists_open_between_and_isCompact_closure hK hO hKO
  obtain ⟨χ, hχ0, hχ1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed (I := 𝓘(ℝ, F)) hVo.isClosed_compl
    hK.isClosed (disjoint_compl_left_iff_subset.2 hKV)
  have hχ : ContDiff ℝ ∞ (χ : F → ℝ) := contMDiff_iff_contDiff.1 χ.contMDiff
  have hΦ : ContDiff ℝ ∞ (fun y => χ y • Pi y) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ O
    · exact hχ.contDiffAt.smul (hPi.contDiffAt (hO.mem_nhds hx))
    · have hx' : x ∈ (closure V)ᶜ := fun h => hx (hVO h)
      have h0 : (fun y => χ y • Pi y) =ᶠ[𝓝 x] fun _ => (0 : E) := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx'] with y hy
        have hyV : y ∈ Vᶜ := fun h => hy (subset_closure h)
        simp [hχ0 hyV]
      exact contDiffAt_const.congr_of_eventuallyEq h0
  refine ⟨fun y => χ y • Pi y, hΦ, fun y hy => by simp [hχ1 hy], fun j => ?_⟩
  exact hK.exists_bound_of_continuousOn
    ((hΦ.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)).continuousOn)

end Formalism.FourierDecayAlt.P.AdmissibleLieWords

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem c6_fib_cost_of_pieces : C6.FibCostOfParts := by
  intro hU k r m m' om om' Gp T T' E _ _ Pi O hom hom' hGp hT hT' hsq hsq' hO hKO hPi ε hε i
  have hGcd : ContDiff ℝ ∞ (fun g => ((Gp g : ℝ) : ℂ)) := (poly_adm (n := 0) hGp).1
  have hGc : Continuous Gp := by
    have h := Complex.continuous_re.comp hGcd.continuous
    simp only [Function.comp_def, Complex.ofReal_re] at h
    exact h
  have ho : ∀ a, ContDiff ℝ ∞ (fun g => om g a) := fun a => (poly_adm (n := 0) (hom a)).1
  have ho' : ∀ a, ContDiff ℝ ∞ (fun g => om' g a) := fun a => (poly_adm (n := 0) (hom' a)).1
  have hu1 : ContDiff ℝ ∞ (utv ε T Gp om) := utv_cd hε hGcd ho
  have hu2 : ContDiff ℝ ∞ (utv ε T' Gp om') := utv_cd hε hGcd ho'
  have hψ : ContDiff ℝ ∞ (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) := hu1.prodMk hu2
  have hOε : IsOpen {g : Mat k r | ε / 2 < Gp g} := isOpen_lt continuous_const hGc

  have hsph : ∀ g ∈ GV k r, ε / 2 < Gp g →
      C6.unitOf T (Gp g) (om g) = utv ε T Gp om g ∧ C6.unitOf T' (Gp g) (om' g) = utv ε T' Gp om' g ∧
      (C6.unitOf T (Gp g) (om g), C6.unitOf T' (Gp g) (om' g)) ∈
        {w : (Fin m → ℂ) × (Fin m' → ℂ) | C6.sq2 w.1 = 1 ∧ C6.sq2 w.2 = 1} := by
    intro g hg hgt
    have hpos : 0 < Gp g := by linarith
    exact ⟨utv_eq hε hT Gp om hgt, utv_eq hε hT' Gp om' hgt, sq2_unitOf_eq_one_of_sq2_eq_div hT hpos (hsq g hg),
      sq2_unitOf_eq_one_of_sq2_eq_div hT' hpos (hsq' g hg)⟩
  obtain ⟨Φ, hΦ, hΦK, hΦb⟩ := bump_ext _ O (spheres_compact m m') hO hKO Pi hPi

  have hwl : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
      ∀ x ∈ wL u ++ wR v, inLie k r x.2 := by
    intro u v hu hv x hx
    rcases List.mem_append.mp hx with hx | hx
    · simp only [wL, List.mem_map] at hx
      obtain ⟨X, hX, rfl⟩ := hx
      exact (hu X hX).1
    · simp only [wR, List.mem_map, List.mem_reverse] at hx
      obtain ⟨X, hX, rfl⟩ := hx
      exact (hv X hX).1
  have hlen : ∀ u v : List (Mat k r), (wL u ++ wR v).length = u.length + v.length := by
    intro u v
    simp [wL, wR]
  choose C1 hC1 using hU k r m om Gp T hom hGp hT hsq ε hε
  choose C2 hC2 using hU k r m' om' Gp T' hom' hGp hT' hsq' ε hε
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∑ j ∈ Finset.range (i + 1), (|C1 j| + |C2 j|) := ⟨_, rfl⟩
  have hCM : ∀ j ≤ i, C1 j ≤ M ∧ C2 j ≤ M := by
    intro j hj
    have hmem : j ∈ Finset.range (i + 1) := Finset.mem_range.mpr (by omega)
    have hle := Finset.single_le_sum (f := fun j => |C1 j| + |C2 j|)
      (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hmem
    rw [← hM] at hle
    exact ⟨by linarith [le_abs_self (C1 j), abs_nonneg (C2 j)], by linarith [le_abs_self (C2 j), abs_nonneg (C1 j)]⟩
  have H : ∀ w, admitted i w → w ≠ [] → ∀ g ∈ {g : Mat k r | g ∈ GV k r ∧ ε ≤ Gp g},
      ‖Dw w (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) g‖ ≤
        M * gN g ^ (2 * (r + 1) * w.length + (r + 1)) := by
    rintro w ⟨u, v, hu, hv, hl, rfl⟩ - g ⟨hg, hge⟩
    have hgt : ε / 2 < Gp g := by linarith
    have hw := hwl u v hu hv
    have huv : C6.UnitWords k r u v (u.length + v.length) := ⟨hu, hv, rfl⟩
    have e1 : Dw (wL u ++ wR v) (utv ε T Gp om) g =
        Dw (wL u ++ wR v) (fun g' => C6.unitOf T (Gp g') (om g')) g :=
      Dw_congr_loc hw hOε (fun g' hg' hg'O => ((hsph g' hg' hg'O).1).symm) g hg hgt
    have e2 : Dw (wL u ++ wR v) (utv ε T' Gp om') g =
        Dw (wL u ++ wR v) (fun g' => C6.unitOf T' (Gp g') (om' g')) g :=
      Dw_congr_loc hw hOε (fun g' hg' hg'O => ((hsph g' hg' hg'O).2.1).symm) g hg hgt
    have f1 : Dw (wL u ++ wR v) (utv ε T Gp om) g =
        (Dw (wL u ++ wR v) (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) g).1 := by
      have h := congrFun (dw_clm (ContinuousLinearMap.fst ℝ (Fin m → ℂ) (Fin m' → ℂ)) (wL u ++ wR v) hψ) g
      simpa using h
    have f2 : Dw (wL u ++ wR v) (utv ε T' Gp om') g =
        (Dw (wL u ++ wR v) (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) g).2 := by
      have h := congrFun (dw_clm (ContinuousLinearMap.snd ℝ (Fin m → ℂ) (Fin m' → ℂ)) (wL u ++ wR v) hψ) g
      simpa using h
    have b1 := hC1 _ u v huv g hg hge
    have b2 := hC2 _ u v huv g hg hge
    rw [dLR_eq, ← e1, f1] at b1
    rw [dLR_eq, ← e2, f2] at b2
    have hexp : (r + 1) * (2 * (u.length + v.length) + 1) =
        2 * (r + 1) * (wL u ++ wR v).length + (r + 1) := by
      rw [hlen]; ring
    rw [hexp] at b1 b2
    have hY : 0 ≤ gN g ^ (2 * (r + 1) * (wL u ++ wR v).length + (r + 1)) :=
      pow_nonneg (le_trans zero_le_one (gN_ge_one hg)) _
    obtain ⟨m1, m2⟩ := hCM _ hl
    rw [Prod.norm_def]
    exact max_le (b1.trans (mul_le_mul_of_nonneg_right m1 hY)) (b2.trans (mul_le_mul_of_nonneg_right m2 hY))
  obtain ⟨C, -, hC⟩ := fdb (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) hψ
    {g : Mat k r | g ∈ GV k r ∧ ε ≤ Gp g} _
    (fun g hg => by rw [← (hsph g hg.1 (by linarith [hg.2])).1, ← (hsph g hg.1 (by linarith [hg.2])).2.1]
                    exact (hsph g hg.1 (by linarith [hg.2])).2.2)
    gN (fun g hg => gN_ge_one hg.1) (2 * (r + 1)) (r + 1) M i H i E Φ hΦ hΦb
  refine ⟨C, fun u v huv g hg hge => ?_⟩
  have hw := hwl u v huv.1 huv.2.1
  rw [dLR_eq]
  have e : Dw (wL u ++ wR v) (fun g' => Pi (C6.unitOf T (Gp g') (om g'), C6.unitOf T' (Gp g') (om' g'))) g =
      Dw (wL u ++ wR v) (fun g' => Φ (utv ε T Gp om g', utv ε T' Gp om' g')) g := by
    refine Dw_congr_loc hw hOε (fun g' hg' hg'O => ?_) g hg (show ε / 2 < Gp g by linarith)
    obtain ⟨h1, h2, h3⟩ := hsph g' hg' hg'O
    rw [← hΦK _ h3, h1, h2]
  rw [e]
  have hl : (wL u ++ wR v).length = i := by rw [hlen]; exact huv.2.2
  have hb := hC (wL u ++ wR v) (admissible_of_unit_words huv) hl.le g ⟨hg, hge⟩
  rw [hl] at hb
  have hexp : (2 * (r + 1) + (r + 1)) * i = 3 * (r + 1) * i := by ring
  rwa [hexp] at hb

theorem fibre_cost_estimate : C6.FibCost := c6_fib_cost_of_pieces fibre_unit_normalization

end Formalism.FourierDecayAlt.P
end
end
