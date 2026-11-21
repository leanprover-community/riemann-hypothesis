import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ContinuousResLe

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.phiConj :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D) (s : W.HidaSetting l T.L Ω), ∃ cF : G T.F Ω, ∀ g : G T.L Ω, ∃ g' : G T.L Ω, W.resP T.L Ω g' = s.c * W.resP T.L Ω g * s.c⁻¹ ∧ resLe T.F_le g' = cF * resLe T.F_le g * cF⁻¹ := by
  intro Ω _ _ _ l _ c D T s
  obtain ⟨j, hj⟩ := s.hc
  have hfixF : ∀ x : T.F, s.c (x : Ω) = x := by
    intro x
    have hr := IsTotallyReal.complexEmbedding_isReal (j.comp (algebraMap T.F Ω))
    have := RingHom.congr_fun (NumberField.ComplexEmbedding.isReal_iff.1 hr) x
    simp only [NumberField.ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply] at this
    apply j.injective
    rw [hj]
    exact this
  have hstab : ∀ (τ : G (W.Lp T.L) Ω) (x : T.L), ∃ y : T.L, τ (x : Ω) = y := by
    intro τ x
    exact ⟨τ.restrictNormal T.L x, (AlgEquiv.restrictNormal_commutes τ T.L x).symm⟩
  let cF : G T.F Ω := AlgEquiv.ofRingEquiv (f := s.c.toRingEquiv) (fun x => hfixF x)
  refine ⟨cF, fun g => ?_⟩
  let σ : G (W.Lp T.L) Ω := s.c * W.resP T.L Ω g * s.c⁻¹
  have hσ : ∀ x : T.L, σ (x : Ω) = x := by
    intro x
    obtain ⟨y, hy⟩ := hstab s.c⁻¹ x
    have h1 : g (y : Ω) = y := g.commutes y
    have h2 : s.c (y : Ω) = x := by
      rw [← hy]
      exact mul_inv_apply (σ := s.c) (x : Ω)
    show s.c (g (s.c⁻¹ (x : Ω))) = x
    rw [hy, h1, h2]
  let g' : G T.L Ω := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun x => hσ x)
  refine ⟨g', ?_, ?_⟩
  · ext x
    rfl
  · ext x
    rfl
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private def formJ (R : Type) [CommRing R] : M4 R := !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]

private theorem formJ_mul (R : Type) [CommRing R] : (formJ R).transpose * formJ R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [formJ, Matrix.mul_apply, Fin.sum_univ_four]

private theorem adj_eq_conj {R : Type} [CommRing R] (M : M4 R) :
    adj M = formJ R * (M.transpose * (formJ R).transpose) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [formJ, adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four]

theorem UpperTheory.V.Ws.phiAdj :
    ∀ {R : Type} [CommRing R] (ν : R) (M N : M4 R), IsGSp ν M → M * N = 1 → (ν • N).charpoly = M.charpoly := by
  intro R _ ν M N hM hMN
  have h1 : adj M = ν • N := by
    have h2 : adj M * M * N = ν • N := by
      unfold IsGSp at hM
      rw [hM, smul_mul_assoc, one_mul]
    rw [mul_assoc, hMN, mul_one] at h2
    exact h2
  rw [← h1, adj_eq_conj, Matrix.charpoly_mul_comm, mul_assoc, formJ_mul, mul_one, Matrix.charpoly_transpose]
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem charpoly_gsp_conj_inv_scaled {R Γ : Type} [CommRing R] [Group Γ] (r : Γ →* M4 R) (x y : Γ) (ν s s' t : R)
    (hr : IsGSp ν (r x)) (hs : s * s' = 1) (ht : t = s * ν) :
    (t • r (y * x * y⁻¹)⁻¹).charpoly = (s • r x).charpoly := by
  have h1 : IsGSp (s * s * ν) (s • r x) := by
    have ha : adj (s • r x) = s • adj (r x) := by
      ext i j
      simp only [adj_apply, Matrix.smul_apply]
      rw [smul_comm]
    unfold IsGSp at hr ⊢
    rw [ha, Matrix.smul_mul, Matrix.mul_smul, hr, smul_smul, smul_smul]
  have h2 : (s • r x) * (s' • r x⁻¹) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs, one_smul, ← map_mul, mul_inv_cancel, map_one]
  have h3 := phiAdj _ _ _ h1 h2
  rw [← h3, smul_smul]
  have h4 : s * s * ν * s' = t := by rw [ht]; linear_combination (s * ν) * hs
  rw [h4]
  have h5 : t • r (y * x * y⁻¹)⁻¹ = r y * ((t • r x⁻¹) * r y⁻¹) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, ← map_mul, ← map_mul]
    congr 2
    group
  rw [h5, Matrix.charpoly_mul_comm, Matrix.mul_assoc, ← map_mul, inv_mul_cancel, map_one, Matrix.mul_one]

theorem UpperTheory.V.Ws.phiPol :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∀ g, ∃ g', K.V.pr g' = (K.V.frame.conj (K.V.pr g))⁻¹ ∧ (((K.V.frame.eps c'.O X.A (K.V.pr g) ^ (1 - ((4 : ℕ) : ℤ)) : X.Aˣ) : X.A) • K.rho X n g').charpoly = (K.rho X n g).charpoly := by
  intro Ω _ _ _ l _ c D T c' h K X n g
  obtain ⟨cF, hc⟩ := phiConj T K.s
  obtain ⟨g₂, h1, h2⟩ := hc g
  refine ⟨g₂⁻¹, ?_, ?_⟩
  · rw [map_inv]
    congr 1
    apply Subtype.ext
    change toGS Ω K.V.S' (W.resP T.L Ω g₂) = toGS Ω K.V.S' K.s.c * toGS Ω K.V.S' (W.resP T.L Ω g) * (toGS Ω K.V.S' K.s.c)⁻¹
    rw [h1, map_mul, map_mul, map_inv]
  · obtain ⟨k1, k2, -⟩ := K.conj g g₂ h1
    have he : K.V.frame.eps c'.O X.A (K.V.pr g) =
        Units.map (algebraMap c'.O X.A : c'.O →* X.A) (chiO T.L Ω l c'.O g) := by
      have : K.V.ε (toGS Ω K.V.S' (W.resP T.L Ω g)) = cycZ T.L Ω l g := DFunLike.congr_fun K.V.hε (W.resP T.L Ω g)
      apply Units.ext
      change algebraMap c'.O X.A (algebraMap ℤ_[l] c'.O (K.V.ε (toGS Ω K.V.S' (W.resP T.L Ω g)) : ℤ_[l]ˣ)) = _
      rw [this]
      rfl
    rw [Link.rho_apply, Link.rho_apply, smul_smul, map_inv, h2, he]
    refine charpoly_gsp_conj_inv_scaled X.P.r _ _ _ _ (algebraMap c'.O X.A (K.sc n g⁻¹)) _ (X.pair.mult (resLe T.F_le g)) ?_ ?_
    · rw [← map_mul, ← Link.sc_mul, mul_inv_cancel, Link.sc_one, map_one]
    · have hb : K.β g₂⁻¹ = K.β g := by rw [map_inv]; exact (eq_inv_of_mul_eq_one_left k2).symm
      rw [← map_zpow, Units.coe_map]
      change algebraMap c'.O X.A _ * _ = _ * algebraMap c'.O X.A (inc h (D.th (resQ T.L g)))
      rw [← map_mul, ← map_mul]
      congr 1
      simp only [Link.sc, hb]
      set e := chiO T.L Ω l c'.O g
      have e1 : ((e ^ (1 - ((4 : ℕ) : ℤ)) : c'.Oˣ) : c'.O) * (e : c'.O) ^ 3 = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_add]
        norm_num
      have e2 : ((K.κ g₂⁻¹ : c'.Oˣ) : c'.O) * K.κ g₂ = 1 := by
        rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
      generalize ((e ^ (1 - ((4 : ℕ) : ℤ)) : c'.Oˣ) : c'.O) = u at e1 ⊢
      generalize ((K.κ g₂⁻¹ : c'.Oˣ) : c'.O) = v at e2 ⊢
      generalize (inc h (D.th (resQ T.L g)) : c'.O) = θ at k1 ⊢
      generalize ((K.β g : c'.Oˣ) : c'.O) ^ n = b
      linear_combination (-u * v * b) * k1 + (b * (K.κ g : c'.O) * θ * u * (e : c'.O) ^ 3) * e2 + (b * (K.κ g : c'.O) * θ) * e1
end
