import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Clifford
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtIneL
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem twist_triv {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K]
    [Algebra K Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}
    (D : Dat Ω K c e ψ) (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) {C : Type} [Group C]
    (φ : G K Ω →* C) (hφ : (cycBar K Ω l).ker ≤ φ.ker) (m : ℕ) (hm : m ≠ 0)
    (h : ∀ s : G K Ω, galEmb ℚ K Ω s ∈ Ine (F := ℚ) A → φ s ≠ 1 → D.ΨQ (galEmb ℚ K Ω s) ^ m = 1) (g : G K Ω) :
    φ g = 1 := by
  have hl : l.Prime := Fact.out
  have hI : Ine (F := ℚ) A ≤ (galEmb ℚ K Ω).range := by
    rw [range_galEmb, ← D.η_ker]
    exact ((dat_facts D).2.2.2.2.2.2.2.2.2.2 A hA).1
  have hsur : ∀ u : ℤ_[l]ˣ, ∃ s : G K Ω, galEmb ℚ K Ω s ∈ Ine (F := ℚ) A ∧ cycZ K Ω l s = u := fun u => by
    obtain ⟨σ, hσ, hu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA u
    obtain ⟨s, rfl⟩ := hI hσ
    exact ⟨s, hσ, hu⟩
  by_contra hg
  obtain ⟨s, hs, hsg⟩ := hsur (cycZ K Ω l g)
  have hs1 : φ s ≠ 1 := by
    intro h1
    have : φ (g * s⁻¹) = 1 := hφ (by
      rw [MonoidHom.mem_ker, cycBar, MonoidHom.comp_apply, map_mul, map_inv, hsg, mul_inv_cancel, map_one])
    rw [map_mul, map_inv, h1, inv_one, mul_one] at this
    exact hg this
  have hu : IsUnit ((1 + l : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    simp
  obtain ⟨t, ht, htu⟩ := hsur hu.unit
  have ht1 : D.ΨQ (galEmb ℚ K Ω t) ^ m = 1 := by
    by_cases h1 : φ t = 1
    · have h2 := h (s * t) (by rw [map_mul]; exact mul_mem hs ht) (by rwa [map_mul, h1, mul_one])
      rwa [map_mul, map_mul, mul_pow, h s hs hs1, one_mul] at h2
    · exact h t ht h1
  have hn : Chr.dirG ℚ Ω ψ (galEmb ℚ K Ω t) ^ Nat.card (ZMod N)ˣ = 1 := by
    rw [Chr.dirG, MonoidHom.comp_apply, ← map_pow, pow_card_eq_one', map_one]
  have hc : (chiO ℚ Ω l c.O (galEmb ℚ K Ω t) : c.O) = ((1 + l : ℕ) : c.O) := by
    have : cycZ ℚ Ω l (galEmb ℚ K Ω t) = hu.unit := htu
    rw [chiO, MonoidHom.comp_apply, this]
    simp
  have h3 : ((D.Ψ (galEmb ℚ K Ω t) ^ Nat.card (ZMod N)ˣ : c.Oˣ) : c.O) = ((1 + l : ℕ) : c.O) ^ (e * Nat.card (ZMod N)ˣ) := by
    rw [Dat.Ψ, Chr.Psi, MonoidHom.mul_apply, mul_pow, hn, mul_one, zpow_natCast, MonoidHom.pow_apply, ← pow_mul,
      Units.val_pow_eq_pow_val, hc]
  have h4 : ((D.ΨQ (galEmb ℚ K Ω t) ^ Nat.card (ZMod N)ˣ : (PadicAlgCl l)ˣ) : PadicAlgCl l) =
      ((1 + l : ℕ) : PadicAlgCl l) ^ (e * Nat.card (ZMod N)ˣ) := by
    have := congrArg (algebraMap c.O (PadicAlgCl l)) h3
    rw [map_pow, map_natCast] at this
    rw [← this, Dat.ΨQ, MonoidHom.comp_apply, ← map_pow]
    rfl
  have h5 : ((1 + l : ℕ) : PadicAlgCl l) ^ (e * Nat.card (ZMod N)ˣ * m) = 1 := by
    rw [pow_mul, ← h4, ← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, ht1, one_pow, Units.val_one]
  have h6 : (1 + l) ^ (e * Nat.card (ZMod N)ˣ * m) = 1 := by exact_mod_cast h5
  have he := D.gd.e_pos
  have hN : 0 < Nat.card (ZMod N)ˣ := Nat.card_pos
  rcases Nat.pow_eq_one.1 h6 with h7 | h7
  · exact hl.ne_zero (by omega)
  · exact (mul_ne_zero (mul_ne_zero (by omega) hN.ne') hm) h7

theorem UpperTheory.V.U3.typeI_irr_cyc :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG 3 (PadicAlgCl l)} (h : D.IsPt U g₁ r),
      TypeI D.η r → Af.IsIrr ((D.rhoK r h.mult).comp (cycBar K Ω l).ker.subtype) := by
  intro hC Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hg r h hI
  have hirr : MatIrr ⊤ fun g => (D.rhoK r h.mult g : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) := by
    intro W hW
    refine hI W fun g hg v hv => ?_
    rw [D.η_ker, ← range_galEmb] at hg
    obtain ⟨s, rfl⟩ := hg
    exact hW s trivial v hv
  have key : MatIrr (cycBar K Ω l).ker fun g => (D.rhoK r h.mult g : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) := by
    by_contra hred
    obtain ⟨φ, hφ1, hker, -, M, hM⟩ := exists_selfTwist (D.rhoK r h.mult) (cycBar K Ω l).ker
      (fun a b => by simp [MonoidHom.mem_ker, mul_comm (cycBar K Ω l a)]) hirr hred
    obtain ⟨A, hA⟩ := (Chr.placesQ Ω).1 l Fact.out
    refine hφ1 (MonoidHom.ext (twist_triv D A hA φ hker 3 (by norm_num) fun s hs h1 => ?_))
    have hch := (pt_inertia_above hC D hg h A hA).1 _ hs
    have htr : (D.rhoK r h.mult s : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)).trace =
        (r0 D.η D.ΨQ (galEmb ℚ K Ω s)).mat.trace := by
      rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, ← hch]
      rfl
    have h2 := congrArg (fun X => (X * ((M⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))).trace)
      (hM s trivial)
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul] at h2
    rw [Matrix.trace_mul_cycle, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, htr,
      smul_eq_mul] at h2
    have h3 : (r0 D.η D.ΨQ (galEmb ℚ K Ω s)).mat.trace = 0 := by
      by_contra h0
      exact h1 (Units.ext (mul_right_cancel₀ h0 (h2.trans (one_mul _).symm)))
    rw [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.trace_diagonal, Fin.sum_univ_three] at h3
    generalize D.ΨQ (galEmb ℚ K Ω s) = a at h3 ⊢
    have h4 : (a : PadicAlgCl l) + 1 + (a : PadicAlgCl l)⁻¹ = 0 := by simpa [wt1] using h3
    have ha : (a : PadicAlgCl l) * (a : PadicAlgCl l)⁻¹ = 1 := mul_inv_cancel₀ a.ne_zero
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    linear_combination (a : PadicAlgCl l) * (a - 1) * h4 - ((a : PadicAlgCl l) - 1) * ha
  refine ⟨top_ne_bot, fun _ _ _ => trivial, fun W _ hW => key W fun g hg v hv => hW ⟨g, hg⟩ v hv⟩
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem left_conj {R : Type} [CommRing R] {m : ℕ} (x y : GG m R) (h1 : x.mat = 1) (h2 : x.right = -1)
    (h3 : y.right = 1) : (x * y * x⁻¹).left = theta y.left := by
  have hl : x.left = 1 := Units.ext h1
  simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
    hl, h2, h3, inv_one, mul_one, one_mul, sgnAct_neg_one, map_one]

private theorem pairing_theta {R : Type} [CommRing R] {m : ℕ} (a : GL (Fin m) R) :
    (a : Matrix (Fin m) (Fin m) R)ᵀ * Jmat R m * (theta a : GL (Fin m) R) = Jmat R m := by
  rw [theta_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (Jmat R m) (Jmat R m), Jmat_mul_Jmat,
    Matrix.mul_one, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one,
    Matrix.one_mul]

private theorem cont_hom {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ] [Monoid M] [TopologicalSpace M]
    (f : Γ →* Mˣ) (h : Continuous fun g => (f g : M)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

private theorem irr_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (ρ : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) :
    (Af.tw ρ χ⁻¹).comp χ.ker.subtype = ρ.comp χ.ker.subtype := by
  refine MonoidHom.ext fun s => Units.ext ?_
  have hs : χ s = 1 := s.2
  show (Af.tw ρ χ⁻¹ s : Matrix (Fin n) (Fin n) k) = ρ s
  rw [Af.tw_val, MonoidHom.inv_apply, hs, inv_one, Units.val_one, one_smul]

private theorem ad_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (ρ : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (s : Γ)
    (X : Matrix (Fin n) (Fin n) k) :
    (Af.tw ρ χ s : Matrix (Fin n) (Fin n) k) * X * ((Af.tw ρ χ s)⁻¹ : GL (Fin n) k) =
      (ρ s : Matrix (Fin n) (Fin n) k) * X * ((ρ s)⁻¹ : GL (Fin n) k) := by
  rw [← map_inv, ← map_inv, Af.tw_val, Af.tw_val, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_smul]

theorem UpperTheory.V.U3.bloch_kato_type_one :
    CohInp → Af.AdVanishK → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG 3 (PadicAlgCl l)} (h : D.IsPt U g₁ r), ∀ [IsCMField K] (ι : Qbar l ≃+* ℂ),
      TypeI D.η r → D.IsAutI ι r h.mult → Af.BlochKatoSelmerVanishes l (adRep r) := by
  intro hC hA Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hM r h _ ι hI hAut
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsAlgClosure K Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  have hK : ∀ s : G K Ω, (r (galEmb ℚ K Ω s)).right = 1 := fun s =>
    (h.mult _).trans (show galEmb ℚ K Ω s ∈ D.η.ker from D.η_ker ▸ galEmb_mem ℚ K Ω s)
  have hc : (r D.cc).right = -1 := (h.mult _).trans hM.ηc
  have hz : Continuous fun s : G K Ω => ((cycZ K Ω l s : ℤ_[l]ˣ) : ℤ_[l]) :=
    Units.continuous_val.comp (continuous_cycZ K Ω l)
  have hcyc : Continuous fun s : G K Ω => (cycBar K Ω l s : Qbar l) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp
      (continuous_subtype_val.comp hz)
  refine hA K D.gd.quad 3 (by norm_num) l Ω ι _ ?_ hAut ?_ _ ⟨D.cc, Jgl _ 3, D.conj, ?_, ?_, ?_⟩
  · refine cont_hom _ ?_
    simp only [Af.tw_val, MonoidHom.inv_apply, ← map_inv]
    exact (hcyc.comp continuous_inv).smul (h.cont.comp (galEmbTop ℚ K Ω).1.continuous)
  · rw [irr_tw]
    exact typeI_irr_cyc hC D hM h hI
  · intro s s' hs
    have hs' : galEmb ℚ K Ω s' = D.cc * galEmb ℚ K Ω s * D.cc⁻¹ := hs
    have h1 : cycBar K Ω l s' = cycBar K Ω l s := by
      show cycBar ℚ Ω l (galEmb ℚ K Ω s') = cycBar ℚ Ω l (galEmb ℚ K Ω s)
      rw [hs', map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    have h2 : D.rhoK r h.mult s' = theta (D.rhoK r h.mult s) := by
      rw [D.rhoK_apply, D.rhoK_apply, hs', map_mul, map_mul, map_inv]
      exact left_conj _ _ h.norm.atc hc (hK s)
    rw [Af.tw_val, Af.tw_val, h2, MonoidHom.inv_apply, MonoidHom.inv_apply, h1, Matrix.transpose_smul,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Units.val_mul]
    have h3 : (cycBar K Ω l ^ (1 - ((3 : ℕ) : ℤ))) s = (cycBar K Ω l s)⁻¹ * (cycBar K Ω l s)⁻¹ := by
      rw [MonoidHom.zpow_apply, show (1 - ((3 : ℕ) : ℤ)) = -1 + -1 by norm_num, _root_.zpow_add, _root_.zpow_neg_one]
    rw [h3]
    exact congrArg _ (pairing_theta _)
  · intro s X
    rw [ad_tw]
    show (r (galEmb ℚ K Ω s)).adFun X = _
    rw [GG.adFun, if_pos (hK s)]
    rfl
  · intro X
    have hl : (r D.cc).left = 1 := Units.ext h.norm.atc
    show (r D.cc).adFun X = _
    rw [GG.adFun, hc, if_neg (by decide), h.norm.atc, hl, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
    rfl
end
