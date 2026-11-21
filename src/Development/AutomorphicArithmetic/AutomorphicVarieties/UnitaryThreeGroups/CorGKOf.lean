import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsDat
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ULocEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.RingEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ModelEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ModelUpper
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.VlenLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtHypOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsFlagCharactersOfUpperTriangular
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdmissibleOfTypeII
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CoefIndep
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.OrbEquiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.GdOfHost
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.OrbFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.OrbSum

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

section Transfer

variable {O O' : Type} [CommRing O] [CommRing O'] {N : ℕ} (f : O →+* O')

private def chHom : DirichletCharacter O N →* DirichletCharacter O' N where
  toFun χ := χ.ringHomComp f
  map_one' := MulChar.ringHomComp_one f
  map_mul' a b := MulChar.ringHomComp_mul a b f

private theorem chHom_inj (hf : Function.Injective f) : Function.Injective (chHom (N := N) f) :=
  MulChar.injective_ringHomComp hf

private theorem chHom_comp (r : ℕ) (χ : DirichletCharacter O N) : chHom f (comp r χ) = comp r (chHom f χ) := by
  refine MulChar.ext fun a => ?_
  show f (comp r χ a) = _
  simp only [HV.comp, MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MulChar.coe_toUnitHom]
  rfl

private theorem chHom_chiP (hf : Function.Injective f) (l : ℕ) (χ : DirichletCharacter O N) :
    chHom f (chiP l χ) = chiP l (chHom f χ) := by
  have h : chHom f (th0 l χ) = th0 l (chHom f χ) := by
    simp only [th0, lPrime, lPart, map_mul, map_inv, map_pow, orderOf_injective _ (chHom_inj f hf)]
  simp only [chiP, map_mul, map_inv, chHom_comp, h]

private theorem gd_chHom (hf : Function.Injective f) [NeZero N] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    {K : Type} [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {e : ℕ} (χ : DirichletCharacter O N) :
    GD Ω K l e (chHom f χ) ↔ GD Ω K l e χ := by
  have h1 : orderOf (chHom f χ) = orderOf χ := orderOf_injective _ (chHom_inj f hf) _
  have h2 : comp l (chHom f χ) ^ 2 = 1 ↔ comp l χ ^ 2 = 1 := by
    rw [← chHom_comp, ← map_pow, map_eq_one_iff _ (chHom_inj f hf)]
  have h3 : PsiEven e (chHom f χ) ↔ PsiEven e χ := by
    show f (χ (-1)) = _ ↔ χ (-1) = _
    rw [← hf.eq_iff (a := χ (-1)), map_pow, map_neg f, map_one f]
  have h4 : (Chr.dirG ℚ Ω (chiP l (chHom f χ))).ker = (Chr.dirG ℚ Ω (chiP l χ)).ker := by
    rw [← chHom_chiP f hf]
    ext g
    simp only [MonoidHom.mem_ker, Chr.dirG, MonoidHom.comp_apply, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
    exact map_eq_one_iff f hf
  exact ⟨fun h => ⟨h.l_odd, h.e_pos, h.N_even, h1 ▸ h.ord, h2.1 h.ine, h3.1 h.par, h.quad, h.imag, h.l_cop, h.cop,
      h4 ▸ h.eta, h.gen⟩,
    fun h => ⟨h.l_odd, h.e_pos, h.N_even, h1 ▸ h.ord, h2.2 h.ine, h3.2 h.par, h.quad, h.imag, h.l_cop, h.cop,
      h4 ▸ h.eta, h.gen⟩⟩

end Transfer

private theorem exists_unram {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (ψ : DirichletCharacter c.O N)
    (h : ¬ l ∣ orderOf ψ) : ∃ (c' : Coef l) (ψ' : DirichletCharacter c'.O N), eO l c'.O = 1 ∧
      ∀ a : ZMod N, ((ψ a : c.O) : PadicAlgCl l) = ((ψ' a : c'.O) : PadicAlgCl l) := by
  haveI : NeZero (orderOf ψ) := ⟨fun h0 => h (h0 ▸ dvd_zero l)⟩
  obtain ⟨c', he, hr⟩ := (coefSup l).2.1 (orderOf ψ) h
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot c'.O (orderOf ψ)
  have hζ' : IsPrimitiveRoot (ζ : PadicAlgCl l) (orderOf ψ) :=
    hζ.map_of_injective (f := c'.O.val) Subtype.val_injective
  have hmem : ∀ a : ZMod N, ((ψ a : c.O) : PadicAlgCl l) ∈ c'.O := by
    intro a
    by_cases ha : IsUnit a
    · obtain ⟨u, rfl⟩ := ha
      have h1 : ψ u ^ orderOf ψ = 1 := by
        rw [← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe]
      have h2 : ((ψ u : c.O) : PadicAlgCl l) ^ orderOf ψ = 1 := by
        rw [← SubmonoidClass.coe_pow, h1]; rfl
      obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one h2
      rw [← hi]
      exact pow_mem ζ.2 i
    · rw [ψ.map_nonunit ha]
      exact zero_mem _
  refine ⟨c', ⟨⟨⟨fun a => ⟨_, hmem a⟩, Subtype.ext ?_⟩, fun a b => Subtype.ext ?_⟩, fun a ha => Subtype.ext ?_⟩, he,
    fun _ => rfl⟩
  · show ((ψ 1 : c.O) : PadicAlgCl l) = 1
    rw [map_one]; rfl
  · show ((ψ (a * b) : c.O) : PadicAlgCl l) = _
    rw [map_mul]; rfl
  · show ((ψ a : c.O) : PadicAlgCl l) = 0
    rw [ψ.map_nonunit ha]; rfl

private theorem isPush_push {O Γ R κ : Type} [CommRing O] [Group Γ] [CommRing R] [Algebra O R] [CommRing κ] [Algebra O κ]
    (f : R →ₐ[O] κ) (r : Γ →* GG 3 R) : IsPush (f.comp (entAlg O r).val) r (push f r) :=
  fun g => ⟨rfl, fun a b => ⟨Algebra.subset_adjoin ⟨g, a, b, rfl⟩, rfl⟩⟩

private theorem trace_reducible_three_dim {Γ R : Type} [Group Γ] [CommRing R] (η : Γ →* ℤˣ) (Ψ : Γ →* Rˣ) (g : Γ) :
    (r0 η Ψ g).mat.trace = (Ψ g : R) + 1 + (((Ψ g)⁻¹ : Rˣ) : R) := by
  simp [GG.mat, tor_val, Matrix.trace_diagonal, Fin.sum_univ_three, wt1]

private theorem oneChar_unram (hI : Inp) (hA : Aut.AutomorphyUnramifiedCoefficients)
    (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (he : eO l c.O = 1) (hG : GD Ω K l e ψ) (ι : Qbar l ≃+* ℂ) (σ : G K Ω) (t : Qbar l)
    (ht : t = algebraMap c.O (PadicAlgCl l) ((Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ K Ω σ) : c.O) + 1 +
      (((Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ K Ω σ))⁻¹ : c.Oˣ) : c.O)))
    (hne : ∀ ρ : G K Ω →* GL (Fin 3) (Qbar l), Af.Adm3 ι e N ρ ∨ Af.Adm2 ι e (N * (discr K).natAbs) ρ →
      (ρ σ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace ≠ t) :
    Vlen Ω c e ψ ≠ ⊤ ∧ ∃ X : Finset (G K Ω →* GL (Fin 3) (Qbar l)),
      (∀ ρ ∈ X, Af.Adm3 ι e N ρ ∨ Af.Adm2 ι e (N * (discr K).natAbs) ρ) ∧ (∀ ρ ∈ X, ∀ ρ' ∈ X, Af.RepIso ρ ρ' → ρ = ρ') ∧
      Vn Ω c e ψ ≤ 2 * ∑ ρ ∈ X, vl l ((ρ σ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace - t) := by
  classical
  obtain ⟨D⟩ := exists_dat hG
  obtain ⟨g₁, hM, hFin, hB, hW⟩ := hA Ω K l c N e ψ D he ι
  obtain ⟨U⟩ := exists_uLoc hI.toCohInp D
  obtain ⟨S⟩ := exists_ring hI.toCohInp D U g₁ hM
  obtain ⟨M⟩ := exists_model hI.toCohInp hI.lemP D hM S
  have hmult : ∀ f : S.R →ₐ[c.O] PadicAlgCl l, HasMult D.η (push f S.r.hom) := fun f g => S.r.hasMult g
  let ρ : (S.R →ₐ[c.O] PadicAlgCl l) → (G K Ω →* GL (Fin 3) (Qbar l)) := fun f => D.rhoK (push f S.r.hom) (hmult f)
  have hσ : D.η (galEmb ℚ K Ω σ) = 1 := by
    rw [← MonoidHom.mem_ker, D.η_ker]
    exact galEmb_mem ℚ K Ω σ
  have htr : ∀ f, trDiff D.η D.Ψ S.r.hom (galEmb ℚ K Ω σ) f =
      (ρ f σ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace - t := by
    intro f
    rw [trDiff, trace_reducible_three_dim, ht]
    congr 1
    exact AddMonoidHom.map_trace (f : S.R →+* PadicAlgCl l) _
  have hadm : ∀ f, TwoPt D.η S.r.hom f → Af.Adm3 ι e N (ρ f) ∨ Af.Adm2 ι e (N * (discr K).natAbs) (ρ f) := by
    intro f hf
    have hp := isPt_push D hM S f hf.1
    rcases (twoPt_shape S hG.l_odd hM f hf).1 with h | h
    · exact Or.inl (admissible_rank_three_type_one hI.toCohInp D hM hp ι h (hB U S _ _ _ (isPush_push f _) h))
    · exact Or.inr (admissible_of_typeII hI.toCohInp D hM hp ι h
        (hW U S _ _ (isPush_push f _) h (typeII_facts hI.toCohInp D hM hp h).1))
  obtain ⟨hlen, T, hT, hTo, hle⟩ := model_upper S M hG.l_odd hM hI.lemM (hFin U S)
    (ptHyp_of hI D hM S ι hB hW M.x₀ M.base) (galEmb ℚ K Ω σ) hσ
    fun f hf => by rw [htr]; exact sub_ne_zero.2 (hne _ (hadm f hf))
  have hV := vlen_le hI.toCohInp hI.lemM' D hM S M
  have hinj : ∀ f ∈ T, ∀ f' ∈ T, Af.RepIso (ρ f) (ρ f') → f = f' := by
    rintro f hf f' hf' ⟨g, hg⟩
    obtain ⟨s, hs⟩ := (twoPt_shape S hG.l_odd hM f (hT.1 f hf)).2 f' (hT.1 f' hf').1 ⟨g, fun x hx => by
      rw [D.η_ker, ← range_galEmb] at hx
      obtain ⟨y, rfl⟩ := hx
      exact (congrArg Units.val (eq_mul_inv_iff_mul_eq.1 (hg y))).symm⟩
    exact hTo f hf f' hf' s hs
  refine ⟨ne_top_of_le_ne_top hlen hV, T.image ρ, fun x hx => ?_, fun x hx x' hx' h => ?_, ?_⟩
  · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hx
    exact hadm f (hT.1 f hf)
  · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.1 hx'
    rw [hinj f hf f' hf' h]
  · rw [Finset.sum_image fun f hf f' hf' h => hinj f hf f' hf' ⟨1, fun s => by rw [h, one_mul, inv_one, mul_one]⟩]
    simp only [← htr]
    exact (Chr.nrm_mono l hV hlen).trans hle

theorem UpperTheory.V.U3.oneChar :
    Inp → Aut.AutomorphyUnramifiedCoefficients → OneChar := by
  intro hI hA Ω _ _ _ K _ _ _ _ _ l _ c N _ e ψ hG ι σ t ht hne
  obtain ⟨c', ψ', he, hψ⟩ := exists_unram c ψ hG.ord
  have h1 : chHom c.O.val.toRingHom ψ = chHom c'.O.val.toRingHom ψ' := MulChar.ext fun a => hψ a
  have hG' : GD Ω K l e ψ' :=
    (gd_chHom c'.O.val.toRingHom Subtype.val_injective ψ').1
      (h1 ▸ (gd_chHom c.O.val.toRingHom Subtype.val_injective ψ).2 hG)
  obtain ⟨h2, h3⟩ := coefIndep Ω l c c' N e ψ ψ' hψ
  have h4 : ∀ g, Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (Chr.Psi l e (Chr.dirG ℚ Ω ψ) g) =
      Units.map (algebraMap c'.O (PadicAlgCl l)).toMonoidHom (Chr.Psi l e (Chr.dirG ℚ Ω ψ') g) := by
    intro g
    simp only [Chr.Psi, MonoidHom.mul_apply, MonoidHom.zpow_apply, map_mul, map_zpow]
    congr 1
    exact Units.ext (hψ _)
  have h5 := congrArg Units.val (h4 (galEmb ℚ K Ω σ))
  have h6 := congrArg (fun u : (PadicAlgCl l)ˣ => (u⁻¹).val) (h4 (galEmb ℚ K Ω σ))
  rw [Ne, h2, h3]
  refine oneChar_unram hI hA Ω K l c' N e ψ' he hG' ι σ t ?_ hne
  rw [ht, map_add, map_add, map_add, map_add, map_one, map_one]
  exact congrArg₂ (· + ·) (congrArg (· + 1) h5) h6
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private lemma corG_sum_log (n : ℤ) (hn : n ≠ 0) (Ls : Finset Nat.Primes) :
    ∑ l ∈ Ls, Real.log (l : ℕ) * (padicValInt l n : ℝ) ≤ Real.log |(n : ℝ)| := by
  classical
  have hdvd : ∏ l ∈ Ls, ((l : ℕ) : ℤ) ^ (padicValInt l n) ∣ n := by
    apply Finset.prod_dvd_of_coprime
    · intro a _ b _ hab
      simp only [Function.onFun]
      apply IsCoprime.pow
      rw [Nat.isCoprime_iff_coprime]
      exact (Nat.coprime_primes a.2 b.2).mpr (fun h => hab (Subtype.ext h))
    · intro l _
      haveI : Fact (Nat.Prime l) := ⟨l.2⟩
      exact padicValInt_dvd n
  have hP : (∏ l ∈ Ls, ((l : ℕ) : ℝ) ^ (padicValInt l n)) ≤ |(n : ℝ)| := by
    have h1 := Int.le_of_dvd (abs_pos.mpr hn) ((dvd_abs _ _).mpr hdvd)
    have h2 : ((∏ l ∈ Ls, ((l : ℕ) : ℤ) ^ (padicValInt l n) : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h2
    exact h2
  have hpos : ∀ l ∈ Ls, (0 : ℝ) < ((l : ℕ) : ℝ) ^ (padicValInt l n) :=
    fun l _ => pow_pos (by exact_mod_cast l.2.pos) _
  calc ∑ l ∈ Ls, Real.log (l : ℕ) * (padicValInt l n : ℝ)
      = ∑ l ∈ Ls, Real.log (((l : ℕ) : ℝ) ^ (padicValInt l n)) := by
        apply Finset.sum_congr rfl
        intro l _
        rw [Real.log_pow]
        ring
    _ = Real.log (∏ l ∈ Ls, ((l : ℕ) : ℝ) ^ (padicValInt l n)) :=
        (Real.log_prod (fun l hl => (hpos l hl).ne')).symm
    _ ≤ Real.log |(n : ℝ)| := Real.log_le_log (Finset.prod_pos hpos) hP

theorem UpperTheory.V.U3.corGK :
    PropGK → CorGK := by
  intro hP K _ _
  obtain ⟨c₅, A, hK⟩ := hP K
  refine ⟨c₅, A, ?_⟩
  intro Ω _ _ _ _ e N _ H p p' hp hp' hne hd hd' c Ls hL
  rcases Ls.eq_empty_or_nonempty with rfl | ⟨l₀, hl₀⟩
  · refine ⟨by simp, ?_⟩
    rw [Finset.sum_empty]
    have h1 := Real.log_natCast_nonneg p
    have h2 := Real.log_natCast_nonneg p'
    positivity
  have he : 1 ≤ e := by
    obtain ⟨ψ, _, h⟩ := hL l₀ hl₀
    exact h.e_pos
  obtain ⟨n, hn, hb, h⟩ := hK e N H p he hp hd
  obtain ⟨n', hn', hb', h'⟩ := hK e N H p' he hp' hd'
  have key : ∀ l ∈ Ls, (∀ ψ ∈ orb (c l) H, Vlen Ω (c l) e ψ ≠ ⊤) ∧
      ∑ ψ ∈ orb (c l) H, Vn Ω (c l) e ψ ≤ 2 * (padicValInt l n : ℝ) + 2 * (padicValInt l n' : ℝ) := by
    intro l hl
    have a1 : (0 : ℝ) ≤ (padicValInt l n : ℝ) := Nat.cast_nonneg _
    have a2 : (0 : ℝ) ≤ (padicValInt l n' : ℝ) := Nat.cast_nonneg _
    by_cases hlp : (l : ℕ) = p
    · have hlp' : (l : ℕ) ≠ p' := fun x => hne (hlp.symm.trans x)
      obtain ⟨b1, b2⟩ := h' Ω l hlp' (c l) (hL l hl)
      exact ⟨b1, by linarith⟩
    · obtain ⟨b1, b2⟩ := h Ω l hlp (c l) (hL l hl)
      exact ⟨b1, by linarith⟩
  refine ⟨fun l hl => (key l hl).1, ?_⟩
  have s1 := corG_sum_log n hn Ls
  have s2 := corG_sum_log n' hn' Ls
  calc _ ≤ ∑ l ∈ Ls, Real.log (l : ℕ) * (2 * (padicValInt l n : ℝ) + 2 * (padicValInt l n' : ℝ)) :=
        Finset.sum_le_sum fun l hl => mul_le_mul_of_nonneg_left (key l hl).2 (Real.log_natCast_nonneg _)
    _ = 2 * ∑ l ∈ Ls, Real.log (l : ℕ) * (padicValInt l n : ℝ) + 2 * ∑ l ∈ Ls, Real.log (l : ℕ) * (padicValInt l n' : ℝ) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ ≤ _ := by nlinarith
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem absorb (A N t e : ℝ) (k a : ℕ) (hk : A ≤ 16 ^ k) (hN : 16 ≤ N) (he : 0 ≤ e) (het : e + 1 ≤ t) :
    A * N * (N * (e + 1)) ^ a ≤ (N * t) ^ (k + 1 + a) := by
  have h0 : 0 ≤ N := by linarith
  have ht : 1 ≤ t := by linarith
  have h1 : A ≤ N ^ k := hk.trans (pow_le_pow_left₀ (by norm_num) hN k)
  have h2 : N ≤ N * t := le_mul_of_one_le_right h0 ht
  calc A * N * (N * (e + 1)) ^ a ≤ N ^ k * N * (N * t) ^ a := by gcongr
    _ ≤ (N * t) ^ k * (N * t) * (N * t) ^ a := by gcongr
    _ = (N * t) ^ (k + 1 + a) := by ring

theorem UpperTheory.V.U3.countI :
    CorGK → CountI := by
  intro hC χ
  classical
  obtain ⟨hpK, hpK4, hpK7, hpKcop⟩ := (pK_pOne_prime_conditions χ).1
  obtain ⟨hdisc, -, -, -⟩ := kstar (pK χ) hpK hpK4
  obtain ⟨c₅, A, hcor⟩ := hC (Kstar (pK χ))
  obtain ⟨r₁, hr₁B, hr₁⟩ := Nat.exists_infinite_primes (30 * χ.N * pK χ + 1)
  obtain ⟨r₂, hr₂B, hr₂⟩ := Nat.exists_infinite_primes (r₁ + 1)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (2 * (c₅ : ℝ) * (Real.log r₁ + Real.log r₂)) (by norm_num : (1 : ℝ) < 16)
  refine ⟨k + 1 + A, r₁, r₂, hr₁, hr₂, ?_⟩
  intro h hχ h1q h1d h2q h2d t hBig e he het Ω _ _ _ c Ls hLs
  subst hχ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  letI : Algebra (Kstar (pK h.chi)) Ω :=
    (IsAlgClosed.lift (M := Ω) (R := ℚ) (S := Kstar (pK h.chi))).toRingHom.toAlgebra
  obtain ⟨-, -, h16, -, -, hprimeN, -⟩ := hostIndex h
  have hN0 := h.N_pos
  have hqpos : 0 < h.chi.N := Nat.pos_of_ne_zero (h.chi.ne.out)
  have hnd : ∀ p : ℕ, p.Prime → 30 * h.chi.N * pK h.chi + 1 ≤ p → p < h.q1 → p < h.d →
      ¬ p ∣ 30 * h.N * (NumberField.discr (Kstar (pK h.chi))).natAbs := by
    intro p hp hpB hpq hpd hdiv
    rw [hdisc, Int.natAbs_neg, Int.natAbs_natCast] at hdiv
    have hp30 : 30 < p := by nlinarith [hpK7]
    rcases (Nat.Prime.dvd_mul hp).1 hdiv with h1 | h1
    · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
      · have := Nat.le_of_dvd (by norm_num) h2
        omega
      · rcases (hprimeN p hp).1 h2 with h3 | h3 | h3 | h3
        · omega
        · have := Nat.le_of_dvd hqpos h3
          nlinarith [hpK7]
        · omega
        · omega
    · have := Nat.le_of_dvd (by omega) h1
      nlinarith [hqpos]
  have hnd1 := hnd r₁ hr₁ hr₁B h1q h1d
  have hnd2 := hnd r₂ hr₂ (by omega) h2q h2d
  have hne : r₁ ≠ r₂ := by omega
  set T : Finset (Subgroup (ZMod h.N)ˣ) :=
    Ls.biUnion (fun l => (h.X (c l) e).image (fun ψ => (MulChar.toUnitHom ψ).ker)) with hT
  have hcorK : ∀ K' : Subgroup (ZMod h.N)ˣ,
      (∀ l ∈ Ls.filter (fun l => ∃ ψ ∈ h.X (c l) e, (MulChar.toUnitHom ψ).ker = K'),
        ∀ ψ ∈ orb (c l) K', Vlen Ω (c l) e ψ ≠ ⊤) ∧
      ∑ l ∈ Ls.filter (fun l => ∃ ψ ∈ h.X (c l) e, (MulChar.toUnitHom ψ).ker = K'),
        Real.log ((l : ℕ) : ℝ) * ∑ ψ ∈ orb (c l) K', Vn Ω (c l) e ψ ≤
        2 * (c₅ : ℝ) * (K'.index.totient : ℝ) * ((h.N : ℝ) * ((e : ℝ) + 1)) ^ A *
          (Real.log r₁ + Real.log r₂) := by
    intro K'
    refine hcor Ω e h.N K' r₁ r₂ hr₁ hr₂ hne hnd1 hnd2 c _ ?_
    intro l hl
    obtain ⟨hlLs, ψ, hψ, hker⟩ := Finset.mem_filter.1 hl
    obtain ⟨hchar, hpar⟩ := (Host.mem_X h).1 hψ
    exact ⟨ψ, (mem_orb _).2 hker, gdOfHost h t hBig Ω l e (hLs l hlLs).1 he het (hLs l hlLs).2 _ ψ hchar hpar⟩
  have hmapT : ∀ l ∈ Ls, ∀ ψ ∈ h.X (c l) e, (MulChar.toUnitHom ψ).ker ∈ T := by
    intro l hl ψ hψ
    rw [hT, Finset.mem_biUnion]
    exact ⟨l, hl, Finset.mem_image_of_mem _ hψ⟩
  have hsumT : ∑ K' ∈ T, ((K'.index.totient : ℕ) : ℝ) ≤ (h.N : ℝ) := by
    have hcyc : ∀ K' ∈ T, IsCyclic ((ZMod h.N)ˣ ⧸ K') := by
      intro K' hK'
      rw [hT, Finset.mem_biUnion] at hK'
      obtain ⟨l, -, hK'⟩ := hK'
      obtain ⟨ψ, -, rfl⟩ := Finset.mem_image.1 hK'
      exact (orbFacts _ h.N ψ).2.1
    have h1 := orbSum (ZMod h.N)ˣ T hcyc
    have h2 : Nat.card (ZMod h.N)ˣ ≤ h.N := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
      exact Nat.totient_le _
    exact_mod_cast h1.trans h2
  have hc5 : (0 : ℝ) ≤ c₅ := by positivity
  have hL : 0 ≤ Real.log r₁ + Real.log r₂ := add_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  have hP : 0 ≤ ((h.N : ℝ) * ((e : ℝ) + 1)) ^ A := by positivity
  have hN16 : (16 : ℝ) ≤ h.N := by exact_mod_cast Nat.le_of_dvd hN0 h16
  have het' : (e : ℝ) + 1 ≤ t := by exact_mod_cast Nat.succ_le_of_lt het
  refine ⟨?_, ?_⟩
  · intro l hl ψ hψ
    exact (hcorK _).1 l (Finset.mem_filter.2 ⟨hl, ψ, hψ, rfl⟩) ψ ((mem_orb _).2 rfl)
  · have hstep : ∀ l ∈ Ls, Real.log ((l : ℕ) : ℝ) * ∑ ψ ∈ h.X (c l) e, Vn Ω (c l) e ψ ≤
        ∑ K' ∈ T, if (∃ ψ ∈ h.X (c l) e, (MulChar.toUnitHom ψ).ker = K') then
          Real.log ((l : ℕ) : ℝ) * ∑ ψ ∈ orb (c l) K', Vn Ω (c l) e ψ else 0 := by
      intro l hl
      have hlog : 0 ≤ Real.log ((l : ℕ) : ℝ) := Real.log_natCast_nonneg _
      rw [← Finset.sum_fiberwise_of_maps_to (hmapT l hl), Finset.mul_sum]
      refine Finset.sum_le_sum fun K' _ => ?_
      split_ifs with hex
      · apply mul_le_mul_of_nonneg_left _ hlog
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro ψ hψ
          exact (mem_orb _).2 (Finset.mem_filter.1 hψ).2
        · intro ψ _ _
          exact Vn_nonneg Ω _ e ψ
      · have hempty : (h.X (c l) e).filter (fun ψ => (MulChar.toUnitHom ψ).ker = K') = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro ψ hψ hk
          exact hex ⟨ψ, hψ, hk⟩
        rw [hempty, Finset.sum_empty, mul_zero]
    calc _ ≤ ∑ l ∈ Ls, ∑ K' ∈ T, (if (∃ ψ ∈ h.X (c l) e, (MulChar.toUnitHom ψ).ker = K') then
          Real.log ((l : ℕ) : ℝ) * ∑ ψ ∈ orb (c l) K', Vn Ω (c l) e ψ else 0) := Finset.sum_le_sum hstep
      _ = ∑ K' ∈ T, ∑ l ∈ Ls.filter (fun l => ∃ ψ ∈ h.X (c l) e, (MulChar.toUnitHom ψ).ker = K'),
          Real.log ((l : ℕ) : ℝ) * ∑ ψ ∈ orb (c l) K', Vn Ω (c l) e ψ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun K' _ => ?_
        rw [Finset.sum_filter]
      _ ≤ ∑ K' ∈ T, 2 * (c₅ : ℝ) * (K'.index.totient : ℝ) * ((h.N : ℝ) * ((e : ℝ) + 1)) ^ A *
          (Real.log r₁ + Real.log r₂) := Finset.sum_le_sum fun K' _ => (hcorK K').2
      _ = (2 * (c₅ : ℝ) * (Real.log r₁ + Real.log r₂)) * ((h.N : ℝ) * ((e : ℝ) + 1)) ^ A *
          ∑ K' ∈ T, ((K'.index.totient : ℕ) : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun K' _ => by ring
      _ ≤ (2 * (c₅ : ℝ) * (Real.log r₁ + Real.log r₂)) * ((h.N : ℝ) * ((e : ℝ) + 1)) ^ A * (h.N : ℝ) :=
        mul_le_mul_of_nonneg_left hsumT (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc5) hL) hP)
      _ = (2 * (c₅ : ℝ) * (Real.log r₁ + Real.log r₂)) * (h.N : ℝ) * ((h.N : ℝ) * ((e : ℝ) + 1)) ^ A := by ring
      _ ≤ ((h.N : ℝ) * (t : ℝ)) ^ (k + 1 + A) :=
        absorb _ _ _ _ k A hk.le hN16 (Nat.cast_nonneg e) het'
end

section
namespace UpperTheory.V.U3

theorem corGK_of (h : Inp) (ha : Aut.AutomorphyUnramifiedCoefficients) : CorGK := corGK (propGK h.number (oneChar h ha))

theorem caseI (h : Inp) (ha : Aut.AutomorphyUnramifiedCoefficients) : HV.CountI := countI (corGK_of h ha)

end UpperTheory.V.U3
end
