import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.LdExOfLeaves
import Development.WeilBound.ThetaLifts.LatticeBasics.FrameA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroConjNegOfCmExtensionStatement

section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald.YFA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sig_sig' (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])

variable (F) in

def spcOf {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Spc F E n := ⟨J, ⊤, fun _ => 1, fun _ => 1⟩

theorem toCols₁_wit {n : ℕ} (T : GL (Fin n) E) (a : E) :
    ∃ t : GL (Fin n) E, (GlobalTheory.ThK.Dbl.Frame.two 1 * GlobalTheory.ThK.Dbl.Frame.wit a T).1.toCols₁ = diagCols (Fin n) * t.1 := by
  have hd := GlobalTheory.ThK.Dbl.Frame.frame_diag (1 : GL (Fin n) E) T a
  refine ⟨1, ?_⟩
  ext i j
  have := congrFun (congrFun hd i) j
  rw [Matrix.mul_apply, Fintype.sum_sum_type] at this
  simp only [Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at this
  simpa [Matrix.toCols₁] using this

omit [NumberField F] [NumberField E] in
theorem dbl_sym {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {e₀ : E} (hJ : ∀ i j, σ (J j i) = e₀ * J i j) :
    ((dbl J).map (σ : E →+* E))ᵀ = e₀ • dbl J := by
  ext (i | i) (j | j) <;> simp [dbl, Matrix.fromBlocks, hJ]

theorem eps_eq {n : ℕ} (hn : 1 ≤ n) (hc : ∀ z : E, σ (σ z) = z) {J : Matrix (Fin n) (Fin n) E} {e₀ : E}
    (hJ : ∀ i j, σ (J j i) = e₀ * J i j) {b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E} {e : E}
    (hb : bᵀ * dbl J * b.map σ = Matrix.fromBlocks 0 1 (e • 1) 0) (he : σ e = e) : e = e₀ := by
  have h := GlobalTheory.ThK.Dbl.Frame.gram_sym (σ : E →+* E) hc (dbl_sym hJ) b
  have hb' : bᵀ * dbl J * b.map (σ : E →+* E) = Matrix.fromBlocks 0 1 (e • 1) 0 := hb
  rw [hb'] at h
  have := congrFun (congrFun h (Sum.inl ⟨0, hn⟩)) (Sum.inr ⟨0, hn⟩)
  simpa [Matrix.fromBlocks, he] using this

end PositivityTheory.SiegelWeilFormula.Ald.YFA

end
end

section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

open PositivityTheory.SiegelWeilFormula.Ald.YFA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

omit [NumberField F] in

theorem frame_of {n : ℕ} (hc : ∀ z : E, σ (σ z) = z) {J : Matrix (Fin n) (Fin n) E} {e₀ : E} (he : e₀ * e₀ = 1)
    (hJ : ∀ i j, σ (J j i) = e₀ * J i j) (T : GL (Fin n) E) (hT : J * T.1.map σ = 1) :
    ∃ b : GL (Fin n ⊕ Fin n) E, b.1ᵀ * dbl J * b.1.map σ = Matrix.fromBlocks 0 1 (e₀ • 1) 0 ∧
      ∃ t : GL (Fin n) E, b.1.toCols₁ = diagCols (Fin n) * t.1 := by
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  have ha : (2 : E)⁻¹ + (σ : E →+* E) (2 : E)⁻¹ = 1 := by
    rw [map_inv₀, map_ofNat, ← two_mul, mul_inv_cancel₀ h2]
  have hJ' : (J.map (σ : E →+* E))ᵀ = e₀ • J := by
    ext i j
    simpa using hJ i j
  have hT' : (1 : GL (Fin n) E).1ᵀ * J * (1 : GL (Fin n) E).1.map (σ : E →+* E) * T.1.map (σ : E →+* E) = 1 := by
    have : (1 : Matrix (Fin n) (Fin n) E).map (σ : E →+* E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
    simpa [this] using hT
  refine ⟨GlobalTheory.ThK.Dbl.Frame.two 1 * GlobalTheory.ThK.Dbl.Frame.wit (2 : E)⁻¹ T,
    GlobalTheory.ThK.Dbl.Frame.frame_gram (σ : E →+* E) hc he ha hJ' 1 T hT', toCols₁_wit T _⟩

theorem yFrame : YFrame := by
  intro F E _ _ _ _ _ σ d n hN hn
  have hc : ∀ z : E, σ (σ z) = z := sig_sig' d.ok.good.cm
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have hεσ : σ (((ε : ℤ) : E)) = ((ε : ℤ) : E) := map_intCast σ _
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
  · obtain ⟨ξ, hξ, hσξ⟩ := GlobalTheory.T.exists_ne_zero_conj_neg_of_cmExtension F E σ d.B d.ok.good
    have hξ' : -ξ ≠ 0 := neg_ne_zero.2 hξ
    let J : Matrix (Fin n) (Fin n) E := ξ • 1
    have hJ : ∀ i j, σ (J j i) = (-1) * J i j := fun i j => by
      by_cases h : i = j
      · subst h; simp [J, hσξ]
      · simp [J, Matrix.one_apply, h, Ne.symm h]
    let T : GL (Fin n) E := ⟨(-ξ)⁻¹ • 1, (-ξ) • 1,
      by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hξ', one_smul],
      by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hξ', one_smul]⟩
    have hm : T.1.map σ = ξ⁻¹ • 1 := by
      ext i j
      by_cases h : i = j
      · subst h; simp [T, map_inv₀, hσξ]
      · simp [T, Matrix.one_apply, h]
    have hT : J * T.1.map σ = 1 := by
      rw [hm, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hξ, one_smul]
    obtain ⟨b, hb, hd⟩ := frame_of hc (by norm_num) hJ T hT
    have hεv : ((ε : ℤ) : E) = -1 :=
      eps_eq (by omega) hc (fun i j => by rw [hY]; ring) hε hεσ
    refine ⟨spcOf F J, b, ε, Or.inl ⟨hA, fun i j => (by simpa using hJ i j : σ (J j i) = -J i j)⟩, ⟨⟨ε, ?_⟩, hd⟩, hε, ?_⟩ <;>
      · change b.1ᵀ * dbl J * b.1.map σ = _
        try simp only [jeps]
        rw [hεv]; exact hb
  · let J : Matrix (Fin n) (Fin n) E := 1
    have hJ : ∀ i j, σ (J j i) = 1 * J i j := fun i j => by
      by_cases h : i = j
      · subst h; simp [J]
      · simp [J, Matrix.one_apply, h, Ne.symm h]
    have hT : J * (1 : GL (Fin n) E).1.map σ = 1 := by
      simp [J, Matrix.map_one _ (map_zero σ) (map_one σ)]
    obtain ⟨b, hb, hd⟩ := frame_of hc (by norm_num) hJ 1 hT
    have hεv : ((ε : ℤ) : E) = 1 :=
      eps_eq (by omega) hc (fun i j => by rw [hY]; ring) hε hεσ
    refine ⟨spcOf F J, b, ε, Or.inr ⟨hA, fun i j => (by simpa using hJ i j : σ (J j i) = J i j)⟩, ⟨⟨ε, ?_⟩, hd⟩, hε, ?_⟩ <;>
      · change b.1ᵀ * dbl J * b.1.map σ = _
        try simp only [jeps]
        rw [hεv]; exact hb

end PositivityTheory.SiegelWeilFormula.Ald

end
end
