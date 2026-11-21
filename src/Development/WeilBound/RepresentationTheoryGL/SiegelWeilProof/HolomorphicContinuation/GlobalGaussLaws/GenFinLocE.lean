import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRedField

section
noncomputable section

set_option linter.unusedSectionVars false

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GenFinLocAH

variable {R S : Type} [CommRing R] [CommRing S] {n : ℕ}

def bf (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  M.submatrix finSumFinEquiv finSumFinEquiv

theorem bf_mul (M N : Matrix (Fin (n + n)) (Fin (n + n)) R) : bf (M * N) = bf M * bf N := by
  unfold bf; exact (Matrix.submatrix_mul_equiv M N _ _ _).symm

theorem block_matrix_to_fromBlocks (a b c d : Matrix (Fin n) (Fin n) R) : bf (GlobalTheory.StdUnn.blk4 a b c d) = fromBlocks a b c d := by
  unfold bf GlobalTheory.StdUnn.blk4; simp [Matrix.submatrix_submatrix]

theorem blkDm_eq (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : blkDm M = (bf M).toBlocks₂₂ := rfl

theorem bf_map (f : R →+* S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : bf (M.map f) = (bf M).map f := rfl

theorem bf_one : bf (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 := Matrix.submatrix_one_equiv _

theorem bf_injective : Function.Injective (bf : Matrix (Fin (n + n)) (Fin (n + n)) R → _) := by
  intro M N h
  ext i j
  have := congrFun (congrFun h (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
  simpa [bf] using this

theorem block_matrix_one : GlobalTheory.StdUnn.blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 :=
  bf_injective (by rw [block_matrix_to_fromBlocks, bf_one, fromBlocks_one])

theorem blkDm_map (f : R →+* S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : (blkDm M).map f = blkDm (M.map f) := rfl

theorem det_map (f : R →+* S) (M : Matrix (Fin n) (Fin n) R) : f M.det = (M.map f).det := by
  rw [RingHom.map_det]; rfl

theorem block_matrix_map (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (GlobalTheory.StdUnn.blk4 a b c d).map f = GlobalTheory.StdUnn.blk4 (a.map f) (b.map f) (c.map f) (d.map f) :=
  bf_injective (by rw [bf_map, block_matrix_to_fromBlocks, block_matrix_to_fromBlocks, fromBlocks_map])

theorem eI_map (f : R →+* S) (I : Finset (Fin n)) : (eI I : Matrix (Fin n) (Fin n) R).map f = eI I := by
  ext i j; simp only [eI, map_apply, diagonal_apply]; split_ifs <;> simp

theorem wIm_map (f : R →+* S) (I : Finset (Fin n)) : (wIm I : Matrix (Fin (n + n)) (Fin (n + n)) R).map f = wIm I := by
  unfold wIm; rw [block_matrix_map]; simp [Matrix.map_sub, Matrix.map_one, Matrix.map_neg, eI_map]

theorem standard_symplectic_matrix_map (f : R →+* S) : (J2 R n).map f = J2 S n := by
  unfold J2; rw [block_matrix_map]; simp [Matrix.map_one, Matrix.map_neg]

theorem cT_map (σ : R →+* R) (σ' : S →+* S) (f : R →+* S) (hf : ∀ x, f (σ x) = σ' (f x)) {m p : Type}
    (M : Matrix m p R) : (Formalism.UG.cT σ M).map f = Formalism.UG.cT σ' (M.map f) := by
  ext i j; simp [Formalism.UG.cT, hf]

theorem isUnit_of (σ : R →+* R) (𝔪 : Ideal R) (horb : ∀ 𝔫 : Ideal R, 𝔫.IsMaximal → 𝔫 = 𝔪 ∨ 𝔫 = 𝔪.comap σ)
    (z : R) (h1 : z ∉ 𝔪) (h2 : σ z ∉ 𝔪) : IsUnit z := by
  by_contra hz
  obtain ⟨𝔫, h𝔫, hz𝔫⟩ := Ideal.exists_le_maximal (Ideal.span {z}) (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hz' : z ∈ 𝔫 := hz𝔫 (Ideal.subset_span rfl)
  rcases horb 𝔫 h𝔫 with rfl | rfl
  · exact h1 hz'
  · exact h2 hz'

end PositivityTheory.Rg.Sw.Glob.GenFinLocAH
end
end

section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GenFinLocAH

variable {R S : Type} [CommRing R] [CommRing S] {n : ℕ}

theorem map_nonsing_inv (f : R →+* S) (M : Matrix (Fin n) (Fin n) R) (h : IsUnit M.det) :
    (M⁻¹).map f = (M.map f)⁻¹ := by
  obtain ⟨u, hu⟩ := h
  have h' : IsUnit (M.map f).det := by rw [← det_map, ← hu]; exact (u.isUnit.map f)
  rw [Matrix.inv_def, Matrix.inv_def, ← det_map, ← hu, Ring.inverse_unit, Matrix.map_smul' _ _ _ (fun a b => map_mul f a b)]
  have hadj : M.adjugate.map f = (M.map f).adjugate := RingHom.map_adjugate f M
  have hinv : Ring.inverse (f ↑u) = f ↑u⁻¹ := by
    rw [show f ↑u = ((Units.map f.toMonoidHom u : Sˣ) : S) from rfl, Ring.inverse_unit]; rfl
  rw [hadj, hinv]

theorem bf_cT (σ : R →+* R) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    bf (Formalism.UG.cT σ M) = Formalism.UG.cT σ (bf M) := rfl

theorem cT_fromBlocks (σ : R →+* R) (A B C D : Matrix (Fin n) (Fin n) R) :
    Formalism.UG.cT σ (fromBlocks A B C D) =
      fromBlocks (Formalism.UG.cT σ A) (Formalism.UG.cT σ C) (Formalism.UG.cT σ B) (Formalism.UG.cT σ D) := by
  unfold Formalism.UG.cT; rw [fromBlocks_map, fromBlocks_transpose]

def Uni (σ : R →+* R) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Prop := Formalism.UG.cT σ M * J2 R n * M = J2 R n

theorem Uni.mul {σ : R →+* R} {M N : Matrix (Fin (n + n)) (Fin (n + n)) R} (hM : Uni σ M) (hN : Uni σ N) :
    Uni σ (M * N) := by
  unfold Uni at *
  rw [Formalism.UG.cT_mul]
  calc Formalism.UG.cT σ N * Formalism.UG.cT σ M * J2 R n * (M * N) = Formalism.UG.cT σ N * (Formalism.UG.cT σ M * J2 R n * M) * N := by
        simp only [Matrix.mul_assoc]
    _ = J2 R n := by rw [hM, hN]

theorem caseA (hF : LocRedField) (σ : R →+* R) (hσ : ∀ a, σ (σ a) = a) (𝔪 : Ideal R) [h𝔪 : 𝔪.IsMaximal]
    (hfix : 𝔪.comap σ = 𝔪) (horb : ∀ 𝔫 : Ideal R, 𝔫.IsMaximal → 𝔫 = 𝔪 ∨ 𝔫 = 𝔪.comap σ)
    (g : Matrix (Fin (n + n)) (Fin (n + n)) R) (hg : Uni σ g) (hgu : IsUnit g.det) :
    ∃ I : Finset (Fin n), IsUnit (blkDm (g * wIm I)).det := by
  letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have hle : 𝔪 ≤ 𝔪.comap σ := hfix.symm ▸ le_refl _
  let σb : R ⧸ 𝔪 →+* R ⧸ 𝔪 := Ideal.quotientMap 𝔪 σ hle
  have hπσ : ∀ x, Ideal.Quotient.mk 𝔪 (σ x) = σb (Ideal.Quotient.mk 𝔪 x) := fun x => (Ideal.quotientMap_mk ..).symm
  have hσb : ∀ x, σb (σb x) = x := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← hπσ, ← hπσ, hσ]
  have hdet : IsUnit (g.map (Ideal.Quotient.mk 𝔪)).det := by rw [← det_map]; exact hgu.map _
  let gb : GL (Fin (n + n)) (R ⧸ 𝔪) := Matrix.nonsingInvUnit _ hdet
  have hgb : gb ∈ Formalism.UG.UJ σb (J2 (R ⧸ 𝔪) n) := by
    show Formalism.UG.cT σb (g.map (Ideal.Quotient.mk 𝔪)) * J2 (R ⧸ 𝔪) n * g.map (Ideal.Quotient.mk 𝔪) = J2 (R ⧸ 𝔪) n
    have := congrArg (fun M => M.map (Ideal.Quotient.mk 𝔪)) hg
    simp only [Matrix.map_mul, standard_symplectic_matrix_map] at this
    rwa [cT_map σ σb _ hπσ] at this
  obtain ⟨I, hI⟩ := hF (R ⧸ 𝔪) σb hσb n gb hgb
  refine ⟨I, isUnit_of σ 𝔪 horb _ ?_ ?_⟩
  · intro hm
    have h0 : Ideal.Quotient.mk 𝔪 (blkDm (g * wIm I)).det = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
    rw [det_map, blkDm_map, Matrix.map_mul, wIm_map] at h0
    exact hI.ne_zero h0
  · intro hm
    have : (blkDm (g * wIm I)).det ∈ 𝔪.comap σ := hm
    rw [hfix] at this
    have h0 : Ideal.Quotient.mk 𝔪 (blkDm (g * wIm I)).det = 0 := Ideal.Quotient.eq_zero_iff_mem.2 this
    rw [det_map, blkDm_map, Matrix.map_mul, wIm_map] at h0
    exact hI.ne_zero h0

end PositivityTheory.Rg.Sw.Glob.GenFinLocAH
end
end

section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GenFinLocAH

variable {R : Type} [CommRing R] {n : ℕ}

theorem det_cT (σ : R →+* R) (a : Matrix (Fin n) (Fin n) R) : (Formalism.UG.cT σ a).det = σ a.det := by
  unfold Formalism.UG.cT; rw [det_transpose, det_map]

theorem cT_cT (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) {m p : Type} (a : Matrix m p R) :
    Formalism.UG.cT σ (Formalism.UG.cT σ a) = a := by
  ext i j; simp [Formalism.UG.cT, hσ]

theorem cT_inv (σ : R →+* R) (a : Matrix (Fin n) (Fin n) R) (ha : IsUnit a.det) :
    Formalism.UG.cT σ a⁻¹ = (Formalism.UG.cT σ a)⁻¹ := by
  unfold Formalism.UG.cT; rw [map_nonsing_inv σ a ha, transpose_nonsing_inv]

theorem uni_levi (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) (a : Matrix (Fin n) (Fin n) R) (ha : IsUnit a.det) :
    Uni σ (GlobalTheory.StdUnn.blk4 a 0 0 (Formalism.UG.cT σ a)⁻¹) := by
  have hca : IsUnit (Formalism.UG.cT σ a).det := by rw [det_cT]; exact ha.map σ
  apply bf_injective
  unfold J2
  rw [bf_mul, bf_mul, bf_cT, block_matrix_to_fromBlocks, block_matrix_to_fromBlocks, cT_fromBlocks, fromBlocks_multiply, fromBlocks_multiply]
  rw [cT_inv σ _ hca, cT_cT σ hσ]
  have hc0 : Formalism.UG.cT σ (0 : Matrix (Fin n) (Fin n) R) = 0 := by ext; simp [Formalism.UG.cT]
  simp only [hc0, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, add_zero,
    zero_add, mul_nonsing_inv _ hca, nonsing_inv_mul _ ha, neg_zero]

theorem eI_mul_eI (I : Finset (Fin n)) : (eI I : Matrix (Fin n) (Fin n) R) * eI I = eI I := by
  unfold eI; rw [diagonal_mul_diagonal]; congr 1; funext i; split_ifs <;> simp

theorem cT_eI (σ : R →+* R) (I : Finset (Fin n)) : Formalism.UG.cT σ (eI I : Matrix (Fin n) (Fin n) R) = eI I := by
  unfold Formalism.UG.cT; rw [eI_map, eI, diagonal_transpose]

theorem uni_wIm (σ : R →+* R) (I : Finset (Fin n)) : Uni σ (wIm I : Matrix (Fin (n + n)) (Fin (n + n)) R) := by
  apply bf_injective
  unfold J2 wIm
  rw [bf_mul, bf_mul, bf_cT, block_matrix_to_fromBlocks, block_matrix_to_fromBlocks, cT_fromBlocks, fromBlocks_multiply, fromBlocks_multiply]
  have h1 : Formalism.UG.cT σ (1 - eI I : Matrix (Fin n) (Fin n) R) = 1 - eI I := by
    unfold Formalism.UG.cT; rw [Matrix.map_sub _ (map_sub σ), Matrix.map_one _ (map_zero σ) (map_one σ), eI_map, transpose_sub,
      transpose_one, eI, diagonal_transpose]
  have h2 : Formalism.UG.cT σ (-eI I : Matrix (Fin n) (Fin n) R) = -eI I := by
    unfold Formalism.UG.cT; rw [Matrix.map_neg _ (map_neg σ), eI_map, transpose_neg, eI, diagonal_transpose]
  rw [h1, h2, cT_eI]
  have hE := eI_mul_eI (R := R) I
  congr 1 <;> simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, add_zero,
    zero_add, neg_neg, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, hE] <;> abel_nf

end PositivityTheory.Rg.Sw.Glob.GenFinLocAH
end
end

section
noncomputable section

set_option linter.style.haveILetI false

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GenFinLocAH

variable {R : Type} [CommRing R] {n : ℕ}

theorem uni_blocks (σ : R →+* R) (h : Matrix (Fin (n + n)) (Fin (n + n)) R) (hu : Uni σ h) :
    Formalism.UG.cT σ (bf h).toBlocks₂₂ * (bf h).toBlocks₁₁ - Formalism.UG.cT σ (bf h).toBlocks₁₂ * (bf h).toBlocks₂₁ = 1 ∧
      Formalism.UG.cT σ (bf h).toBlocks₂₂ * (bf h).toBlocks₁₂ = Formalism.UG.cT σ (bf h).toBlocks₁₂ * (bf h).toBlocks₂₂ := by
  have e := congrArg bf hu
  unfold J2 at e
  rw [bf_mul, bf_mul, bf_cT, block_matrix_to_fromBlocks, ← fromBlocks_toBlocks (bf h), cT_fromBlocks, fromBlocks_multiply,
    fromBlocks_multiply] at e
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add] at e
  obtain ⟨-, -, e3, e4⟩ := fromBlocks_inj.1 e
  refine ⟨?_, ?_⟩
  · have : -(Formalism.UG.cT σ (bf h).toBlocks₂₂ * (bf h).toBlocks₁₁) + Formalism.UG.cT σ (bf h).toBlocks₁₂ * (bf h).toBlocks₂₁ = -1 := e3
    rw [← neg_neg (1 : Matrix (Fin n) (Fin n) R), ← this]; abel
  · have : -(Formalism.UG.cT σ (bf h).toBlocks₂₂ * (bf h).toBlocks₁₂) + Formalism.UG.cT σ (bf h).toBlocks₁₂ * (bf h).toBlocks₂₂ = 0 := e4
    rw [neg_add_eq_zero] at this; exact this

theorem schur {K : Type} [CommRing K] (P Q A B C D : Matrix (Fin n) (Fin n) K) (h1 : P * A - Q * C = 1) (h2 : P * B = Q * D)
    (hD : IsUnit D.det) : IsUnit P.det := by
  have hQ : Q = P * B * D⁻¹ := by rw [h2, Matrix.mul_assoc, mul_nonsing_inv _ hD, Matrix.mul_one]
  have : P * (A - B * D⁻¹ * C) = 1 := by
    rw [← h1, hQ]; simp only [Matrix.mul_sub, Matrix.mul_assoc]
  have hd := congrArg Matrix.det this
  rw [det_mul, det_one] at hd
  exact ⟨⟨_, _, hd, by rw [mul_comm]; exact hd⟩, rfl⟩

theorem lift2 (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) (𝔪 : Ideal R) [h𝔪 : 𝔪.IsMaximal] (hne : 𝔪.comap σ ≠ 𝔪)
    (s t : R ⧸ 𝔪) : ∃ x : R, Ideal.Quotient.mk 𝔪 x = s ∧ Ideal.Quotient.mk 𝔪 (σ x) = t := by
  have hsurj : Function.Surjective σ := fun y => ⟨σ y, hσ y⟩
  have h' : (𝔪.comap σ).IsMaximal := Ideal.comap_isMaximal_of_surjective σ hsurj
  have hsup : 𝔪 ⊔ 𝔪.comap σ = ⊤ := Ideal.IsMaximal.coprime_of_ne h𝔪 h' (Ne.symm hne)
  have h1 : (1 : R) ∈ 𝔪 ⊔ 𝔪.comap σ := hsup ▸ Submodule.mem_top
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.1 h1
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective t
  have hf' : σ f ∈ 𝔪 := hf
  have he0 : Ideal.Quotient.mk 𝔪 e = 0 := Ideal.Quotient.eq_zero_iff_mem.2 he
  have hf1 : Ideal.Quotient.mk 𝔪 f = 1 := by
    rw [show f = 1 - e by rw [← hef]; ring, map_sub, map_one, he0, sub_zero]
  have hsf : Ideal.Quotient.mk 𝔪 (σ f) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hf'
  have hse : Ideal.Quotient.mk 𝔪 (σ e) = 1 := by
    rw [show e = 1 - f by rw [← hef]; ring, map_sub, map_one, map_sub, map_one, hsf, sub_zero]
  refine ⟨u * f + σ y * e, ?_, ?_⟩
  · rw [map_add, map_mul, map_mul, hf1, he0]; ring
  · rw [map_add, map_mul, map_mul, map_add, map_mul, map_mul, hσ, hsf, hse]; ring

theorem caseB (hS : LocRedSplit) (σ : R →+* R) (hσ : ∀ a, σ (σ a) = a) (𝔪 : Ideal R) [h𝔪 : 𝔪.IsMaximal]
    (hne : 𝔪.comap σ ≠ 𝔪) (horb : ∀ 𝔫 : Ideal R, 𝔫.IsMaximal → 𝔫 = 𝔪 ∨ 𝔫 = 𝔪.comap σ)
    (g : Matrix (Fin (n + n)) (Fin (n + n)) R) (hg : Uni σ g) (hgu : IsUnit g.det) :
    ∃ (a : Matrix (Fin n) (Fin n) R) (I : Finset (Fin n)), IsUnit a.det ∧
      IsUnit (blkDm (g * GlobalTheory.StdUnn.blk4 a 0 0 (Formalism.UG.cT σ a)⁻¹ * wIm I)).det := by
  letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have hdet : IsUnit (g.map (Ideal.Quotient.mk 𝔪)).det := by rw [← det_map]; exact hgu.map _
  obtain ⟨ab, db, I, hI⟩ := hS (R ⧸ 𝔪) n (Matrix.nonsingInvUnit _ hdet)
  choose x hx using fun i j => lift2 σ hσ 𝔪 hne ((ab : Matrix (Fin n) (Fin n) (R ⧸ 𝔪)) i j)
    (((db⁻¹ : GL (Fin n) (R ⧸ 𝔪)) : Matrix (Fin n) (Fin n) (R ⧸ 𝔪)) j i)
  let a : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => x i j
  have ha1 : a.map (Ideal.Quotient.mk 𝔪) = ab := by ext i j; exact (hx i j).1
  have ha2 : (Formalism.UG.cT σ a).map (Ideal.Quotient.mk 𝔪) = ((db⁻¹ : GL (Fin n) (R ⧸ 𝔪)) : Matrix (Fin n) (Fin n) (R ⧸ 𝔪)) := by
    ext i j; exact (hx j i).2
  have hab : IsUnit (ab : Matrix (Fin n) (Fin n) (R ⧸ 𝔪)).det := Matrix.isUnits_det_units ab
  have hdb : IsUnit ((db⁻¹ : GL (Fin n) (R ⧸ 𝔪)) : Matrix (Fin n) (Fin n) (R ⧸ 𝔪)).det := Matrix.isUnits_det_units _
  have hadet : IsUnit a.det := by
    refine isUnit_of σ 𝔪 horb _ ?_ ?_
    · intro hm
      have h0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
      rw [det_map, ha1] at h0
      exact hab.ne_zero h0
    · intro hm
      have h0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
      rw [← det_cT, det_map, ha2] at h0
      exact hdb.ne_zero h0
  have hca : IsUnit (Formalism.UG.cT σ a).det := by rw [det_cT]; exact hadet.map σ
  have hinv : ((Formalism.UG.cT σ a)⁻¹).map (Ideal.Quotient.mk 𝔪) = (db : Matrix (Fin n) (Fin n) (R ⧸ 𝔪)) := by
    rw [map_nonsing_inv _ _ hca, ha2, Matrix.coe_units_inv, Matrix.nonsing_inv_nonsing_inv _ (Matrix.isUnits_det_units db)]
  set h := g * GlobalTheory.StdUnn.blk4 a 0 0 (Formalism.UG.cT σ a)⁻¹ * wIm I with hh
  have hmap : h.map (Ideal.Quotient.mk 𝔪) =
      g.map (Ideal.Quotient.mk 𝔪) * GlobalTheory.StdUnn.blk4 (ab : Matrix (Fin n) (Fin n) (R ⧸ 𝔪)) 0 0 db * wIm I := by
    rw [hh, Matrix.map_mul, Matrix.map_mul, block_matrix_map, ha1, hinv, wIm_map, Matrix.map_zero _ (map_zero _)]
  have hδ : IsUnit ((blkDm h).map (Ideal.Quotient.mk 𝔪)).det := by rw [blkDm_map, hmap]; exact hI
  refine ⟨a, I, hadet, isUnit_of σ 𝔪 horb _ ?_ ?_⟩
  · intro hm
    have h0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
    rw [det_map] at h0
    exact hδ.ne_zero h0
  · have hu : Uni σ h := (hg.mul (uni_levi σ hσ a hadet)).mul (uni_wIm σ I)
    obtain ⟨e1, e2⟩ := uni_blocks σ h hu
    have hπσ : ∀ y : Matrix (Fin n) (Fin n) R, (Formalism.UG.cT σ y).map (Ideal.Quotient.mk 𝔪) =
        (Formalism.UG.cT σ y).map (Ideal.Quotient.mk 𝔪) := fun _ => rfl
    have e1' := congrArg (fun M => M.map (Ideal.Quotient.mk 𝔪)) e1
    have e2' := congrArg (fun M => M.map (Ideal.Quotient.mk 𝔪)) e2
    simp only [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at e1' e2'
    have hD : IsUnit ((bf h).toBlocks₂₂.map (Ideal.Quotient.mk 𝔪)).det := hδ
    have hP := schur _ _ _ _ _ _ e1' e2' hD
    intro hm
    have h0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
    rw [blkDm_eq, ← det_cT, det_map] at h0
    exact hP.ne_zero h0

end PositivityTheory.Rg.Sw.Glob.GenFinLocAH
end
end

section
noncomputable section

set_option linter.unusedSectionVars false

open scoped TensorProduct
open IsDedekindDomain NumberField GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace PositivityTheory.Rg.Sw.Glob.GenFinLocAH

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def sigI (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) : intLoc F E v →+* intLoc F E v :=
  (sigR (Fv F v) σ).restrict (intLoc F E v) (intLoc F E v) (fun _ hx => sigR_mem_intLoc σ hx)

theorem sigI_coe (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (z : intLoc F E v) :
    ((sigI σ v z : intLoc F E v) : Fv F v ⊗[F] E) = sigR (Fv F v) σ z := rfl

theorem sigR_sigR (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (R : Type) [CommRing R] [Algebra F R] (z : R ⊗[F] E) :
    sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR, hσ]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem sigI_sigI (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (v : HeightOneSpectrum (𝓞 F)) (z : intLoc F E v) :
    sigI σ v (sigI σ v z) = z := Subtype.ext (sigR_sigR σ hσ (Fv F v) (z : Fv F v ⊗[F] E))

theorem fixed_eq_tmul (σ : E →ₐ[F] E) (hfix : ∀ x, σ x = x ↔ x ∈ (algebraMap F E).range) (v : HeightOneSpectrum (𝓞 F))
    (z : Fv F v ⊗[F] E) (hz : sigR (Fv F v) σ z = z) : ∃ a : Fv F v, z = a ⊗ₜ[F] (1 : E) := by
  let φ : E →ₗ[F] E := σ.toLinearMap - LinearMap.id
  have hex : Function.Exact (Algebra.linearMap F E) φ := by
    intro y
    constructor
    · intro hy
      have : σ y = y := by have := hy; simp only [φ, LinearMap.sub_apply, AlgHom.toLinearMap_apply, LinearMap.id_apply,
        sub_eq_zero] at this; exact this
      obtain ⟨c, hc⟩ := (hfix y).1 this
      exact ⟨c, hc⟩
    · rintro ⟨c, rfl⟩
      simp [φ]
  have hex' := Module.Flat.lTensor_exact (Fv F v) hex
  have hφ : φ.lTensor (Fv F v) z = 0 := by
    have key : ∀ w : Fv F v ⊗[F] E, φ.lTensor (Fv F v) w = sigR (Fv F v) σ w - w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul a x => simp [φ, sigR, TensorProduct.tmul_sub]
      | add y w hy hw => rw [map_add, hy, hw, map_add]; abel
    rw [key, hz, sub_self]
  obtain ⟨w, hw⟩ := (hex' z).1 hφ
  refine ⟨TensorProduct.rid F (Fv F v) w, ?_⟩
  rw [← hw]
  clear hw
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
    simp only [LinearMap.lTensor_tmul, Algebra.linearMap_apply, TensorProduct.rid_tmul]
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add y w hy hw => rw [map_add, hy, hw, map_add, TensorProduct.add_tmul]

theorem mem_of_tmul_mem (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (h : a ⊗ₜ[F] (1 : E) ∈ intLoc F E v) :
    a ∈ v.adicCompletionIntegers F := by
  have h1 := absFin_le_one_of_mem_intLoc h
  rw [absFin_tmul_one] at h1
  exact (Valued.toNormedField.norm_le_one_iff).1 (by exact_mod_cast h1)

theorem tmul_one_mem (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (h : a ∈ v.adicCompletionIntegers F) :
    a ⊗ₜ[F] (1 : E) ∈ intLoc F E v := by
  simpa using tmul_mem_intLoc (E := E) h (1 : 𝓞 E)

theorem nontrivial_intLoc (v : HeightOneSpectrum (𝓞 F)) : Nontrivial (intLoc F E v) := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have h' : ((0 : intLoc F E v) : Fv F v ⊗[F] E) = ((1 : intLoc F E v) : Fv F v ⊗[F] E) := congrArg Subtype.val h
  have := congrArg (absFin F v) h'
  rw [ZeroMemClass.coe_zero, OneMemClass.coe_one, absFin_zero, absFin_one] at this
  exact zero_ne_one this

theorem orbit_abs {R : Type} [CommRing R] (s : R →+* R) (hss : ∀ z, s (s z) = z)
    (hloc : ∀ z, s z = z → IsUnit z ∨ IsUnit (1 - z)) (𝔪 𝔫 : Ideal R) (h𝔪 : 𝔪.IsMaximal) (h𝔫 : 𝔫.IsMaximal) :
    𝔫 = 𝔪 ∨ 𝔫 = 𝔪.comap s := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hn1, hn2⟩ := hne
  have hsurj : Function.Surjective s := fun y => ⟨s y, hss y⟩
  have hcc : ∀ I : Ideal R, (I.comap s).comap s = I := by
    intro I; ext z; rw [Ideal.mem_comap, Ideal.mem_comap, hss]
  have hm' : (𝔪.comap s).IsMaximal := Ideal.comap_isMaximal_of_surjective s hsurj
  have hn' : (𝔫.comap s).IsMaximal := Ideal.comap_isMaximal_of_surjective s hsurj
  have hn3 : 𝔫.comap s ≠ 𝔪 := by
    intro h; apply hn2; rw [← h, hcc]
  have hn4 : 𝔫.comap s ≠ 𝔪.comap s := by
    intro h; apply hn1; rw [← hcc 𝔫, h, hcc]
  have c1 : 𝔪 ⊔ 𝔫 = ⊤ := Ideal.IsMaximal.coprime_of_ne h𝔪 h𝔫 (Ne.symm hn1)
  have c2 : 𝔪 ⊔ 𝔫.comap s = ⊤ := Ideal.IsMaximal.coprime_of_ne h𝔪 hn' (Ne.symm hn3)
  have c3 : 𝔪.comap s ⊔ 𝔫 = ⊤ := Ideal.IsMaximal.coprime_of_ne hm' h𝔫 (Ne.symm hn2)
  have c4 : 𝔪.comap s ⊔ 𝔫.comap s = ⊤ := Ideal.IsMaximal.coprime_of_ne hm' hn' (Ne.symm hn4)
  have d1 : 𝔪 ⊔ 𝔫 * 𝔫.comap s = ⊤ := (Ideal.sup_mul_eq_of_coprime_left c1).trans c2
  have d2 : 𝔪.comap s ⊔ 𝔫 * 𝔫.comap s = ⊤ := (Ideal.sup_mul_eq_of_coprime_left c3).trans c4
  have e1 : 𝔫 * 𝔫.comap s ⊔ 𝔪 = ⊤ := by rw [sup_comm]; exact d1
  have e2 : 𝔫 * 𝔫.comap s ⊔ 𝔪.comap s = ⊤ := by rw [sup_comm]; exact d2
  have d3 : 𝔫 * 𝔫.comap s ⊔ 𝔪 * 𝔪.comap s = ⊤ := (Ideal.sup_mul_eq_of_coprime_left e1).trans e2
  have h1 : (1 : R) ∈ 𝔫 * 𝔫.comap s ⊔ 𝔪 * 𝔪.comap s := by rw [d3]; exact Submodule.mem_top
  obtain ⟨y, hy, x, hx, hxy⟩ := Submodule.mem_sup.1 h1
  have hxm : x ∈ 𝔪 := (Ideal.mul_le_left : 𝔪 * 𝔪.comap s ≤ 𝔪) hx
  have hyn : y ∈ 𝔫 := (Ideal.mul_le_left : 𝔫 * 𝔫.comap s ≤ 𝔫) hy
  have hyn'' : y ∈ 𝔫.comap s := (Ideal.mul_le_right : 𝔫 * 𝔫.comap s ≤ 𝔫.comap s) hy
  have hyn' : s y ∈ 𝔫 := Ideal.mem_comap.1 hyn''
  have hzm : x * s x ∈ 𝔪 := Ideal.mul_mem_right _ _ hxm
  have hfz : s (x * s x) = x * s x := by rw [map_mul, hss, mul_comm]
  have h1z : 1 - x * s x ∈ 𝔫 := by
    have hx' : x = 1 - y := by rw [← hxy]; ring
    have e : 1 - x * s x = y + s y - y * s y := by rw [hx', map_sub, map_one]; ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.add_mem _ hyn hyn') (Ideal.mul_mem_right _ _ hyn)
  rcases hloc _ hfz with hu | hu
  · exact h𝔪.ne_top (Ideal.eq_top_of_isUnit_mem _ hzm hu)
  · exact h𝔫.ne_top (Ideal.eq_top_of_isUnit_mem _ h1z hu)

theorem isUnit_tmul (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletionIntegers F)ˣ) :
    IsUnit (⟨((u : v.adicCompletionIntegers F) : Fv F v) ⊗ₜ[F] (1 : E), tmul_one_mem v _ (u : v.adicCompletionIntegers F).2⟩ :
      intLoc F E v) := by
  refine ⟨⟨_, ⟨((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) ⊗ₜ[F] (1 : E),
    tmul_one_mem v _ (u⁻¹ : (v.adicCompletionIntegers F)ˣ).1.2⟩, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
  · show ((u : v.adicCompletionIntegers F) : Fv F v) ⊗ₜ[F] (1 : E) * (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) :
      v.adicCompletionIntegers F) : Fv F v) ⊗ₜ[F] (1 : E) = 1
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← Subring.coe_mul, Units.mul_inv]; rfl
  · show (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : Fv F v) ⊗ₜ[F] (1 : E) *
      ((u : v.adicCompletionIntegers F) : Fv F v) ⊗ₜ[F] (1 : E) = 1
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← Subring.coe_mul, Units.inv_mul]; rfl

theorem fixed_local (σ : E →ₐ[F] E) (hfix : ∀ x, σ x = x ↔ x ∈ (algebraMap F E).range) (v : HeightOneSpectrum (𝓞 F))
    (z : intLoc F E v) (hz : sigI σ v z = z) : IsUnit z ∨ IsUnit (1 - z) := by
  obtain ⟨a, ha⟩ := fixed_eq_tmul σ hfix v (z : Fv F v ⊗[F] E) (by rw [← sigI_coe]; exact congrArg Subtype.val hz)
  have haO : a ∈ v.adicCompletionIntegers F := mem_of_tmul_mem v a (ha ▸ z.2)
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (⟨a, haO⟩ : v.adicCompletionIntegers F) with hu | hu
  · left
    obtain ⟨u, hu⟩ := hu
    have e : z = ⟨((u : v.adicCompletionIntegers F) : Fv F v) ⊗ₜ[F] (1 : E), tmul_one_mem v _ (u : v.adicCompletionIntegers F).2⟩ :=
      Subtype.ext (by rw [ha, hu])
    rw [e]; exact isUnit_tmul v u
  · right
    obtain ⟨u, hu⟩ := hu
    have e : 1 - z = ⟨((u : v.adicCompletionIntegers F) : Fv F v) ⊗ₜ[F] (1 : E), tmul_one_mem v _ (u : v.adicCompletionIntegers F).2⟩ := by
      apply Subtype.ext
      rw [hu]
      show (1 : Fv F v ⊗[F] E) - (z : Fv F v ⊗[F] E) = (1 - a) ⊗ₜ[F] (1 : E)
      rw [ha, TensorProduct.sub_tmul, Algebra.TensorProduct.one_def]
    rw [e]; exact isUnit_tmul v u

theorem orbit (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ (algebraMap F E).range)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ 𝔪 : Ideal (intLoc F E v), 𝔪.IsMaximal ∧ ∀ 𝔫 : Ideal (intLoc F E v), 𝔫.IsMaximal → 𝔫 = 𝔪 ∨ 𝔫 = 𝔪.comap (sigI σ v) := by
  have := nontrivial_intLoc (E := E) v
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal (intLoc F E v)
  exact ⟨𝔪, h𝔪, fun 𝔫 h𝔫 => orbit_abs (sigI σ v) (sigI_sigI σ hσ v) (fixed_local σ hfix v) 𝔪 𝔫 h𝔪 h𝔫⟩

end PositivityTheory.Rg.Sw.Glob.GenFinLocAH
end
end
