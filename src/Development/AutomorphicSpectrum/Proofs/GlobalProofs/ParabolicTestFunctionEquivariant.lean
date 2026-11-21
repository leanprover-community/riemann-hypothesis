import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BlockMatrixMulBlocks
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldUniformizerNormProperties
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemIntegralGLIffIntegralUnitDetStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldUniformizerNormPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldTopologyNormBallsStatement
import BuildAid.ForwardExisting

section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.Par

section Alg

variable {F : Type} [Field F]

def piIdeal (O : Subring F) (ϖ : F) : Ideal O where
  carrier := {x | ∃ o ∈ O, (x : F) = ϖ * o}
  add_mem' := by
    rintro a b ⟨x, hx, hax⟩ ⟨y, hy, hby⟩
    exact ⟨x + y, O.add_mem hx hy, by simp [hax, hby, mul_add]⟩
  zero_mem' := ⟨0, O.zero_mem, by simp⟩
  smul_mem' := by
    rintro c a ⟨x, hx, hax⟩
    refine ⟨c * x, O.mul_mem c.2 hx, ?_⟩
    simp only [smul_eq_mul, Subring.coe_mul, hax]
    ring

def liftO {n : ℕ} (O : Subring F) (Z : Matrix (Fin n) (Fin n) F) (h : IsInt O Z) :
    Matrix (Fin n) (Fin n) O := fun i j => ⟨Z i j, h i j⟩

theorem liftO_mul {n : ℕ} (O : Subring F) {x y : Matrix (Fin n) (Fin n) F} (hx : IsInt O x)
    (hy : IsInt O y) (hxy : IsInt O (x * y)) :
    liftO O (x * y) hxy = liftO O x hx * liftO O y hy := by
  ext i j
  simp [liftO, Matrix.mul_apply]

theorem liftO_one {n : ℕ} (O : Subring F) (h : IsInt O (1 : Matrix (Fin n) (Fin n) F)) :
    liftO O 1 h = 1 := by
  ext i j
  by_cases hij : i = j <;> simp [liftO, hij, Matrix.one_apply]

def red {n : ℕ} (O : Subring F) (ϖ : F) (Z : Matrix (Fin n) (Fin n) F) (h : IsInt O Z) :
    Matrix (Fin n) (Fin n) (O ⧸ piIdeal O ϖ) :=
  (liftO O Z h).map (Ideal.Quotient.mk (piIdeal O ϖ))

theorem red_mul {n : ℕ} (O : Subring F) (ϖ : F) {x y : Matrix (Fin n) (Fin n) F} (hx : IsInt O x)
    (hy : IsInt O y) (hxy : IsInt O (x * y)) :
    red O ϖ (x * y) hxy = red O ϖ x hx * red O ϖ y hy := by
  rw [red, liftO_mul O hx hy hxy, Matrix.map_mul]
  rfl

theorem red_one {n : ℕ} (O : Subring F) (ϖ : F) (h : IsInt O (1 : Matrix (Fin n) (Fin n) F)) :
    red O ϖ 1 h = 1 := by
  rw [red, liftO_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem red_congr {n : ℕ} (O : Subring F) (ϖ : F) {x y : Matrix (Fin n) (Fin n) F} (e : x = y)
    (hx : IsInt O x) (hy : IsInt O y) : red O ϖ x hx = red O ϖ y hy := by
  subst e
  rfl

def blk (r c : ℕ) (i : Fin (r + c)) : ℕ := if (i : ℕ) < r then 0 else 1

theorem bDA_iff {r c : ℕ} (O : Subring F) (ϖ : F) {Z : Matrix (Fin (r + c)) (Fin (r + c)) F}
    (h : IsInt O Z) : bDA Z ∈ IIset O ϖ ↔ (red O ϖ Z h).BlockTriangular (blk r c) := by
  constructor
  · intro hZ i j hij
    have hji : (j : ℕ) < r ∧ r ≤ (i : ℕ) := by
      unfold blk at hij
      split_ifs at hij <;> omega
    obtain ⟨hj, hi'⟩ := hji
    obtain ⟨i', rfl⟩ : ∃ i' : Fin c, i = Fin.natAdd r i' :=
      ⟨⟨(i : ℕ) - r, by omega⟩, by ext; simp; omega⟩
    obtain ⟨j', rfl⟩ : ∃ j' : Fin r, j = Fin.castAdd c j' := ⟨⟨j, hj⟩, by ext; simp⟩
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hZ i' j')
  · intro hZ i j
    have hlt : blk r c (Fin.castAdd c j) < blk r c (Fin.natAdd r i) := by
      simp [blk]
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hZ hlt)

theorem parJ_mul {O : Subring F} {ϖ : F} {r c : ℕ} {k k' : GL (Fin (r + c)) F}
    (hk : k ∈ parJ O ϖ r c) (hk' : k' ∈ parJ O ϖ r c) : k * k' ∈ parJ O ϖ r c := by
  have hm : k * k' ∈ GLint O (r + c) := mul_mem hk.1 hk'.1
  refine ⟨hm, ?_⟩
  rw [bDA_iff O ϖ hm.1]
  rw [red_congr O ϖ (Units.val_mul k k') hm.1 (isInt_mul' O hk.1.1 hk'.1.1),
    red_mul O ϖ hk.1.1 hk'.1.1]
  exact ((bDA_iff O ϖ hk.1.1).mp hk.2).mul ((bDA_iff O ϖ hk'.1.1).mp hk'.2)

theorem parJ_inv {O : Subring F} {ϖ : F} {r c : ℕ} {k : GL (Fin (r + c)) F}
    (hk : k ∈ parJ O ϖ r c) : k⁻¹ ∈ parJ O ϖ r c := by
  have hm : k⁻¹ ∈ GLint O (r + c) := inv_mem hk.1
  refine ⟨hm, ?_⟩
  rw [bDA_iff O ϖ hm.1]
  have h1 : IsInt O ((k : Matrix (Fin (r + c)) (Fin (r + c)) F) *
      ((k⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F)) :=
    isInt_mul' O hk.1.1 hm.1
  have e1 : (k : Matrix (Fin (r + c)) (Fin (r + c)) F) *
      ((k⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hN : red O ϖ (k : Matrix (Fin (r + c)) (Fin (r + c)) F) hk.1.1 * red O ϖ _ hm.1 = 1 := by
    rw [← red_mul O ϖ hk.1.1 hm.1 h1, red_congr O ϖ e1 h1 (e1 ▸ h1)]
    exact red_one O ϖ _
  have hinv : (red O ϖ (k : Matrix (Fin (r + c)) (Fin (r + c)) F) hk.1.1)⁻¹ = red O ϖ _ hm.1 :=
    Matrix.inv_eq_right_inv hN
  letI : Invertible (red O ϖ (k : Matrix (Fin (r + c)) (Fin (r + c)) F) hk.1.1) :=
    ⟨_, mul_eq_one_comm.mp hN, hN⟩
  rw [← hinv]
  exact Matrix.blockTriangular_inv_of_blockTriangular ((bDA_iff O ϖ hk.1.1).mp hk.2)

theorem one_mem_parJ {O : Subring F} {ϖ : F} {r c : ℕ} : (1 : GL (Fin (r + c)) F) ∈ parJ O ϖ r c := by
  refine ⟨one_mem _, fun i j => ⟨0, O.zero_mem, ?_⟩⟩
  have : Fin.natAdd r i ≠ Fin.castAdd c j := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  simp [bDA, Matrix.one_apply, this]

def parSub (O : Subring F) (ϖ : F) (r c : ℕ) : Subgroup (GL (Fin (r + c)) F) where
  carrier := parJ O ϖ r c
  mul_mem' := parJ_mul
  one_mem' := one_mem_parJ
  inv_mem' := parJ_inv

end Alg

section Top

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

theorem isOpen_O (h : LF O ϖ nrm q) : IsOpen (O : Set F) := by
  rw [h.O_eq]
  exact Valuation.isOpen_integer

theorem isCompact_O (h : LF O ϖ nrm q) : IsCompact (O : Set F) := by
  rw [h.O_eq]
  exact isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace 𝒪[F]))

theorem isOpen_GLint (h : LF O ϖ nrm q) (n : ℕ) : IsOpen (GLint O n : Set (GL (Fin n) F)) := by
  have hv : ∀ a b : Fin n, Continuous fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F) a b :=
    fun a b => Units.continuous_val.matrix_elem a b
  have hw : ∀ a b : Fin n, Continuous fun g : GL (Fin n) F =>
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a b :=
    fun a b => (hv a b).comp continuous_inv
  have e : (GLint O n : Set (GL (Fin n) F)) =
      (⋂ a, ⋂ b, (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F) a b) ⁻¹' (O : Set F)) ∩
      (⋂ a, ⋂ b, (fun g : GL (Fin n) F =>
        ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a b) ⁻¹' (O : Set F)) := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    rfl
  rw [e]
  exact (isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b =>
      (isOpen_O h).preimage (hv a b)).inter
    (isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b =>
      (isOpen_O h).preimage (hw a b))

theorem isCompact_int (h : LF O ϖ nrm q) (n : ℕ) :
    IsCompact {m : Matrix (Fin n) (Fin n) F | IsInt O m} := by
  have e : {m : Matrix (Fin n) (Fin n) F | IsInt O m} =
      Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin n => (O : Set F))) := by
    ext m
    exact ⟨fun hm a _ b _ => hm a b, fun hm a b => hm a trivial b trivial⟩
  rw [e]
  exact isCompact_univ_pi (fun _ : Fin n => isCompact_univ_pi (fun _ : Fin n => isCompact_O h))

theorem isCompact_GLint (h : LF O ϖ nrm q) (n : ℕ) : IsCompact (GLint O n : Set (GL (Fin n) F)) := by
  haveI : T2Space F := by
    letI := IsTopologicalAddGroup.rightUniformSpace F
    haveI := isUniformAddGroup_of_addCommGroup (G := F)
    infer_instance
  have hc := isCompact_int h n
  have h2 := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) F)).isCompact_preimage
    (hc.prod (hc.image MulOpposite.continuous_op))
  refine h2.of_isClosed_subset ((GLint O n).isClosed_of_isOpen (isOpen_GLint h n)) ?_
  intro x hx
  exact ⟨hx.1, _, hx.2, rfl⟩



end Top

end GlobalTheory.CompanionTheory.QL.Par
end

section
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.Tame

section Alg

variable {F : Type} [Field F]

theorem det_eq_coe {ι : Type} [Fintype ι] [DecidableEq ι] (O : Subring F) (X : Matrix ι ι F)
    (hX : ∀ i j, X i j ∈ O) :
    X.det = ((Matrix.det (fun i j => (⟨X i j, hX i j⟩ : O)) : O) : F) := by
  have h := RingHom.map_det O.subtype (fun i j => (⟨X i j, hX i j⟩ : O))
  have h2 : O.subtype.mapMatrix (fun i j => (⟨X i j, hX i j⟩ : O) : Matrix ι ι O) = X := by
    ext i j; rfl
  rw [h2] at h
  exact h.symm

theorem det_mem {ι : Type} [Fintype ι] [DecidableEq ι] (O : Subring F) (X : Matrix ι ι F)
    (hX : ∀ i j, X i j ∈ O) : X.det ∈ O := by
  rw [det_eq_coe O X hX]; exact Subtype.property _

theorem det_congr_mod {ι : Type} [Fintype ι] [DecidableEq ι] (O : Subring F) {ϖ : F} (hϖ : ϖ ∈ O)
    (X Y : Matrix ι ι F) (hX : ∀ i j, X i j ∈ O) (hY : ∀ i j, Y i j ∈ O)
    (h : ∀ i j, ∃ o ∈ O, X i j - Y i j = ϖ * o) : ∃ o ∈ O, X.det - Y.det = ϖ * o := by
  let Xo : Matrix ι ι O := fun i j => ⟨X i j, hX i j⟩
  let Yo : Matrix ι ι O := fun i j => ⟨Y i j, hY i j⟩
  let I : Ideal O := Ideal.span {⟨ϖ, hϖ⟩}
  have hmap : (Ideal.Quotient.mk I).mapMatrix Xo = (Ideal.Quotient.mk I).mapMatrix Yo := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
    obtain ⟨o, ho, e⟩ := h i j
    refine ⟨⟨o, ho⟩, Subtype.ext ?_⟩
    change o * ϖ = X i j - Y i j
    rw [e, mul_comm]
  have hdet : Ideal.Quotient.mk I Xo.det = Ideal.Quotient.mk I Yo.det := by
    rw [RingHom.map_det, RingHom.map_det, hmap]
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hdet
  obtain ⟨a, ha⟩ := hdet
  refine ⟨a, a.2, ?_⟩
  rw [det_eq_coe O X hX, det_eq_coe O Y hY]
  have := congrArg Subtype.val ha
  change (a : F) * ϖ = ((Xo.det : O) : F) - ((Yo.det : O) : F) at this
  change ((Xo.det : O) : F) - ((Yo.det : O) : F) = ϖ * a
  rw [← this, mul_comm]

theorem det_eq_blocks {r c : ℕ} (M : Matrix (Fin (r + c)) (Fin (r + c)) F) :
    M.det = (Matrix.fromBlocks (bAA M) (bAD M) (bDA M) (bDD M)).det := by
  have h : M = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (bAA M) (bAD M) (bDA M) (bDD M)) := by
    ext i j
    induction i using Fin.addCases <;> induction j using Fin.addCases <;>
      simp [bAA, bAD, bDA, bDD]
  conv_lhs => rw [h]
  exact Matrix.det_reindex_self _ _

theorem bDD_one {r c : ℕ} : bDD (1 : Matrix (Fin (r + c)) (Fin (r + c)) F) = 1 :=
  Matrix.submatrix_one _ (Fin.natAdd_injective _ _)

theorem extendedCharacter_units (δ : Fˣ →* ℂˣ) (u : Fˣ) : chi0 δ (u : F) = ((δ u : ℂˣ) : ℂ) := by
  unfold chi0
  rw [dif_neg u.ne_zero]
  simp

theorem unitCharExtendedByZero_mul (δ : Fˣ →* ℂˣ) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    chi0 δ (x * y) = chi0 δ x * chi0 δ y := by
  have e : x * y = ((Units.mk0 x hx * Units.mk0 y hy : Fˣ) : F) := by simp
  rw [e, extendedCharacter_units, map_mul, Units.val_mul, ← extendedCharacter_units, ← extendedCharacter_units]
  simp

theorem extendedCharacter_congr_of_tame {nrm : AbsoluteValue F ℝ} {δ : Fˣ →* ℂˣ} (hδ : Del nrm δ) {x y : F}
    (hy : nrm y = 1) (hxy : nrm (x - y) < 1) : chi0 δ x = chi0 δ y := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp [hy] at hxy
  have h1 : δ (Units.mk0 x hx0 / Units.mk0 y hy0) = 1 := by
    apply hδ.tame
    have e : (((Units.mk0 x hx0 / Units.mk0 y hy0 : Fˣ) : F) - 1) = (x - y) / y := by
      simp only [Units.val_div_eq_div_val, Units.val_mk0]
      field_simp
    rw [e, map_div₀, hy, div_one]
    exact hxy
  rw [map_div, div_eq_one] at h1
  have ex : x = ((Units.mk0 x hx0 : Fˣ) : F) := rfl
  have ey : y = ((Units.mk0 y hy0 : Fˣ) : F) := rfl
  rw [ex, ey, extendedCharacter_units, extendedCharacter_units, h1]

end Alg

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

theorem par_data (h : LF O ϖ nrm q) {r c : ℕ} {k : GL (Fin (r + c)) F} (hk : k ∈ parJ O ϖ r c) :
    nrm (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧
    nrm (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧
    ∃ o ∈ O, (k : Matrix (Fin (r + c)) (Fin (r + c)) F).det -
      (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det *
      (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = ϖ * o := by
  obtain ⟨-, hϖ, hO, hlt, -, hult, -⟩ := GlobalTheory.T.localField_uniformizer_norm_properties h
  set M : Matrix (Fin (r + c)) (Fin (r + c)) F := (k : Matrix (Fin (r + c)) (Fin (r + c)) F) with hMdef
  have hM : IsInt O M := hk.1.1
  have hdet : nrm M.det = 1 := ((GlobalTheory.T.mem_integralGL_iff_integral_unit_det h (r + c) k).1 hk.1).2
  have hC := hk.2
  have hcong : ∃ o ∈ O, M.det - (bAA M).det * (bDD M).det = ϖ * o := by
    have := det_congr_mod O hϖ (Matrix.fromBlocks (bAA M) (bAD M) (bDA M) (bDD M))
      (Matrix.fromBlocks (bAA M) (bAD M) 0 (bDD M))
      (by rintro (i | i) (j | j) <;> exact hM _ _)
      (by
        rintro (i | i) (j | j)
        · exact hM _ _
        · exact hM _ _
        · exact O.zero_mem
        · exact hM _ _)
      (by
        rintro (i | i) (j | j)
        · exact ⟨0, O.zero_mem, by simp⟩
        · exact ⟨0, O.zero_mem, by simp⟩
        · obtain ⟨o, ho, e⟩ := hC i j
          exact ⟨o, ho, by simpa using e⟩
        · exact ⟨0, O.zero_mem, by simp⟩)
    rwa [← det_eq_blocks, Matrix.det_fromBlocks_zero₂₁] at this
  obtain ⟨o, ho, e⟩ := hcong
  have hA : nrm (bAA M).det ≤ 1 := (hO _).2 (det_mem O _ fun i j => hM _ _)
  have hD : nrm (bDD M).det ≤ 1 := (hO _).2 (det_mem O _ fun i j => hM _ _)
  have hsmall : nrm (ϖ * o) < 1 := (hlt _).2 ⟨o, ho, rfl⟩
  have hprod : 1 ≤ nrm (bAA M).det * nrm (bDD M).det := by
    have e2 : M.det = (bAA M).det * (bDD M).det + ϖ * o := by rw [← e]; ring
    have h3 := hult ((bAA M).det * (bDD M).det) (ϖ * o)
    rw [← e2, hdet, map_mul] at h3
    rcases le_max_iff.1 h3 with h4 | h4
    · exact h4
    · exact absurd h4 (not_le.2 hsmall)
  have hA0 : 0 ≤ nrm (bAA M).det := nrm.nonneg _
  have hD0 : 0 ≤ nrm (bDD M).det := nrm.nonneg _
  refine ⟨?_, ?_, o, ho, e⟩ <;> nlinarith

theorem lam_mul (h : LF O ϖ nrm q) {δ : Fˣ →* ℂˣ} (hδ : Del nrm δ) {r c : ℕ}
    {k k' : GL (Fin (r + c)) F} (hk : k ∈ parJ O ϖ r c) (hk' : k' ∈ parJ O ϖ r c) :
    lamJ δ (k * k') = lamJ δ k * lamJ δ k' := by
  obtain ⟨-, hϖ, hO, hlt, -, -, -⟩ := GlobalTheory.T.localField_uniformizer_norm_properties h
  obtain ⟨-, hD, -⟩ := par_data h hk
  obtain ⟨-, hD', -⟩ := par_data h hk'
  unfold lamJ
  have hC := hk.2
  set M : Matrix (Fin (r + c)) (Fin (r + c)) F := (k : Matrix (Fin (r + c)) (Fin (r + c)) F) with hMdef
  set M' : Matrix (Fin (r + c)) (Fin (r + c)) F := (k' : Matrix (Fin (r + c)) (Fin (r + c)) F) with hM'def
  have hM : IsInt O M := hk.1.1
  have hM' : IsInt O M' := hk'.1.1
  have hprod : ((k * k' : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = M * M' := rfl
  have hblock : bDD (M * M') = bDA M * bAD M' + bDD M * bDD M' :=
    (GlobalTheory.CompanionTheory.QL.BlockMul.blocks_mul r c c c M M').2.2.2
  rw [hprod, hblock]
  choose o ho e using hC
  have hCB : ∀ i j, ∃ t ∈ O, (bDA M * bAD M') i j = ϖ * t := by
    intro i j
    refine ⟨∑ l, o i l * bAD M' l j, O.sum_mem fun l _ => O.mul_mem (ho i l) (hM' _ _), ?_⟩
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [e i l, mul_assoc]
  have hDD : ∀ i j, (bDD M * bDD M') i j ∈ O := by
    intro i j
    rw [Matrix.mul_apply]
    exact O.sum_mem fun l _ => O.mul_mem (hM _ _) (hM' _ _)
  obtain ⟨t, ht, et⟩ := det_congr_mod O hϖ (bDA M * bAD M' + bDD M * bDD M') (bDD M * bDD M')
    (by
      intro i j
      obtain ⟨t, ht, et⟩ := hCB i j
      rw [Matrix.add_apply, et]
      exact O.add_mem (O.mul_mem hϖ ht) (hDD i j))
    hDD
    (by
      intro i j
      obtain ⟨t, ht, et⟩ := hCB i j
      exact ⟨t, ht, by rw [Matrix.add_apply, et]; ring⟩)
  have hn : nrm (bDD M * bDD M').det = 1 := by
    rw [Matrix.det_mul, map_mul, hD, hD', one_mul]
  have hne : ∀ {x : F}, nrm x = 1 → x ≠ 0 := by
    rintro x hx rfl
    simp at hx
  rw [extendedCharacter_congr_of_tame hδ hn (by rw [et]; exact (hlt _).2 ⟨t, ht, rfl⟩), Matrix.det_mul,
    unitCharExtendedByZero_mul δ (hne hD) (hne hD')]

end Loc

theorem tame_character : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ δ : Fˣ →* ℂˣ, Del nrm δ → ∀ r c : ℕ, lamJ δ (1 : GL (Fin (r + c)) F) = 1 ∧ (∀ k ∈ parJ O ϖ r c, ‖lamJ δ k‖ = 1 ∧ nrm (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧ nrm (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧ ((δ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) = chi0 δ (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det * lamJ δ k ∧ ∀ k' ∈ parJ O ϖ r c, lamJ δ (k * k') = lamJ δ k * lamJ δ k') ∧ ContinuousOn (fun k : GL (Fin (r + c)) F => lamJ δ k) (parJ O ϖ r c) := by
  intro F _ _ _ _ O ϖ nrm q h δ hδ r c
  obtain ⟨-, hϖ, hO, hlt, -, -, -⟩ := GlobalTheory.T.localField_uniformizer_norm_properties h
  have hne : ∀ {x : F}, nrm x = 1 → x ≠ 0 := by
    rintro x hx rfl
    simp at hx
  refine ⟨?_, ?_, ?_⟩
  · unfold lamJ
    have e : ((1 : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 1 := rfl
    rw [e, bDD_one, Matrix.det_one]
    have := extendedCharacter_units δ (1 : Fˣ)
    simpa using this
  · intro k hk
    obtain ⟨hA, hD, o, ho, e⟩ := par_data h hk
    refine ⟨?_, hA, hD, ?_, fun k' hk' => lam_mul h hδ hk hk'⟩
    · unfold lamJ
      have : (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det =
          ((Units.mk0 _ (hne hD) : Fˣ) : F) := rfl
      rw [this, extendedCharacter_units]
      exact hδ.unitary _
    · unfold lamJ
      rw [← extendedCharacter_units, ← unitCharExtendedByZero_mul δ (hne hA) (hne hD)]
      apply extendedCharacter_congr_of_tame hδ
      · rw [map_mul, hA, hD, one_mul]
      · rw [Matrix.GeneralLinearGroup.val_det_apply, e]
        exact (hlt _).2 ⟨o, ho, rfl⟩
  · obtain ⟨-, -, -, hcont, -, -⟩ := GlobalTheory.T.localField_topology_norm_balls h
    intro k₀ hk₀
    obtain ⟨-, hD₀, -⟩ := par_data h hk₀
    have hf : Continuous (fun k : GL (Fin (r + c)) F =>
        (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det) :=
      Continuous.matrix_det (Continuous.matrix_submatrix Units.continuous_val _ _)
    have hU : {k : GL (Fin (r + c)) F | nrm ((bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det -
        (bDD (k₀ : Matrix (Fin (r + c)) (Fin (r + c)) F)).det) < 1} ∈ nhds k₀ := by
      refine IsOpen.mem_nhds (isOpen_lt (hcont.comp (hf.sub continuous_const)) continuous_const) ?_
      simp
    refine (continuousWithinAt_const (b := lamJ δ k₀)).congr_of_eventuallyEq ?_ rfl
    filter_upwards [mem_nhdsWithin_of_mem_nhds hU] with k hkU
    exact extendedCharacter_congr_of_tame hδ hD₀ hkU

end GlobalTheory.CompanionTheory.QL.Tame
end

open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoric_character_modulus_properties : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ δ : Fˣ →* ℂˣ, Del nrm δ → ∀ r c : ℕ, lamJ δ (1 : GL (Fin (r + c)) F) = 1 ∧ (∀ k ∈ parJ O ϖ r c, ‖lamJ δ k‖ = 1 ∧ nrm (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧ nrm (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧ ((δ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) = chi0 δ (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det * lamJ δ k ∧ ∀ k' ∈ parJ O ϖ r c, lamJ δ (k * k') = lamJ δ k * lamJ δ k') ∧ ContinuousOn (fun k : GL (Fin (r + c)) F => lamJ δ k) (parJ O ϖ r c) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.QL.Tame.tame_character
end

section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.Eigen

section Alg

variable {F : Type} [Field F]

theorem unramifiedCharExt_mul (δ : Fˣ →* ℂˣ) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    chi0 δ (x * y) = chi0 δ x * chi0 δ y := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  simp only [chi0, dif_neg hx, dif_neg hy, dif_neg hxy]
  rw [show Units.mk0 (x * y) hxy = Units.mk0 x hx * Units.mk0 y hy from Units.ext rfl, map_mul,
    Units.val_mul]


theorem extendedCharacter_congr_of_tame (nrm : AbsoluteValue F ℝ) (δ : Fˣ →* ℂˣ)
    (tame : ∀ x : Fˣ, nrm ((x : F) - 1) < 1 → δ x = 1) {u v : F} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : nrm (u - v) < nrm v) : chi0 δ u = chi0 δ v := by
  have hw : u / v ≠ 0 := div_ne_zero hu hv
  have h1 : chi0 δ (u / v) = 1 := by
    simp only [chi0, dif_neg hw]
    have : δ (Units.mk0 (u / v) hw) = 1 := by
      apply tame
      have e : ((Units.mk0 (u / v) hw : Fˣ) : F) - 1 = (u - v) / v := by
        simp only [Units.val_mk0]; field_simp
      rw [e, map_div₀]
      exact (div_lt_one (nrm.pos hv)).2 h
    rw [this]; rfl
  have h2 : u = (u / v) * v := by field_simp
  calc chi0 δ u = chi0 δ ((u / v) * v) := by rw [← h2]
    _ = chi0 δ v := by rw [unramifiedCharExt_mul δ hw hv, h1, one_mul]

theorem int_mul {O : Subring F} {a b c : ℕ} {X : Matrix (Fin a) (Fin b) F}
    {Y : Matrix (Fin b) (Fin c) F} (hX : X ∈ intMat O a b) (hY : Y ∈ intMat O b c) :
    X * Y ∈ intMat O a c := fun i j => by
  rw [Matrix.mul_apply]; exact O.sum_mem fun k _ => O.mul_mem (hX i k) (hY k j)

theorem int_add {O : Subring F} {a b : ℕ} {X Y : Matrix (Fin a) (Fin b) F}
    (hX : X ∈ intMat O a b) (hY : Y ∈ intMat O a b) : X + Y ∈ intMat O a b :=
  fun i j => O.add_mem (hX i j) (hY i j)

theorem II_add {O : Subring F} {ϖ : F} {a b : ℕ} {X Y : Matrix (Fin a) (Fin b) F}
    (hX : X ∈ IIset O ϖ) (hY : Y ∈ IIset O ϖ) : X + Y ∈ IIset O ϖ := fun i j => by
  obtain ⟨o, ho, e⟩ := hX i j
  obtain ⟨p, hp, f⟩ := hY i j
  exact ⟨o + p, O.add_mem ho hp, by rw [Matrix.add_apply, e, f, mul_add]⟩

theorem II_mul_int {O : Subring F} {ϖ : F} {a b c : ℕ} {X : Matrix (Fin a) (Fin b) F}
    {Y : Matrix (Fin b) (Fin c) F} (hX : X ∈ IIset O ϖ) (hY : Y ∈ intMat O b c) :
    X * Y ∈ IIset O ϖ := fun i j => by
  choose f hf hfe using hX
  refine ⟨∑ k, f i k * Y k j, O.sum_mem fun k _ => O.mul_mem (hf i k) (hY k j), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [hfe, mul_assoc]

theorem int_mul_II {O : Subring F} {ϖ : F} {a b c : ℕ} {X : Matrix (Fin a) (Fin b) F}
    {Y : Matrix (Fin b) (Fin c) F} (hX : X ∈ intMat O a b) (hY : Y ∈ IIset O ϖ) :
    X * Y ∈ IIset O ϖ := fun i j => by
  choose f hf hfe using hY
  refine ⟨∑ k, X i k * f k j, O.sum_mem fun k _ => O.mul_mem (hX i k) (hf k j), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [hfe]; ring

theorem II_int {O : Subring F} {ϖ : F} (hϖ : ϖ ∈ O) {a b : ℕ} {X : Matrix (Fin a) (Fin b) F}
    (hX : X ∈ IIset O ϖ) : X ∈ intMat O a b := fun i j => by
  obtain ⟨o, ho, e⟩ := hX i j
  rw [e]; exact O.mul_mem hϖ ho

theorem det_congr {O : Subring F} {ϖ : F} (hϖ : ϖ ∈ O) {n : ℕ} {P Q : Matrix (Fin n) (Fin n) F}
    (hP : P ∈ intMat O n n) (hQ : Q ∈ intMat O n n) (h : P - Q ∈ IIset O ϖ) :
    ∃ o ∈ O, P.det - Q.det = ϖ * o := by
  let P' : Matrix (Fin n) (Fin n) O := fun i j => ⟨P i j, hP i j⟩
  let Q' : Matrix (Fin n) (Fin n) O := fun i j => ⟨Q i j, hQ i j⟩
  let I : Ideal O := Ideal.span {(⟨ϖ, hϖ⟩ : O)}
  have hm : (Ideal.Quotient.mk I).mapMatrix P' = (Ideal.Quotient.mk I).mapMatrix Q' := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    refine Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ?_)
    obtain ⟨o, ho, e⟩ := h i j
    refine ⟨⟨o, ho⟩, Subtype.ext ?_⟩
    show o * ϖ = P i j - Q i j
    rw [mul_comm]; exact e.symm
  have hd : Ideal.Quotient.mk I P'.det = Ideal.Quotient.mk I Q'.det := by
    rw [RingHom.map_det, RingHom.map_det, hm]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hd)
  have hPd : P.det = ((P'.det : O) : F) := by
    have e : O.subtype.mapMatrix P' = P := by ext i j; rfl
    have := RingHom.map_det O.subtype P'
    rw [e] at this
    exact this.symm
  have hQd : Q.det = ((Q'.det : O) : F) := by
    have e : O.subtype.mapMatrix Q' = Q := by ext i j; rfl
    have := RingHom.map_det O.subtype Q'
    rw [e] at this
    exact this.symm
  have hv : (a : F) * ϖ = ((P'.det : O) : F) - ((Q'.det : O) : F) := congrArg Subtype.val ha
  exact ⟨a, a.2, by rw [hPd, hQd, ← hv, mul_comm]⟩

theorem nrm_eq_one_of_close {nrm : AbsoluteValue F ℝ}
    (hna : ∀ x y : F, nrm (x + y) ≤ max (nrm x) (nrm y)) {u v : F} (hv : nrm v = 1)
    (h : nrm (u - v) < 1) : nrm u = 1 := by
  apply le_antisymm
  · have := hna (u - v) v
    rw [sub_add_cancel, hv] at this
    exact this.trans (max_le h.le le_rfl)
  · have := hna u (v - u)
    rw [add_sub_cancel, hv, nrm.map_sub v u] at this
    rcases le_max_iff.1 this with h' | h'
    · exact h'
    · exact absurd h (not_lt.2 h')

end Alg

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

def Supp (O : Subring F) (ϖ : F) {r d c : ℕ} (x : Matrix (Fin (r + d)) (Fin (r + c)) F) : Prop :=
  bAA x ∈ Jset (GLint O r) ∧ bDA x ∈ IIset O ϖ ∧ bAD x ∈ intMat O r c ∧ bDD x ∈ intMat O d c

theorem Jset_iff (hLF : LF O ϖ nrm q) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    M ∈ Jset (GLint O n) ↔ M ∈ intMat O n n ∧ nrm M.det = 1 := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (GlobalTheory.T.mem_integralGL_iff_integral_unit_det hLF n g).1 hg
  · rintro ⟨h, hd⟩
    have hne : M.det ≠ 0 := fun h0 => by
      rw [h0, map_zero] at hd; exact zero_ne_one hd
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hne, ?_, rfl⟩
    exact (GlobalTheory.T.mem_integralGL_iff_integral_unit_det hLF n _).2 ⟨h, hd⟩

theorem step (hLF : LF O ϖ nrm q) (δ : Fˣ →* ℂˣ) (hδ : Del nrm δ) {r d c : ℕ}
    {k : GL (Fin (r + c)) F} (hk : k ∈ parJ O ϖ r c) {x : Matrix (Fin (r + d)) (Fin (r + c)) F}
    (hx : Supp O ϖ x) :
    Supp O ϖ (x * (k : Matrix (Fin (r + c)) (Fin (r + c)) F)) ∧
      chi0 δ (bAA (x * (k : Matrix (Fin (r + c)) (Fin (r + c)) F))).det =
        chi0 δ (bAA x).det * chi0 δ (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det := by
  obtain ⟨-, hϖ, -, hlt, -, hna, -⟩ := NormalisedValue.main hLF
  obtain ⟨e1, e2, e3, e4⟩ := BlockMul.blocks_mul r d c c x (k : Matrix (Fin (r + c)) (Fin (r + c)) F)
  have kint : ∀ i j, (k : Matrix (Fin (r + c)) (Fin (r + c)) F) i j ∈ O := hk.1.1
  have ka : bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F) ∈ intMat O r r := fun i j => kint _ _
  have kb : bAD (k : Matrix (Fin (r + c)) (Fin (r + c)) F) ∈ intMat O r c := fun i j => kint _ _
  have kd : bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F) ∈ intMat O c c := fun i j => kint _ _
  have kc : bDA (k : Matrix (Fin (r + c)) (Fin (r + c)) F) ∈ IIset O ϖ := hk.2
  obtain ⟨hA, hC, hB, hD⟩ := hx
  obtain ⟨hAi, hAd⟩ := (Jset_iff hLF _).1 hA
  have hadet : nrm (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 :=
    ((GlobalTheory.T.parahoric_character_modulus_properties hLF δ hδ r c).2.1 k hk).2.1
  have hV := int_mul hAi ka
  have hW := int_mul_II hB kc
  have hU : bAA (x * (k : Matrix (Fin (r + c)) (Fin (r + c)) F)) ∈ intMat O r r := by
    rw [e1]; exact int_add hV (II_int hϖ hW)
  have hdiff : bAA (x * (k : Matrix (Fin (r + c)) (Fin (r + c)) F)) -
      bAA x * bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F) ∈ IIset O ϖ := by
    rw [e1, add_sub_cancel_left]; exact hW
  obtain ⟨o, ho, hoe⟩ := det_congr hϖ hU hV hdiff
  have hVd : nrm (bAA x * bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 := by
    rw [Matrix.det_mul, map_mul, hAd, hadet, one_mul]
  have hlt' := (hlt _).2 ⟨o, ho, hoe⟩
  have hUd := nrm_eq_one_of_close hna hVd hlt'
  have hUne : (bAA (x * (k : Matrix (Fin (r + c)) (Fin (r + c)) F))).det ≠ 0 := fun h => by
    rw [h, map_zero] at hUd; exact zero_ne_one hUd
  have hVne : (bAA x * bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det ≠ 0 := fun h => by
    rw [h, map_zero] at hVd; exact zero_ne_one hVd
  refine ⟨⟨(Jset_iff hLF _).2 ⟨hU, hUd⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [e3]; exact II_add (II_mul_int hC ka) (int_mul_II hD kc)
  · rw [e2]; exact int_add (int_mul hAi kb) (int_mul hB kd)
  · rw [e4]; exact int_add (int_mul (II_int hϖ hC) kb) (int_mul hD kd)
  · rw [extendedCharacter_congr_of_tame nrm δ hδ.tame hUne hVne (by rw [hVd]; exact hlt')]
    rw [Matrix.det_mul] at hVne ⊢
    exact unramifiedCharExt_mul δ (left_ne_zero_of_mul hVne) (right_ne_zero_of_mul hVne)


end Local

end GlobalTheory.CompanionTheory.QL.Eigen
end
