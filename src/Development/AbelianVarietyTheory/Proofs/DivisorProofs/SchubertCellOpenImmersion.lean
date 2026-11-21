import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockLuDecompositionExists
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula
open GlobalTheory.ProjSpace

namespace GlobalTheory.FlagZ

theorem isImmersion_of_X_mem_range {σ : Type} {Y : Scheme.{0}} (f : Sp (MvPolynomial σ ℤ) ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ f ⁻¹ᵁ U) (hX : ∀ s, fnOn ⊤ (MvPolynomial.X s) ∈ (f.appLE U ⊤ h).hom.range) : IsImmersion f := by
  choose t ht using hX
  let ψ : CommRingCat.of (MvPolynomial σ ℤ) ⟶ Γ(Y, U) :=
    CommRingCat.ofHom (MvPolynomial.eval₂Hom (Int.castRingHom _) t)
  have e : ψ ≫ f.appLE U ⊤ h = CommRingCat.ofHom (fnOn ⊤) := by
    ext1
    refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun s => ?_
    rw [CommRingCat.hom_ofHom, ← ht s]
    simp [ψ]
  have i₁ : IsIso (CommRingCat.ofHom (fnOn (A := MvPolynomial σ ℤ) ⊤)) :=
    (ConcreteCategory.isIso_iff_bijective _).2 fnOn_top_bijective
  have i₂ : IsIso (⊤ : (Sp (MvPolynomial σ ℤ)).Opens).toSpecΓ :=
    (isAffineOpen_top _).isoSpec.isIso_hom
  have i₃ : IsImmersion (f.resLE U ⊤ h ≫ U.toSpecΓ ≫ Spec.map ψ) := by
    rw [← Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, ← Spec.map_comp, e]
    infer_instance
  have i₄ : IsImmersion (f.resLE U ⊤ h) := IsImmersion.of_comp _ (U.toSpecΓ ≫ Spec.map ψ)
  have e₂ : f = (Sp (MvPolynomial σ ℤ)).topIso.inv ≫ f.resLE U ⊤ h ≫ U.ι := by
    rw [Scheme.Hom.resLE_comp_ι, ← Scheme.topIso_hom, Iso.inv_hom_id_assoc]
  rw [e₂]
  infer_instance

variable {N : ℕ} {A : Type} [CommRing A]

theorem exists_det_eq_sign_mul_minor (g : Matrix (Fin N) (Fin N) A) (l : Fin (N + 1)) (e : Fin l → Fin N)
    (he : Function.Injective e) :
    ∃ (I : Rows N l) (ε : ℤˣ), (g.submatrix e (Fin.castLE l.is_le)).det = ((ε : ℤ) : A) * minor g l I := by
  let I : Rows N l := ⟨Finset.univ.map ⟨e, he⟩, by simp [Set.powersetCard.mem_iff]⟩
  have hr : Set.range e = Set.range (subsetEnum I) := by
    rw [range_subsetEnum]
    simp [I]
  let p : Equiv.Perm (Fin l) := (Equiv.ofInjective e he).trans
    ((Equiv.setCongr hr).trans (Equiv.ofInjective _ (subsetEnum_injective I)).symm)
  have hp : subsetEnum I ∘ p = e := funext fun x => Equiv.apply_ofInjective_symm (subsetEnum_injective I) _
  refine ⟨I, Equiv.Perm.sign p, ?_⟩
  rw [minor, ← det_permute, submatrix_submatrix, hp]
  rfl

theorem det_updateRow_of_col_eq {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n A) (hM : M.det = 1) (j : n)
    (hj : ∀ c, M c j = (1 : Matrix n n A) c j) (r : n → A) : (M.updateRow j r).det = r j := by
  have h := congrFun (mulVec_cramer Mᵀ r) j
  rw [det_transpose, hM, one_smul] at h
  rw [← h, ← cramer_transpose_apply]
  simp [mulVec, dotProduct, hj, one_apply]

variable {ι κ : Type} (a : κ → ι) (l : κ → Fin (N + 1))

theorem det_lowMat_lead (τ : ι) (m : Fin (N + 1)) :
    ((lowMat a l τ).submatrix (Fin.castLE m.is_le) (Fin.castLE m.is_le)).det = 1 := by
  have h {i j : Fin N} (hij : i ≤ j) : lowMat a l τ i j = (1 : Matrix _ _ _) i j :=
    dif_neg fun ⟨_, _, h₁, h₂⟩ => (h₁.trans_le h₂).not_ge hij
  have ht : ((lowMat a l τ).submatrix (Fin.castLE m.is_le) (Fin.castLE m.is_le)).BlockTriangular
      OrderDual.toDual := fun i j hij =>
    (h (le_of_lt (show i < j from hij))).trans
      (one_apply_ne ((Fin.castLE_injective _).ne (ne_of_lt (show i < j from hij))))
  rw [det_of_isLowerTriangular _ ht]
  simp [h le_rfl]

theorem exists_det_lowMat_eq (w : ι → Equiv.Perm (Fin N)) (τ : ι) (m : Fin (N + 1)) (e : Fin m → Fin N)
    (he : Function.Injective e) : ∃ (c : Fin (plDim N m + 1)) (ε : ℤˣ),
      ((lowMat a l τ).submatrix e (Fin.castLE m.is_le)).det =
        ((ε : ℤ) : CellRing a l) * plVec (cellGL a l w τ).1 m c := by
  obtain ⟨I, ε, h⟩ := exists_det_eq_sign_mul_minor (cellGL a l w τ).1 m ((w τ).symm ∘ e)
    ((w τ).symm.injective.comp he)
  refine ⟨rowsEquiv N m I, ε, ?_⟩
  rw [plVec_rowsEquiv, ← h]
  congr 1
  refine Matrix.ext fun i j => ?_
  change _ = lowMat a l τ (w τ ((w τ).symm (e i))) _
  rw [Equiv.apply_symm_apply]
  rfl

theorem exists_X_eq_plVec [Finite κ] (w : ι → Equiv.Perm (Fin N)) (x : CellVar a l) :
    ∃ (k : κ) (c : Fin (plDim N (l k) + 1)) (ε : ℤˣ),
      MvPolynomial.X x = ((ε : ℤ) : CellRing a l) * plVec (cellGL a l w (a k)).1 (l k) c := by
  obtain ⟨⟨τ, i, j⟩, k₀, hk₀, h₁, h₂⟩ := x
  obtain ⟨k, ⟨rfl, hj⟩, hmin⟩ := Set.exists_min_image {k | a k = τ ∧ (j : ℕ) < l k} (fun k => (l k : ℕ))
    (Set.toFinite _) ⟨k₀, hk₀, h₁⟩
  have hi : (l k : ℕ) ≤ i := (hmin k₀ ⟨hk₀, h₁⟩).trans h₂
  have hinj : Function.Injective (Function.update (Fin.castLE (l k).is_le) ⟨j, hj⟩ i) := by
    intro s t hst
    by_cases hs : s = ⟨j, hj⟩ <;> by_cases ht : t = ⟨j, hj⟩
    · rw [hs, ht]
    · rw [hs, Function.update_self, Function.update_of_ne ht] at hst
      exact absurd (hi.trans_eq (congrArg Fin.val hst)) t.2.not_ge
    · rw [ht, Function.update_self, Function.update_of_ne hs] at hst
      exact absurd (hi.trans_eq (congrArg Fin.val hst.symm)) s.2.not_ge
    · rw [Function.update_of_ne hs, Function.update_of_ne ht] at hst
      exact Fin.castLE_injective _ hst
  obtain ⟨c, ε, h⟩ := exists_det_lowMat_eq a l w (a k) (l k) _ hinj
  refine ⟨k, c, ε, Eq.trans ?_ h⟩
  have hd := det_updateRow_of_col_eq _ (det_lowMat_lead a l (a k) (l k)) ⟨j, hj⟩ (fun c => by
    refine (dif_neg fun ⟨k', hk', h₃, h₄⟩ => ((hmin k' ⟨hk', h₃⟩).trans h₄).not_gt c.2).trans ?_
    simp only [one_apply, (Fin.castLE_injective _).eq_iff]) fun c => lowMat a l (a k) i (Fin.castLE (l k).is_le c)
  refine Eq.trans (Eq.trans ?_ hd.symm) ?_
  · change _ = lowMat a l (a k) i j
    rw [lowMat, of_apply, dif_pos ⟨k₀, hk₀, h₁, h₂⟩]
  · congr 1
    refine Matrix.ext fun s t => ?_
    by_cases hs : s = ⟨j, hj⟩
    · simp [hs]
    · simp [updateRow_ne hs, Function.update_of_ne hs]

theorem isImmersion_plPt_cellGL : ∀ (ι κ : Type) [Fintype ι] [Finite κ] (N : ℕ) (a : κ → ι) (l : κ → Fin (N + 1))
    (w : ι → Equiv.Perm (Fin N)), IsImmersion (plPt a l (cellGL a l w)) := by
  intro ι κ _ _ N a l w
  choose b η hb using fun k => exists_det_lowMat_eq a l w (a k) (l k) _ (Fin.castLE_injective (l k).is_le)
  simp only [det_lowMat_lead] at hb
  let U : (Amb l).Opens := ⟨⋂ k, (Pi.π (fun k => PSpace ℤ (plDim N (l k))) k ⁻¹ᵁ chart ℤ _ (b k)).1,
    isOpen_iInter_of_finite fun k => (Pi.π (fun k => PSpace ℤ (plDim N (l k))) k ⁻¹ᵁ chart ℤ _ (b k)).2⟩
  have hU (k) : U ≤ Pi.π (fun k => PSpace ℤ (plDim N (l k))) k ⁻¹ᵁ chart ℤ _ (b k) :=
    fun y hy => Set.mem_iInter.1 hy k
  have hu (k) : IsUnit (plVec (cellGL a l w (a k)).1 (l k) (b k)) := IsUnit.of_mul_eq_one_right _ (hb k).symm
  have h₀ (k) : ⊤ ≤ (plPt a l (cellGL a l w) ≫ Pi.π _ k) ⁻¹ᵁ chart ℤ _ (b k) := by
    rw [plPt_π, pt_preimage_chart]
    exact fun y _ => mem_spOpen.2 fun hy => y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hy (hu k))
  have h : ⊤ ≤ plPt a l (cellGL a l w) ⁻¹ᵁ U := fun y hy => Set.mem_iInter.2 fun k => h₀ k hy
  refine isImmersion_of_X_mem_range _ U h fun x => ?_
  obtain ⟨k, c, ε, hx⟩ := exists_X_eq_plVec a l w x
  have e₁ := pullRatio_pt_top_mul (Int.castRingHom _) _ (span_plVec (cellGL a l w (a k)) (l k)) (b k) c (hu k)
    (plPt_π a l (cellGL a l w) k ▸ h₀ k)
  rw [← pullRatio_of_eq (plPt_π a l (cellGL a l w) k) (h₀ k), ← appLE_pullRatio (hi := hU k) _ h] at e₁
  have e₂ : plVec (cellGL a l w (a k)).1 (l k) (b k) = ((η k : ℤ) : CellRing a l) := by
    have := congrArg (((η k : ℤ) : CellRing a l) * ·) (hb k)
    simp only [mul_one, ← mul_assoc, ← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one, one_mul] at this
    exact this.symm
  rw [hx, map_mul, ← e₁, e₂, map_intCast, map_intCast]
  exact mul_mem (intCast_mem _ _) (mul_mem ⟨_, rfl⟩ (intCast_mem _ _))

end GlobalTheory.FlagZ
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schubert_cell_point_immersion : ∀ (ι κ : Type) [Fintype ι] [Finite κ] (N : ℕ) (a : κ → ι) (l : κ → Fin (N + 1)) (w : ι → Equiv.Perm (Fin N)), IsImmersion (plPt a l (cellGL a l w)) := by
  atlas_forward_decl GlobalTheory.FlagZ.isImmersion_plPt_cellGL
end

section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula

namespace GlobalTheory

def rowPermGL (A : Type) [CommRing A] {N : ℕ} (σ : Equiv.Perm (Fin N)) : GL (Fin N) A :=
  GeneralLinearGroup.mk'' ((1 : Matrix (Fin N) (Fin N) A).submatrix σ id) (by
    rw [det_permute, det_one, mul_one]
    exact (Equiv.Perm.sign σ).isUnit.map (Int.castRingHom _))

theorem rowPermGL_mul_apply {A : Type} [CommRing A] {N : ℕ} (σ : Equiv.Perm (Fin N)) (g : GL (Fin N) A) (i j : Fin N) :
    (rowPermGL A σ * g).1 i j = g.1 (σ i) j := by
  change ∑ k, (1 : Matrix (Fin N) (Fin N) A) (σ i) k * g.1 k j = _
  rw [← mul_apply, one_mul]

theorem leading_minor_univGL_ne_zero {ι : Type} [Fintype ι] {N : ℕ} (σ : Equiv.Perm (Fin N)) (τ : ι) (k : ℕ)
    (hk : k ≤ N) :
    ((rowPermGL _ σ.symm * univGL ι N τ).1.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0 := fun h => by
  have e := congrArg (evalGL fun _ : ι => rowPermGL ℤ σ) h
  rw [map_zero, RingHom.map_det] at e
  have e' : (evalGL fun _ : ι => rowPermGL ℤ σ).mapMatrix
      ((rowPermGL _ σ.symm * univGL ι N τ).1.submatrix (Fin.castLE hk) (Fin.castLE hk)) = 1 := by
    rw [← submatrix_one (α := ℤ) _ (Fin.castLE_injective hk)]
    ext i j
    rw [RingHom.mapMatrix_apply, map_apply, submatrix_apply, submatrix_apply, rowPermGL_mul_apply, univGL_apply,
      evalGL_X]
    change (1 : Matrix (Fin N) (Fin N) ℤ) (σ (σ.symm _)) _ = _
    rw [Equiv.apply_symm_apply]
    rfl
  rw [e', det_one] at e
  exact one_ne_zero e

theorem exists_generic_comp_orbit_eq_comp_cell {ι κ : Type} [Fintype ι] [Finite κ] {N : ℕ} (a : κ → ι)
    (l : κ → Fin (N + 1)) (w : ι → Equiv.Perm (Fin N)) :
    ∃ s : Sp (FractionRing (GLRing ι N)) ⟶ Sp (CellRing a l),
      spMap (algebraMap (GLRing ι N) (FractionRing (GLRing ι N))) ≫ orbit a l = s ≫ cell a l w := by
  set K := FractionRing (GLRing ι N)
  set φ := algebraMap (GLRing ι N) K
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  have h (τ : ι) := exists_blockLower_mul_blockUpper K N {s | ∃ k, a k = τ ∧ (l k : ℕ) = s}
    (GeneralLinearGroup.map φ (rowPermGL _ (w τ).symm * univGL ι N τ)) fun k hk => by
      refine Ne.isUnit fun h => leading_minor_univGL_ne_zero (w τ) τ k hk (hφ ?_)
      rw [map_zero, RingHom.map_det]
      exact h
  choose L b hLb hL hb using h
  have hB (τ : ι) (i j : Fin N) : Below a l τ i j ↔
      ∃ s ∈ {s | ∃ k, a k = τ ∧ (l k : ℕ) = s}, (j : ℕ) < s ∧ s ≤ (i : ℕ) :=
    ⟨fun ⟨k, h₁, h₂⟩ => ⟨_, ⟨k, h₁, rfl⟩, h₂⟩, fun ⟨_, ⟨k, h₁, h₂⟩, h₃⟩ => ⟨k, h₁, h₂ ▸ h₃⟩⟩
  refine ⟨_, Eq.trans ?_ (flagPt_eq_comp_cell a l w (fun τ => rowPermGL K (w τ) * L τ) b
    (fun τ i j hij => by rw [rowPermGL_mul_apply]; exact hL τ _ _ (mt (hB _ _ _).2 hij))
    fun τ i j hij => hb τ i j ((hB _ _ _).1 hij))⟩
  rw [← flagPt_univGL, spMap_flagPt]
  congr 1
  funext τ
  rw [Pi.mul_apply, mul_assoc, ← hLb]
  ext i j
  rw [rowPermGL_mul_apply, GeneralLinearGroup.map_apply, GeneralLinearGroup.map_apply, rowPermGL_mul_apply,
    Equiv.symm_apply_apply]

theorem schemeDominant_cell {ι κ : Type} [Fintype ι] [Finite κ] {N : ℕ} (a : κ → ι)
    (l : κ → Fin (N + 1)) (w : ι → Equiv.Perm (Fin N)) : IsSchemeTheoreticallyDominant (cell a l w) := by
  obtain ⟨s, hs⟩ := exists_generic_comp_orbit_eq_comp_cell a l w
  have : IsSchemeTheoreticallyDominant (spMap (algebraMap (GLRing ι N) (FractionRing (GLRing ι N)))) :=
    (schemeDominant_specMap_iff (CommRingCat.ofHom _)).2 (IsFractionRing.injective _ _)
  have : IsSchemeTheoreticallyDominant (s ≫ cell a l w) :=
    ⟨by rw [← hs, ker_comp_of_schemeDominant, Scheme.Hom.ker_eq_bot]⟩
  exact schemeDominant_of_comp s _

theorem isOpenImmersion_cell (ι κ : Type) [Fintype ι] [Finite κ] (N : ℕ) (a : κ → ι) (l : κ → Fin (N + 1))
    (w : ι → Equiv.Perm (Fin N)) : IsOpenImmersion (cell a l w) := by
  have : IsImmersion (cell a l w ≫ plEmb a l) := by
    rw [cell, flagPt_plEmb]
    exact GlobalTheory.T.schubert_cell_point_immersion ι κ N a l w
  have : IsImmersion (cell a l w) := IsImmersion.of_comp _ (plEmb a l)
  have : QuasiCompact (cell a l w) := quasiCompact_of_noetherianSpace_source _
  have : IsIso (cell a l w).imageι := (isIso_imageι_iff _).2 (schemeDominant_cell a l w)
  have := isOpenImmersion_toImage (cell a l w)
  rw [← (cell a l w).toImage_imageι]
  infer_instance

end GlobalTheory
end
end
