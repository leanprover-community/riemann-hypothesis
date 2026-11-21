import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedDeterminedBySpherical
import Development.WeilBound.ThetaLifts.LocalTheory.IsArchimedeanLocalEquivariantMap
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.VaceigenDual
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDict
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitCharacterFacts
import Development.WeilBound.ThetaLifts.LocalTheory.DixmierCommutants.LocalMultiplicityOneIrreducibleGL

section
set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKG.LocalRamifiedLeviRestriction

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix
open PositivityTheory.KCo PositivityTheory.ThK
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

def lrH (P : GL (Fin n) k) (Q : GL (Fin d) k) : Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k where
  toFun Y := P.1 * Y * Q.1
  invFun Y := (P⁻¹).1 * Y * (Q⁻¹).1
  left_inv Y := by
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  right_inv Y := by
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

def chg {Z : Type} (P : GL (Fin n) k) (Q : GL (Fin d) k) (s : ℂ) (ι : (Z → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)) :
    (Z → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ) := s • (LinearMap.funLeft ℂ ℂ (lrH P Q) ∘ₗ ι)

theorem chg_apply {Z : Type} (P : GL (Fin n) k) (Q : GL (Fin d) k) (s : ℂ) (ι : (Z → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ))
    (φ : Z → ℂ) (Y : Matrix (Fin n) (Fin d) k) : chg P Q s ι φ Y = s * ι φ (P.1 * Y * Q.1) := rfl

theorem bij_smul {Z Y : Type} [TopologicalSpace Z] [TopologicalSpace Y] {ι : (Z → ℂ) →ₗ[ℂ] (Y → ℂ)}
    (hb : Set.BijOn ι (SB Z : Set _) (SB Y : Set _)) {s : ℂ} (hs : s ≠ 0) : Set.BijOn (s • ι) (SB Z : Set _) (SB Y : Set _) := by
  refine ⟨fun φ h => (SB Y).smul_mem s (hb.1 h), fun a ha b hb' e => hb.2.1 ha hb' (smul_right_injective _ hs e), fun Φ h => ?_⟩
  obtain ⟨φ, h1, h2⟩ := hb.2.2 h
  refine ⟨s⁻¹ • φ, (SB Z).smul_mem _ h1, ?_⟩
  rw [LinearMap.smul_apply, map_smul, smul_smul, mul_inv_cancel₀ hs, one_smul, h2]

variable {P g g' : GL (Fin n) k} {Q h h' : GL (Fin d) k} {ν α β : kˣ →* ℂˣ} (s : ℂ) (Φ : Matrix (Fin n) (Fin d) k → ℂ)
  (Y : Matrix (Fin n) (Fin d) k)

theorem B_left (key : (g'.1)ᵀ * P.1 = P.1 * (g.1)ᵀ) (hd : gdet g' = gdet g) :
    s * omB ν α g' 1 Φ (P.1 * Y * Q.1) = omB ν α g 1 (fun Y => s * Φ (P.1 * Y * Q.1)) Y := by
  simp only [omB, hd, map_one, Units.val_one, apow_one, Matrix.mul_one, mul_one, ← Matrix.mul_assoc, key]
  ring

theorem B_right (key : Q.1 * h'.1 = h.1 * Q.1) (hd : gdet h' = gdet h) :
    s * omB ν α 1 h' Φ (P.1 * Y * Q.1) = omB ν α 1 h (fun Y => s * Φ (P.1 * Y * Q.1)) Y := by
  simp only [omB, hd, map_one, Units.val_one, apow_one, Matrix.one_mul, one_mul, mul_one, transpose_one, Matrix.mul_assoc, key]
  ring

theorem gdet_conj (b g : GL (Fin n) k) : gdet (b⁻¹ * g * b) = gdet g := by
  rw [gdet_mul, gdet_mul, mul_right_comm, ← gdet_mul, inv_mul_cancel, gdet, map_one, one_mul]

end Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
  {ψ : AddChar (AF F) ℂ}

theorem reads_chg {ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)} {T S S'}
    (hR : Reads v ι T S) {P : GL (Fin n) (Fv F v)} {Q : GL (Fin d) (Fv F v)} {s : ℂ}
    (hS : ∀ Φ Y, s * S Φ (P.1 * Y * Q.1) = S' (fun Y => s * Φ (P.1 * Y * Q.1)) Y) : Reads v (chg P Q s ι) T S' := fun φ hφ => by
  obtain ⟨φ₁, h1, h2, h3⟩ := hR φ hφ
  refine ⟨φ₁, h1, h2, funext fun Y => ?_⟩
  rw [chg_apply, h3, hS]
  rfl

theorem comp_comp (hσ : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) : (t.comp σ).comp σ = t :=
  AlgHom.ext fun x => congrArg t (Vac.sigma_sigma hσ x)

theorem chrW_conj (hσ : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {χ : Chr F E} {K : Subgroup (AF F)ˣ} {m : ℕ} (hχ : ResEtaPow K χ m)
    (x : (Fv F v)ˣ) : chrW χ (t.comp σ) x = (chrW χ t x)⁻¹ := by
  obtain ⟨⟨sec, h⟩, -⟩ := section_statement F E σ hσ v t
  obtain ⟨⟨sec', h'⟩, -⟩ := section_statement F E σ hσ v (t.comp σ)
  obtain ⟨g, ha, h1, h2⟩ := h.exists_gl (β := Unit) (GeneralLinearGroup.scalar _ x) 1
  let z : (AE F E)ˣ := GeneralLinearGroup.det g
  have hz : (z : AE F E) = g.1 () () := det_unique _
  have za : At (evFin F v) ((z : AE F E) - 1) := by
    rw [hz]
    simpa using kd_at_matrix.1 ha () ()
  have z1 : piW t z = x := by
    rw [hz]
    simpa using congrFun (congrFun h1 ()) ()
  have z2 : piW (t.comp σ) z = 1 := by
    rw [hz]
    simpa using congrFun (congrFun h2 ()) ()
  let z' : (AE F E)ˣ := Units.map (cA σ : AE F E →* AE F E) z
  have a1 := (h.idele z x za z1 z2).1 χ
  have a2 := (h'.idele z' x (by simpa [z'] using h.atConj _ za) ((h.conj _).2.trans z1)
    (by rw [comp_comp hσ]; exact (h.conj _).1.trans z2)).1 χ
  have a3 := hχ (Units.map (Algebra.norm (AF F) : AE F E →* AF F) z)
  rw [if_pos (Subgroup.mem_sup_right (MonoidHom.mem_range.2 ⟨z, rfl⟩)), show Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E)
    (Units.map (Algebra.norm (AF F) : AE F E →* AF F) z) = z * z' from Units.ext (GlobalTheory.Doubling.algebraMap_norm_eq hσ _),
    map_mul, Circle.coe_mul, a1, a2] at a3
  exact eq_inv_of_mul_eq_one_right (Units.ext a3)

theorem chrW_div (χ χ' : Chr F E) (t : E →ₐ[F] Fv F v) (x : (Fv F v)ˣ) : chrW (χ / χ') t x = chrW χ t x / chrW χ' t x :=
  map_div Circle.toUnits _ _

end PositivityTheory.ThKG.LocalRamifiedLeviRestriction
end
end

section
noncomputable section

namespace PositivityTheory.ThKG.LocalRamifiedLeviRestriction

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix GlobalTheory.ThK
open PositivityTheory.KCo PositivityTheory.ThK PositivityTheory.ThK.SplitAsm ValuativeRel
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H : Plane E d d₁}
  (e : Fin d₁ ⊕ Bool ≃ Fin d)

theorem idele_one (hσ : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (x : (Fv F v)ˣ) (hx : valuation (Fv F v) (x : Fv F v) = 1) :
    ∃ z : (AE F E)ˣ, At (evFin F v) ((z : AE F E) - 1) ∧ piW t z = x ∧ piW (t.comp σ) z = 1 ∧ absE F E z = 1 ∧
      ∀ χ : Chr F E, (χ z : ℂ) = chrW χ t x := by
  obtain ⟨⟨sec, h⟩, -⟩ := section_statement F E σ hσ v t
  obtain ⟨g, ha, h1, h2⟩ := h.exists_gl (β := Unit) (GeneralLinearGroup.scalar _ x) 1
  let z : (AE F E)ˣ := GeneralLinearGroup.det g
  have hz : (z : AE F E) = g.1 () () := det_unique _
  have za : At (evFin F v) ((z : AE F E) - 1) := by
    rw [hz]
    simpa using kd_at_matrix.1 ha () ()
  have z1 : piW t z = x := by
    rw [hz]
    simpa using congrFun (congrFun h1 ()) ()
  have z2 : piW (t.comp σ) z = 1 := by
    rw [hz]
    simpa using congrFun (congrFun h2 ()) ()
  refine ⟨z, za, z1, z2, ?_, (h.idele z x za z1 z2).1⟩
  have e1 : z = GlobalTheory.Doubling.ideleAt F E v (GlobalTheory.Doubling.unitFin F E v z) := Units.ext (by
    change (z : AE F E) = 1 - GlobalTheory.EmbChart.tensAt E v 1 + GlobalTheory.EmbChart.tensAt E v (compFin F E v z)
    have o := off_of_at za
    rw [← PositivityTheory.Member.ZakTransform.ep_smul, ← map_one (compFin F E v), ← PositivityTheory.Member.ZakTransform.ep_smul]
    rw [sub_smul, sub_smul, one_smul, one_smul] at o
    rw [← o, sub_add_cancel])
  have n1 : evFin F v (Algebra.norm (AF F) (z : AE F E)) = x := by
    rw [norm_eq hσ t za z1 z2, map_add, map_sub, map_one, ev_sgl, ev_sgl, sub_self, zero_add]
  rw [e1, GlobalTheory.Doubling.absE_ideleAt, GlobalTheory.Doubling.absEv_unitFin, n1]
  have := (val_eq_one_iff _).1 hx
  exact NNReal.eq (le_antisymm (Valued.toNormedField.norm_le_one_iff.2 this.le) (Valued.toNormedField.one_le_norm_iff.2 this.ge))

theorem idele_two (hσ : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (x y : (Fv F v)ˣ) (hx : valuation (Fv F v) (x : Fv F v) = 1)
    (hy : valuation (Fv F v) (y : Fv F v) = 1) :
    ∃ z : (AE F E)ˣ, At (evFin F v) ((z : AE F E) - 1) ∧ piW t z = x ∧ piW (t.comp σ) z = (y⁻¹ : (Fv F v)ˣ) ∧ absE F E z = 1 ∧
      ∀ (χ : Chr F E) (K : Subgroup (AF F)ˣ) (m : ℕ), ResEtaPow K χ m → (χ z : ℂ) = chrW χ t (x * y) := by
  obtain ⟨z, a1, a2, a3, a4, a5⟩ := idele_one hσ t x hx
  obtain ⟨w, b1, b2, b3, b4, b5⟩ := idele_one hσ (t.comp σ) y⁻¹ (by simp [hy])
  rw [comp_comp hσ] at b3
  refine ⟨z * w, ?_, by simp [a2, b3], by simp [a3, b2], by simp [a4, b4], fun χ K m hχ => ?_⟩
  · have : ((z * w : (AE F E)ˣ) : AE F E) - 1 = (z - 1) * w + (w - 1) := by push_cast; ring
    rw [this]
    exact At.kd_add (fun u hu => by rw [← smul_mul_assoc, a1 u hu, zero_mul]) b1
  · rw [map_mul, Circle.coe_mul, a5, b5, chrW_conj hσ t hχ, map_mul, map_inv, inv_inv, Units.val_mul]

variable (H) in

def fr : Matrix (Fin d) (Fin d) E := Matrix.of fun i c => Sum.elim (H.ι i) (fun b => cond b (H.y i) (H.x i)) (e.symm c)

variable (W₁) in

def gm : Matrix (Fin d) (Fin d) E := reindex e e (fromBlocks W₁.J 0 0 (Matrix.of fun b b' => cond b (cond b' 0 (-1)) (cond b' 1 0)))

variable {e}

theorem form_swap (hσ : IsCMExt F E σ) (hs : ∀ i j, σ (W.J j i) = -W.J i j) (x y : Fin d → E) : form σ W.J y x = -σ (form σ W.J x y) := by
  simp only [form, dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum, hs, Vac.sigma_sigma hσ, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem fr_gram (hσ : IsCMExt F E σ) {B : Base F E} {i₀ i₁} (hH : H.IsAdapted σ B W W₁ i₀ i₁) (hs : ∀ i j, σ (W.J j i) = -W.J i j) :
    (fr H e)ᵀ * W.J * (fr H e).map σ = gm W₁ e := by
  have k : ∀ a b, ((fr H e)ᵀ * W.J * (fr H e).map σ) a b = form σ W.J (fun i => fr H e i a) fun i => fr H e i b := fun a b => by
    rw [Matrix.mul_assoc]; rfl
  have c : ∀ s, (fun i => H.ι i s) = H.ι *ᵥ Pi.single s 1 := fun s => by rw [mulVec_single_one]; rfl
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  rw [k]
  rcases a with s | _ | _ <;> rcases b with s' | _ | _ <;> simp only [fr, gm, of_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr,
    cond, reindex_apply, submatrix_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply]
  · rw [← hH.gram, Matrix.mul_assoc]; rfl
  · rw [c]; exact (hH.orth _).1
  · rw [c]; exact (hH.orth _).2
  · rw [c, form_swap hσ hs, show form σ W.J (H.ι *ᵥ Pi.single s' 1) (fun i => H.x i) = 0 from (hH.orth _).1, map_zero, neg_zero]
  · exact hH.xx
  · exact hH.xy
  · rw [c, form_swap hσ hs, show form σ W.J (H.ι *ᵥ Pi.single s' 1) (fun i => H.y i) = 0 from (hH.orth _).2, map_zero, neg_zero]
  · rw [form_swap hσ hs]; simp [hH.xy]
  · exact hH.yy

theorem gm_det (h : IsUnit W₁.J.det) : IsUnit (gm W₁ e).det := by
  rw [gm, det_reindex_self, det_fromBlocks_zero₂₁]
  refine h.mul (isUnit_iff_ne_zero.2 ?_)
  rw [← det_reindex_self finTwoEquiv.symm, det_fin_two]
  simp [finTwoEquiv]

structure Fr (σ : E →ₐ[F] E) (t : E →ₐ[F] Fv F v) (W : Spc F E d) (W₁ : Spc F E d₁) (H : Plane E d d₁) (e : Fin d₁ ⊕ Bool ≃ Fin d)
    (C : GL (Fin d) (Fv F v)) : Prop where
  val : C.val = (fr H e).map t
  gram : (fr H e)ᵀ * W.J * (fr H e).map σ = gm W₁ e
  det : IsUnit W.J.det

theorem col_eq (h : IsSec σ t sec) {C} (hC : Fr σ t W W₁ H e C) {g : UA σ W.J} (hg : g ∈ UAt σ W (evFin F v)) {p : GL (Fin d) (Fv F v)}
    (hp : (mat g).map (piW t) = (C * p * C⁻¹).val) (c : Fin d) (ω : Fin d → AE F E) (ha : At (evFin F v) (ω - Pi.single c 1))
    (h1 : ∀ i, piW t (ω i) = p.val i c)
    (h2 : p.valᵀ *ᵥ ((gm W₁ e).map t *ᵥ fun i => piW (t.comp σ) (ω i)) = fun i => t (gm W₁ e i c)) :
    mat g *ᵥ (fun i => incM F (fr H e) i c) = incM F (fr H e) *ᵥ ω := by
  have m2 : (incM F (fr H e)).map (piW (t.comp σ)) = ((fr H e).map σ).map t := Matrix.ext fun i j => incM_map' h _ i j
  have e0 : (fun i => incM F (fr H e) i c) = incM F (fr H e) *ᵥ Pi.single c 1 := by rw [mulVec_single_one]; rfl
  have a1 : At (evFin F v) (mat g *ᵥ (fun i => incM F (fr H e) i c) - incM F (fr H e) *ᵥ ω) := fun u hu => by
    have : mat g *ᵥ (fun i => incM F (fr H e) i c) - incM F (fr H e) *ᵥ ω =
        (mat g - 1) *ᵥ (fun i => incM F (fr H e) i c) - incM F (fr H e) *ᵥ (ω - Pi.single c 1) := by
      rw [sub_mulVec, one_mulVec, mulVec_sub, ← e0]; abel
    rw [this, smul_sub, ← smul_mulVec, hg u hu, ← mulVec_smul, ha u hu]
    simp
  have G : C.valᵀ * W.J.map t * ((fr H e).map σ).map t = (gm W₁ e).map t := by
    rw [← hC.gram, Matrix.map_mul, Matrix.map_mul, hC.val, transpose_map]
  have u1 : ((mat g).map (piW t))ᵀ * W.J.map t * (mat g).map (piW (t.comp σ)) = W.J.map t := by
    have := h.unit_rel g
    rwa [incM_map h] at this
  have c1 : (mat g).map (piW t) *ᵥ (fun i => C.val i c) = C.val *ᵥ fun i => piW t (ω i) := by
    have : (fun i => C.val i c) = C.val *ᵥ Pi.single c 1 := by rw [mulVec_single_one]; rfl
    rw [hp, this, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul, ← mulVec_mulVec, mulVec_single_one]
    exact congrArg _ (funext fun i => (h1 i).symm)
  have c2 : (mat g).map (piW (t.comp σ)) *ᵥ (fun i => (((fr H e).map σ).map t) i c) =
      ((fr H e).map σ).map t *ᵥ fun i => piW (t.comp σ) (ω i) := by
    have un : IsUnit (p.valᵀ * C.valᵀ * W.J.map t) :=
      (((isUnit_transpose _).2 p.isUnit).mul ((isUnit_transpose _).2 C.isUnit)).mul
        (((isUnit_iff_isUnit_det _).2 hC.det).map (t : E →+* Fv F v).mapMatrix)
    apply mulVec_injective_iff_isUnit.2 un
    have : p.valᵀ * C.valᵀ = C.valᵀ * ((mat g).map (piW t))ᵀ := by
      rw [← transpose_mul, ← transpose_mul, hp, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]
    have e2 : (fun i => (((fr H e).map σ).map t) i c) = ((fr H e).map σ).map t *ᵥ Pi.single c 1 := by rw [mulVec_single_one]; rfl
    have k1 : p.valᵀ * C.valᵀ * W.J.map t * (mat g).map (piW (t.comp σ)) * ((fr H e).map σ).map t = (gm W₁ e).map t := by
      rw [this, Matrix.mul_assoc C.valᵀ, Matrix.mul_assoc C.valᵀ, u1, G]
    have k2 : p.valᵀ * C.valᵀ * W.J.map t * ((fr H e).map σ).map t = p.valᵀ * (gm W₁ e).map t := by
      rw [← G]; simp only [Matrix.mul_assoc]
    rw [e2]
    simp only [mulVec_mulVec, ← Matrix.mul_assoc]
    rw [k1, k2, ← mulVec_mulVec, h2, mulVec_single_one]
    rfl
  funext i
  refine sub_eq_zero.1 (h.ext _ (fun u hu => congrFun (a1 u hu) i) ?_ ?_)
  · rw [map_sub, RingHom.map_mulVec, RingHom.map_mulVec, incM_map h, ← hC.val, sub_eq_zero]
    refine Eq.trans ?_ (congrFun c1 i)
    congr 1
    funext j
    rw [hC.val, ← incM_map h]; rfl
  · rw [map_sub, RingHom.map_mulVec, RingHom.map_mulVec, m2, sub_eq_zero]
    refine Eq.trans ?_ (congrFun c2 i)
    congr 1
    funext j
    rw [← m2]; rfl

theorem sum_e' {R : Type} [AddCommMonoid R] (a : Fin d → R) : ∑ j, a j = ∑ s, a (e (.inl s)) + (a (e (.inr true)) + a (e (.inr false))) := by
  rw [← e.sum_comp, Fintype.sum_sum_type, Fintype.sum_bool]

theorem fr_mulVec (ω : Fin d → AE F E) : incM F (fr H e) *ᵥ ω = incM F H.ι *ᵥ (fun s => ω (e (.inl s))) +
    (ω (e (.inr true)) • incV F H.y + ω (e (.inr false)) • incV F H.x) := by
  funext i
  simp only [mulVec, dotProduct]
  rw [sum_e' (e := e)]
  simp [incM, incV, fr, mul_comm, mulVec, dotProduct]

theorem fr_col (c : Fin d₁ ⊕ Bool) : (fun i => incM F (fr H e) i (e c)) =
    Sum.elim (fun s i => incM F H.ι i s) (fun b => cond b (incV F H.y) (incV F H.x)) c := by
  funext i
  rcases c with s | _ | _ <;> simp [incM, incV, fr]

theorem at_single (c c' : Fin d) {a : AE F E} (ha : At (evFin F v) a) :
    At (evFin F v) ((Pi.single c 1 + Pi.single c' a : Fin d → AE F E) - Pi.single c 1) := fun u hu => by
  rw [add_sub_cancel_left, ← Pi.single_smul, ha u hu, Pi.single_zero]

theorem mem_unip (h : IsSec σ t sec) {C} (hC : Fr σ t W W₁ H e C) {g : UA σ W.J} (hg : g ∈ UAt σ W (evFin F v)) {p : GL (Fin d) (Fv F v)}
    (hp : (mat g).map (piW t) = (C * p * C⁻¹).val) (p1 : ∀ i, p.val i (e (.inr false)) = if i = e (.inr false) then 1 else 0)
    (p2 : p.val (e (.inr true)) (e (.inr true)) = 1) (p3 : ∀ s s', p.val (e (.inl s)) (e (.inl s')) = if s = s' then 1 else 0)
    (p4 : ∀ s, p.val (e (.inr true)) (e (.inl s)) = 0) : g ∈ unip σ W H := by
  refine Subgroup.subset_closure ⟨?_, fun z => ?_⟩
  · have := col_eq h hC hg hp (e (.inr false)) (Pi.single (e (.inr false)) 1) (fun u _ => by simp) (fun i => by
      rw [p1, Pi.single_apply]; split_ifs <;> simp) (by
      funext i
      obtain ⟨i, rfl⟩ := e.surjective i
      simp only [mulVec, dotProduct, sum_e' (e := e)]
      rcases i with s | _ | _ <;> simp [gm, p1, p2, p4])
    rw [fr_col, fr_mulVec] at this
    simpa [← Pi.zero_def] using this
  · have k : ∀ s, ∃ a : AE F E, mat g *ᵥ (fun i => incM F H.ι i s) = (fun i => incM F H.ι i s) + a • incV F H.x := fun s => by
      let a := sec (p.val (e (.inr false)) (e (.inl s)), ∑ s', p.val (e (.inl s')) (e (.inr true)) * t (W₁.J s' s))
      have := col_eq h hC hg hp (e (.inl s)) (Pi.single (e (.inl s)) 1 + Pi.single (e (.inr false)) a) (at_single _ _ (h.at' _)) (fun i => by
        obtain ⟨i, rfl⟩ := e.surjective i
        rcases i with s' | _ | _
        · by_cases hs : s' = s <;> simp [p3, hs]
        · simp [a, h.fst]
        · simp [p4]) (by
        funext i
        obtain ⟨i, rfl⟩ := e.surjective i
        simp only [mulVec, dotProduct, sum_e' (e := e)]
        rcases i with s' | _ | _ <;> simp [gm, p1, p2, p3, p4, a, h.snd, Pi.single_apply, apply_ite])
      rw [fr_col, fr_mulVec] at this
      refine ⟨a, this.trans ?_⟩
      funext i
      simp [mulVec, dotProduct, Pi.single_apply]
    choose a ha using k
    refine ⟨∑ s, z s * a s, ?_⟩
    have e1 : incM F H.ι *ᵥ z = ∑ s, z s • fun i => incM F H.ι i s := by
      funext i; simp [mulVec, dotProduct, mul_comm]
    rw [e1, mulVec_sum, Finset.sum_smul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by rw [mulVec_smul, ha, smul_add, smul_smul]

variable (e) in

def bl {k : Type} [Field k] (g : Matrix (Fin d₁) (Fin d₁) k) (x y : k) : Matrix (Fin d) (Fin d) k :=
  reindex e e (fromBlocks g 0 0 (diagonal fun b => cond b y x))

theorem usage₄ {k : Type} [Field k] (g : Matrix (Fin d₁) (Fin d₁) k) (x y : k) : (bl e g x y).det = g.det * (x * y) := by
  rw [bl, det_reindex_self, det_fromBlocks_zero₂₁, det_diagonal, Fintype.prod_bool, mul_comm x]
  rfl

theorem is_levi (h : IsSec σ t sec) {C} (hC : Fr σ t W W₁ H e C) {g : UA σ W.J} (hg : g ∈ UAt σ W (evFin F v)) {p : GL (Fin d) (Fv F v)}
    (hp : (mat g).map (piW t) = (C * p * C⁻¹).val) {g₁ : UA σ W₁.J} (hg₁ : g₁ ∈ UAt σ W₁ (evFin F v)) {x y : (Fv F v)ˣ}
    (pe : p.val = bl e ((mat g₁).map (piW t)) x y) {z : (AE F E)ˣ} (za : At (evFin F v) ((z : AE F E) - 1)) (z1 : piW t z = x)
    (z2 : piW (t.comp σ) z = (y⁻¹ : (Fv F v)ˣ)) : IsLevi H z g₁ g := by
  have i1 : piW t (z⁻¹).val = (x⁻¹ : (Fv F v)ˣ) := by
    rw [Units.val_inv_eq_inv_val, ← z1]; exact eq_inv_of_mul_eq_one_left (by rw [← map_mul]; simp)
  have i2 : piW (t.comp σ) (z⁻¹).val = y := by
    have : piW (t.comp σ) (z⁻¹).val * piW (t.comp σ) z = 1 := by rw [← map_mul]; simp
    rw [z2] at this
    simpa using eq_inv_of_mul_eq_one_left this
  have sg : ∀ (c : Fin d) (a : AE F E), At (evFin F v) (a - 1) →
      At (evFin F v) ((Pi.single c a : Fin d → AE F E) - Pi.single c 1) := fun c a ha u hu => by
    rw [← Pi.single_sub, ← Pi.single_smul, ha u hu, Pi.single_zero]
  refine ⟨?_, ?_, ?_⟩
  · have := col_eq h hC hg hp (e (.inr false)) (Pi.single (e (.inr false)) z) (sg _ _ za) (fun i => by
      obtain ⟨i, rfl⟩ := e.surjective i
      rcases i with s | _ | _ <;> simp [pe, bl, z1]) (by
      funext i
      obtain ⟨i, rfl⟩ := e.surjective i
      simp only [mulVec, dotProduct, sum_e' (e := e)]
      rcases i with s | _ | _ <;> simp [gm, pe, bl, z2])
    rw [fr_col, fr_mulVec] at this
    simpa [← Pi.zero_def] using this
  · have a2 : At (evFin F v) (cA σ (z⁻¹).val - 1) := by
      have : At (evFin F v) ((z⁻¹).val - 1) := fun u hu => by
        rw [show (z⁻¹).val - 1 = -((z.val - 1) * (z⁻¹).val) by rw [sub_mul]; simp, smul_neg, ← smul_mul_assoc, za u hu]; simp
      simpa using h.atConj _ this
    have := col_eq h hC hg hp (e (.inr true)) (Pi.single (e (.inr true)) (cA σ (z⁻¹).val)) (sg _ _ a2) (fun i => by
      obtain ⟨i, rfl⟩ := e.surjective i
      rcases i with s | _ | _ <;> simp [pe, bl, (h.conj _).1, i2]) (by
      funext i
      obtain ⟨i, rfl⟩ := e.surjective i
      simp only [mulVec, dotProduct, sum_e' (e := e)]
      rcases i with s | _ | _ <;> simp [gm, pe, bl, (h.conj _).2, i1])
    rw [fr_col, fr_mulVec] at this
    simpa [← Pi.zero_def] using this
  · have u1 := h.unit_rel g₁
    rw [incM_map h] at u1
    ext i s
    have := col_eq h hC hg hp (e (.inl s)) (fun c => Sum.elim (fun s' => mat g₁ s' s) 0 (e.symm c)) (fun u hu => by
      funext c
      obtain ⟨c, rfl⟩ := e.surjective c
      rcases c with s' | b
      · simpa [Matrix.one_apply, Pi.single_apply] using congrFun (congrFun (hg₁ u hu) s') s
      · simp) (fun i => by
      obtain ⟨i, rfl⟩ := e.surjective i
      rcases i with s | _ | _ <;> simp [pe, bl]) (by
      funext i
      obtain ⟨i, rfl⟩ := e.surjective i
      simp only [mulVec, dotProduct, sum_e' (e := e)]
      rcases i with s' | _ | _
      · have := congrFun (congrFun u1 s') s
        rw [Matrix.mul_assoc] at this
        simpa [gm, pe, bl, Matrix.mul_apply, mat] using this
      · simp [gm, pe, bl]
      · simp [gm, pe, bl])
    rw [fr_col, fr_mulVec] at this
    simpa [Matrix.mul_apply, mulVec, dotProduct] using congrFun this i

end PositivityTheory.ThKG.LocalRamifiedLeviRestriction
end
end

section
noncomputable section

namespace PositivityTheory.ThKG.LocalRamifiedLeviRestriction

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix GlobalTheory.ThK
open PositivityTheory.KCo PositivityTheory.ThK PositivityTheory.ThK.SplitAsm ValuativeRel PositivityTheory.ThKG.Loc
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem inP_det {k : Type} [Field k] [ValuativeRel k] {d d₁ : ℕ} {e : Fin d₁ ⊕ Bool ≃ Fin d} {h : Matrix (Fin d) (Fin d) k} (hh : InP e h) :
    h.det = h (e (.inr false)) (e (.inr false)) * h (e (.inr true)) (e (.inr true)) := by
  obtain ⟨p1, -, -, p3, p4⟩ := hh
  have e1 : h.submatrix e e = fromBlocks 1 (h.submatrix e e).toBlocks₁₂ (h.submatrix e e).toBlocks₂₁ (h.submatrix e e).toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks (h.submatrix e e)]
    congr 1
    ext s s'
    exact p3 s s'
  rw [← det_submatrix_equiv_self e, e1, det_fromBlocks_one₁₁, ← det_reindex_self finTwoEquiv.symm, det_fin_two]
  simp [finTwoEquiv, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, Matrix.mul_apply, p1, p4]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

structure Eqv (om : Rep σ X W) (H : Plane E d d₁) (χ : Chr F E) (r : ℝ) {P : Type} [AddCommGroup P] [Module ℂ P]
    (τ : UA σ W₁.J → Module.End ℂ P) (Λ : Fl F v n d →ₗ[ℂ] P) : Prop where
  aug : augAt om v ≤ LinearMap.ker Λ
  act : ∀ t h₁ m, IsLevi H t h₁ m → h₁ ∈ UAt σ W₁ (evFin F v) → ∀ u ∈ unip σ W H, u ∈ UAt σ W (evFin F v) → m ∈ UAt σ W (evFin F v) →
    ∀ φ ∈ SB _, ∀ φ' ∈ SB _, Acts (evFin F v) (om (1, u * m)) φ φ' →
      Λ φ' = ((χ t : ℂ) * (((absE F E t : ℝ) ^ r : ℝ) : ℂ)) • τ h₁ (Λ φ)

theorem one_UAt {m : ℕ} (Y : Spc F E m) : (1 : UA σ Y.J) ∈ UAt σ Y (evFin F v) := fun u _ => by
  rw [show mat (1 : UA σ Y.J) = 1 from rfl, sub_self, smul_zero]

theorem mul_UAt {m : ℕ} {Y : Spc F E m} {g g' : UA σ Y.J} (h : g ∈ UAt σ Y (evFin F v)) (h' : g' ∈ UAt σ Y (evFin F v)) :
    g * g' ∈ UAt σ Y (evFin F v) := fun u hu => by
  rw [show mat (g * g') - 1 = (mat g - 1) * mat g' + (mat g' - 1) by rw [show mat (g * g') = mat g * mat g' from rfl]; noncomm_ring,
    smul_add, ← Matrix.smul_mul, h u hu, h' u hu]
  simp

theorem ua_ext {t : E →ₐ[F] Fv F v} {sec} (h : IsSec σ t sec) (hJ : IsUnit W.J.det) {g g' : UA σ W.J} (hg : g ∈ UAt σ W (evFin F v))
    (hg' : g' ∈ UAt σ W (evFin F v)) (e : (mat g).map (piW t) = (mat g').map (piW t)) : g = g' := by
  have u1 : ((mat g).map (piW t))ᵀ * W.J.map t * (mat g).map (piW (t.comp σ)) = W.J.map t := by
    have := h.unit_rel g
    rwa [incM_map h] at this
  have u2 : ((mat g').map (piW t))ᵀ * W.J.map t * (mat g').map (piW (t.comp σ)) = W.J.map t := by
    have := h.unit_rel g'
    rwa [incM_map h] at this
  have un : IsUnit (((mat g).map (piW t))ᵀ * W.J.map t) :=
    ((isUnit_transpose _).2 (GeneralLinearGroup.map (piW t) g.1).isUnit).mul
      (((isUnit_iff_isUnit_det _).2 hJ).map (t : E →+* Fv F v).mapMatrix)
  refine Subtype.ext (Units.ext (h.extM (z := mat g) (z' := mat g') (fun u hu => ?_) e (un.mul_left_cancel (by rw [u1, e, u2]))))
  rw [show mat g - mat g' = (mat g - 1) - (mat g' - 1) by abel, smul_sub, hg u hu, hg' u hu, sub_zero]

theorem pair_multiplicity_one_ramified (hBe : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) {B : Base F E} (hB : B.IsGood σ) {r₁ s₁ r₂ s₂ r₃ s₃ : ℕ}
    (hX : X.IsHerm σ B r₁ s₁) (hW : W.IsSkew σ B r₂ s₂) (hW₁ : W₁.IsSkew σ B r₃ s₃) {M : Model σ X W} {om : Rep σ X W} {χX χW : Chr F E}
    (hom : M.IsWeil B.ψ χX χW om) (hk : IsHecke F E χW) {K : Subgroup (AF F)ˣ} {m : ℕ} (res : ResEtaPow K χX m) {H : Plane E d d₁} {i₀ i₁}
    (hH : H.IsAdapted σ B W W₁ i₀ i₁) (t : E →ₐ[F] Fv F v) (ram : ¬ GlobalTheory.SplitWeil.IsUnram (chrW χW t)) (hn : n ≤ d₁)
    (hS : ∀ h₀ : GL (Fin d₁) (Fv F v), ∃ h ∈ UAt σ W₁ (evFin F v), (mat h).map (piW t) = h₀)
    {P : Type} [AddCommGroup P] [Module ℂ P] {τ : UA σ W₁.J → Module.End ℂ P} (τ1 : τ 1 = 1) (hr : Module.rank ℂ P ≤ Cardinal.aleph0)
    (hi : ∀ N : Submodule ℂ P, (∀ h ∈ UAt σ W₁ (evFin F v), ∀ x ∈ N, τ h x ∈ N) → N = ⊥ ∨ N = ⊤) {r : ℝ} {Λ Λ' : Fl F v n d →ₗ[ℂ] P}
    (hΛ : Eqv om H χX r τ Λ) (hΛ' : Eqv om H χX r τ Λ') (h0 : ∃ φ ∈ SB _, Λ φ ≠ 0) : ∃ c : ℂ, ∀ φ ∈ SB _, Λ' φ = c • Λ φ := by
  obtain ⟨⟨sec, h⟩, hu⟩ := section_statement F E σ hB.cm v t
  obtain ⟨⟨ι₀, hι⟩, sX, sW, k⟩ := dictionary_extended F E σ n d B X W M om χX χW hB ⟨_, _, hX⟩ ⟨_, _, hW⟩ hom v t
  obtain ⟨kX, kW⟩ := k ι₀ hι
  let e : Fin d₁ ⊕ Bool ≃ Fin d := Fintype.equivFinOfCardEq (by simp [hH.rank])
  have gr := fr_gram (e := e) hB.cm hH hW.skew
  have dC : ((fr H e).map t).det ≠ 0 := by
    have := congrArg det gr
    rw [det_mul, det_mul, det_transpose] at this
    have h1 : (fr H e).det ≠ 0 := fun h' => (gm_det (e := e) (Vac.skew_det hW₁)).ne_zero (by rw [← this, h', zero_mul, zero_mul])
    rw [show (fr H e).map t = (t : E →+* Fv F v).mapMatrix (fr H e) from rfl, ← RingHom.map_det]
    exact (map_ne_zero _).2 h1
  let C : GL (Fin d) (Fv F v) := GeneralLinearGroup.mkOfDetNeZero _ dC
  have hC : Fr σ t W W₁ H e C := ⟨rfl, gr, Vac.skew_det hW⟩
  let ι := chg 1 C⁻¹ 1 ι₀
  have bij : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _) :=
    bij_smul (bij_comp hι.bij (lrH 1 C⁻¹)) one_ne_zero
  have rX : ∀ g₀ : GL (Fin n) (Fv F v), ∃ g ∈ UAt σ X (evFin F v), Reads v ι (om (g, 1)) (omB (chrW χW t) (chrW χX t) g₀ 1) := fun g₀ =>
    let ⟨g, hg, e1⟩ := sX g₀
    ⟨g, hg, reads_chg (kX g hg g₀ e1) fun Φ Y => B_left _ Φ Y (by simp) rfl⟩
  have rW : ∀ g ∈ UAt σ W (evFin F v), ∀ p : GL (Fin d) (Fv F v), (mat g).map (piW t) = (C * p * C⁻¹).val →
      Reads v ι (om (1, g)) (omB (chrW χW t) (chrW χX t) 1 p) := fun g hg p e1 =>
    reads_chg (kW g hg _ e1) fun Φ Y => B_right _ Φ Y (by rw [← Units.val_mul, ← Units.val_mul, mul_assoc C, inv_mul_cancel_left])
      (by simpa using gdet_conj C⁻¹ p)
  obtain ⟨s, hs⟩ := (ι ∘ₗ (SB _).subtype).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 fun a b hab =>
    Subtype.ext (bij.injOn a.2 b.2 hab))
  have s1 : ∀ φ ∈ SB _, (s (ι φ)).1 = φ := fun φ hφ => congrArg Subtype.val (LinearMap.congr_fun hs ⟨φ, hφ⟩)
  have rd : ∀ {T S}, Reads v ι T S → ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), S Φ ∈ SB _ ∧
      Acts (evFin F v) T (s Φ).1 (s (S Φ)).1 := fun {T S} hR Φ hΦ => by
    obtain ⟨φ, hφ, rfl⟩ := bij.surjOn hΦ
    obtain ⟨φ₁, h1, h2, h3⟩ := hR φ hφ
    rw [← h3, s1 φ hφ, s1 φ₁ h1]
    exact ⟨bij.mapsTo h1, h2⟩
  have eo : ∀ (p : GL (Fin d) (Fv F v)) (Φ : Matrix (Fin n) (Fin d) (Fv F v) → ℂ), omB (chrW χW t) (chrW χX t) 1 p Φ =
      ((chrW χX t (gdet p) : ℂ) * apow (gdet p) ((n : ℂ) / 2)) • fun Y : Matrix (Fin n) (Fin d) (Fv F v) => Φ (Y * p.val) := fun p Φ => by
    funext Y
    simp [omB]
  have c0 : ∀ p : GL (Fin d) (Fv F v), ((chrW χX t (gdet p) : ℂ) * apow (gdet p) ((n : ℂ) / 2)) ≠ 0 := fun p =>
    mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)
  have inv : ∀ {Λ : Fl F v n d →ₗ[ℂ] P}, Eqv om H χX r τ Λ → Inv e (chrW χW t) (Λ ∘ₗ (SB _).subtype ∘ₗ s) := fun {Λ} hΛ => by
    refine ⟨fun g₀ Φ hΦ => ?_, fun a ha Φ hΦ => ?_⟩
    · obtain ⟨g, hg, hR⟩ := rX g₀
      have e1 : omB (chrW χW t) 1 g₀ 1 Φ = omB (chrW χW t) (chrW χX t) g₀ 1 Φ := by
        funext Y
        simp [omB]
      have := hΛ.aug (Submodule.subset_span ⟨g, hg, _, (s Φ).2, _, (s _).2, (rd hR Φ hΦ).2, rfl⟩)
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
      rw [e1]
      exact this
    · have da := inP_det ha
      obtain ⟨p1, p2, p3, p4, p5⟩ := ha
      have x0 : a (e (.inr false)) (e (.inr false)) ≠ 0 := fun h => by simp [h] at p2
      have y0 : a (e (.inr true)) (e (.inr true)) ≠ 0 := fun h => by simp [h] at p3
      let x := Units.mk0 _ x0
      let y := Units.mk0 _ y0
      let p : GL (Fin d) (Fv F v) := GeneralLinearGroup.mkOfDetNeZero a (da ▸ mul_ne_zero x0 y0)
      let pm : GL (Fin d) (Fv F v) := GeneralLinearGroup.mkOfDetNeZero (bl e 1 x.val y.val) (by rw [usage₄]; simp)
      have im : (pm⁻¹).val = bl e 1 (x⁻¹).val (y⁻¹).val := by
        refine Units.inv_eq_of_mul_eq_one_right ?_
        ext i j
        obtain ⟨i, rfl⟩ := e.surjective i
        obtain ⟨j, rfl⟩ := e.surjective j
        rw [Matrix.mul_apply, sum_e' (e := e)]
        rcases i with i | _ | _ <;> rcases j with j | _ | _ <;> simp [pm, bl, Matrix.one_apply]
      have pu : ∀ i j, (p * pm⁻¹).val i (e j) = a i (e j) * Sum.elim (fun _ => 1) (fun b => cond b (y⁻¹).val (x⁻¹).val) j := fun i j => by
        rw [Units.val_mul, im, Matrix.mul_apply, sum_e' (e := e)]
        rcases j with j | _ | _ <;> simp [p, bl, Matrix.one_apply]
      obtain ⟨u, hu1, hu2⟩ := sW (C * (p * pm⁻¹) * C⁻¹)
      obtain ⟨m', hm1, hm2⟩ := sW (C * pm * C⁻¹)
      obtain ⟨z, z1, z2, z3, z4, z5⟩ := idele_two hB.cm t x y p2 p3
      have un := mem_unip h hC hu1 hu2 (fun i => by
        rw [pu]; split_ifs with hi
        · simp [hi, x, x0]
        · simp [p1 i hi]) (by rw [pu]; simp [y, y0]) (fun s s' => by rw [pu, p4, Matrix.one_apply]; simp) (fun s => by rw [pu, p5]; simp)
      have lv := is_levi h hC hm1 hm2 (one_UAt W₁) (x := x) (y := y) (by
        rw [show mat (1 : UA σ W₁.J) = 1 from rfl, Matrix.map_one _ (map_zero _) (map_one _)]; rfl) z1 z2 z3
      have hR := rW (u * m') (mul_UAt hu1 hm1) p (by
        rw [show mat (u * m') = mat u * mat m' from rfl, Matrix.map_mul, hu2, hm2, ← Units.val_mul]; congr 1; group)
      obtain ⟨q1, q2⟩ := rd hR Φ hΦ
      have := hΛ.act z 1 m' lv (one_UAt W₁) u un hu1 hm1 _ (s Φ).2 _ (s _).2 q2
      have dp : gdet p = x * y := Units.ext da
      have ap : apow (x * y) ((n : ℂ) / 2) = 1 := apow_of_valuation_eq_one (by simp [x, y, p2, p3]) _
      rw [eo] at q1 this
      rw [map_smul, Submodule.coe_smul, map_smul, dp, ap, z4, z5 _ _ _ res, τ1] at this
      refine ⟨(Submodule.smul_mem_iff _ (c0 p)).1 q1, ?_⟩
      have h9 : Λ (s fun Y : Matrix (Fin n) (Fin d) (Fv F v) => Φ (Y * p.val)).1 = Λ (s Φ).1 := by simpa using this
      exact h9
  choose sc sc1 sc2 using hS
  have bd : ∀ g : GL (Fin d₁) (Fv F v), (bl e g.val 1 1).det ≠ 0 := fun g => by
    rw [usage₄, mul_one, mul_one]; exact g.det_ne_zero
  let pb : GL (Fin d₁) (Fv F v) → GL (Fin d) (Fv F v) := fun g => GeneralLinearGroup.mkOfDetNeZero _ (bd g)
  let ρ : GL (Fin d₁) (Fv F v) → Module.End ℂ P := fun g =>
    ((chrW χX t (gdet (pb g)) : ℂ) * apow (gdet (pb g)) ((n : ℂ) / 2))⁻¹ • τ (sc g)
  have lev : ∀ {Λ : Fl F v n d →ₗ[ℂ] P}, Eqv om H χX r τ Λ → ∀ g, ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)),
      (Λ ∘ₗ (SB _).subtype ∘ₗ s) (fun Y : Matrix (Fin n) (Fin d) (Fv F v) => Φ (Y * blk e g.val)) = ρ g ((Λ ∘ₗ (SB _).subtype ∘ₗ s) Φ) := fun {Λ} hΛ g Φ hΦ => by
    obtain ⟨m', hm1, hm2⟩ := sW (C * pb g * C⁻¹)
    have lv := is_levi h hC hm1 hm2 (sc1 g) (x := 1) (y := 1) (by rw [sc2]; rfl) (z := 1) (fun u _ => by simp) (by simp) (by simp)
    obtain ⟨-, q2⟩ := rd (rW m' hm1 _ hm2) Φ hΦ
    have := hΛ.act 1 _ m' lv (sc1 g) 1 (one_mem _) (one_UAt W) hm1 _ (s Φ).2 _ (s _).2 (by rw [one_mul]; exact q2)
    have bb : blk e g.val = (pb g).val := by
      change _ = bl e g.val 1 1
      rw [blk, bl]
      congr 2
      ext (_ | _) (_ | _) <;> simp
    rw [eo, map_smul, Submodule.coe_smul, map_smul] at this
    rw [bb]
    apply smul_right_injective _ (c0 (pb g))
    simp only [ρ, LinearMap.smul_apply, smul_smul, mul_inv_cancel₀ (c0 (pb g)), one_smul]
    simpa using this
  obtain ⟨l, hl, hν⟩ : ∃ l : (Fv F v)ˣ, valuation (Fv F v) (l : Fv F v) = 1 ∧ chrW χW t l ≠ 1 := by
    by_contra h'
    exact ram fun x hx => by by_contra h''; exact h' ⟨x, hx, h''⟩
  obtain ⟨c, hc⟩ := local_multiplicity_one_irreducible_GL hBe (inv hΛ) (inv hΛ') (hu χW hk) hl hν hn ρ hr (fun N hN => hi N fun g hg x hx => by
    have e1 : sc (GeneralLinearGroup.map (piW t) g.1) = g := ua_ext h (Vac.skew_det hW₁) (sc1 _) hg (sc2 _)
    have := N.smul_mem ((chrW χX t (gdet (pb (GeneralLinearGroup.map (piW t) g.1))) : ℂ) *
      apow (gdet (pb (GeneralLinearGroup.map (piW t) g.1))) ((n : ℂ) / 2)) (hN (GeneralLinearGroup.map (piW t) g.1) x hx)
    simpa only [ρ, LinearMap.smul_apply, smul_smul, mul_inv_cancel₀ (c0 _), one_smul, e1] using this) (lev hΛ) (lev hΛ') (by
      obtain ⟨φ, hφ, h0⟩ := h0
      exact ⟨ι φ, bij.mapsTo hφ, by simpa [s1 φ hφ] using h0⟩)
  exact ⟨c, fun φ hφ => by simpa [s1 φ hφ] using hc (ι φ) (bij.mapsTo hφ)⟩

theorem acts_ex {B : Base F E} (hB : B.IsGood σ) {r₁ s₁ r₂ s₂ : ℕ} (hX : X.IsHerm σ B r₁ s₁) (hW : W.IsSkew σ B r₂ s₂)
    {M : Model σ X W} {om : Rep σ X W} {χX χW : Chr F E} (hom : M.IsWeil B.ψ χX χW om) (t : E →ₐ[F] Fv F v) :
    (∀ h₀ : GL (Fin d) (Fv F v), ∃ h ∈ UAt σ W (evFin F v), (mat h).map (piW t) = h₀) ∧
      ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _, ∃ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ := by
  obtain ⟨⟨ι₀, hι⟩, -, sW, k⟩ := dictionary_extended F E σ n d B X W M om χX χW hB ⟨_, _, hX⟩ ⟨_, _, hW⟩ hom v t
  exact ⟨sW, fun h hh φ hφ => let ⟨φ₁, h1, h2, _⟩ := (k ι₀ hι).2 h hh (GeneralLinearGroup.map (piW t) h.1) rfl φ hφ; ⟨φ₁, h1, h2⟩⟩

theorem acts_zero {κ : Type} [Fintype κ] (T : Module.End ℂ ((κ → AF F) → ℂ)) : Acts (evFin F v) T 0 0 := fun r _ => by
  rw [show tens (evFin F v) (0 : (κ → Fv F v) → ℂ) r = 0 from funext fun _ => zero_mul _, map_zero]

theorem acts_lin {κ : Type} [Fintype κ] {T : Module.End ℂ ((κ → AF F) → ℂ)} (ex : ∀ φ ∈ SB _, ∃ φ₁ ∈ SB _, Acts (evFin F v) T φ φ₁)
    {a b a₁ b₁ : (κ → Fv F v) → ℂ} (ha : a ∈ SB _) (hb : b ∈ SB _) (h1 : Acts (evFin F v) T a a₁) (h2 : Acts (evFin F v) T b b₁) (c : ℂ) :
    Acts (evFin F v) T (a + c • b) (a₁ + c • b₁) := fun r hr => by
  by_cases h0 : a + c • b = 0
  · have key : a₁ + c • b₁ = 0 := by
      by_cases hb0 : b = 0
      · rw [hb0] at h2 h0
        rw [smul_zero, add_zero] at h0
        rw [h0] at h1
        rw [action_uniqueness F κ v T 0 (zero_mem _) _ _ h1 (acts_zero T), action_uniqueness F κ v T 0 (zero_mem _) _ _ h2 (acts_zero T)]
        simp
      · have ea : a = (-c) • b := by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left h0
        by_cases hc : c = 0
        · rw [hc, neg_zero, zero_smul] at ea
          rw [ea] at h1
          rw [action_uniqueness F κ v T 0 (zero_mem _) _ _ h1 (acts_zero T), hc]
          simp
        have : Acts (evFin F v) T a ((-c) • b₁) := fun r hr => by
          have hr' := adjoint_statement.rest F κ v r a ha (by rw [ea]; exact smul_ne_zero (neg_ne_zero.2 hc) hb0) hr b hb
          have e1 : ∀ f : (κ → Fv F v) → ℂ, tens (evFin F v) ((-c) • f) r = (-c) • tens (evFin F v) f r := fun f =>
            funext fun _ => by simp [tens, mul_assoc]
          rw [ea, e1, e1, map_smul, h2 r hr']
        rw [action_uniqueness F κ v T a ha _ _ h1 this]
        simp
    rw [h0, key]
    exact acts_zero T r (h0 ▸ hr)
  · have hs := add_mem ha ((SB _).smul_mem c hb)
    have e1 : ∀ f g : (κ → Fv F v) → ℂ, tens (evFin F v) (f + c • g) r = tens (evFin F v) f r + c • tens (evFin F v) g r := fun f g =>
      funext fun _ => by simp [tens, mul_assoc, add_mul]
    rw [e1, e1, map_add, map_smul, h1 r (adjoint_statement.rest F κ v r _ hs h0 hr a ha), h2 r (adjoint_statement.rest F κ v r _ hs h0 hr b hb)]

theorem ramifiedMultiplicityOne_of_bernstein (hBe : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) : RamifiedMultiplicityOne := by
  intro F E _ _ _ _ _ σ B a a' a₁ a₁' G G₁ X om om' om₁ om₁' R Rf R₁ Rf₁ H i₀ i₁ χ r m m₁ st hH v hv lam lam' hl hl' h0
  have T := m.triple
  have T₁ := m₁.triple
  have hB := T.base
  let t := B.τ ⟨v, T.chars.sub hv⟩
  obtain ⟨sW₁, ex₁⟩ := acts_ex hB T₁.geo.hV T₁.geo.hW T₁.weil t
  obtain ⟨-, ex⟩ := acts_ex hB T.geo.hV T.geo.hW T.weil t
  obtain ⟨-, -, hν, -, ram, -⟩ := split_character_facts F E B X a a' v t T.chars
  have onto₁ : ∀ x, ∃ φ ∈ SB _, Rf₁.p v φ = x := fun x => Submodule.mem_map.1 ((m₁.fin.onto v).symm ▸ Submodule.mem_top)
  have onto : ∀ x, ∃ φ ∈ SB _, Rf.p v φ = x := fun x => Submodule.mem_map.1 ((m.fin.onto v).symm ▸ Submodule.mem_top)
  have onto' : ∀ x, ∃ φ ∈ SB _, Rf.p' v φ = x := fun x => Submodule.mem_map.1 ((m.fin.onto' v).symm ▸ Submodule.mem_top)
  have wd : ∀ h ∈ UAt σ G₁.W (evFin F v), ∀ φ ∈ SB _, ∀ ψ ∈ SB _, ∀ φ₁ ∈ SB _, ∀ ψ₁ ∈ SB _, Acts (evFin F v) (om₁ (1, h)) φ φ₁ →
      Acts (evFin F v) (om₁ (1, h)) ψ ψ₁ → Rf₁.p v φ = Rf₁.p v ψ → Rf₁.p v φ₁ = Rf₁.p v ψ₁ := fun h hh φ a1 ψ a2 φ₁ a3 ψ₁ a4 b1 b2 e => by
    have := m₁.fin.equiv v h hh _ (add_mem a1 ((SB _).smul_mem (-1) a2)) 0 (zero_mem _) _ (add_mem a3 ((SB _).smul_mem (-1) a4)) 0
      (zero_mem _) (acts_lin (ex₁ h hh) a1 a2 b1 b2 (-1)) (acts_zero _) (by simp [e])
    simpa [← sub_eq_add_neg, sub_eq_zero] using this
  have exτ : ∀ h : UA σ G₁.W.J, ∃ τ : Module.End ℂ (Rf₁.Pi v), h ∈ UAt σ G₁.W (evFin F v) → ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _,
      Acts (evFin F v) (om₁ (1, h)) φ φ₁ → τ (Rf₁.p v φ) = Rf₁.p v φ₁ := fun h => by
    by_cases hh : h ∈ UAt σ G₁.W (evFin F v)
    swap
    · exact ⟨0, fun h' => absurd h' hh⟩
    choose s s1 s2 using onto₁
    choose A A1 A2 using ex₁ h hh
    have k : ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om₁ (1, h)) φ φ₁ → Rf₁.p v (A _ (s1 (Rf₁.p v φ))) = Rf₁.p v φ₁ :=
      fun φ b1 φ₁ b2 b3 => wd h hh _ (s1 _) _ b1 _ (A1 _ _) _ b2 (A2 _ _) b3 (s2 _)
    have lin : ∀ x y (c : ℂ), Rf₁.p v (A _ (s1 (x + c • y))) = Rf₁.p v (A _ (s1 x)) + c • Rf₁.p v (A _ (s1 y)) := fun x y c => by
      have := k _ (add_mem (s1 x) ((SB _).smul_mem c (s1 y))) _ (add_mem (A1 _ (s1 x)) ((SB _).smul_mem c (A1 _ (s1 y))))
        (acts_lin (ex₁ h hh) (s1 x) (s1 y) (A2 _ _) (A2 _ _) c)
      rw [map_add, map_smul, s2, s2, map_add, map_smul] at this
      exact this
    obtain ⟨f, hf⟩ : ∃ f : Rf₁.Pi v → Rf₁.Pi v, ∀ x, f x = Rf₁.p v (A _ (s1 x)) := ⟨_, fun _ => rfl⟩
    have k' : ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om₁ (1, h)) φ φ₁ → f (Rf₁.p v φ) = Rf₁.p v φ₁ :=
      fun φ b1 φ₁ b2 b3 => (hf _).trans (k φ b1 φ₁ b2 b3)
    have lin' : ∀ x y (c : ℂ), f (x + c • y) = f x + c • f y := fun x y c => by rw [hf, hf, hf]; exact lin x y c
    have z : f 0 = 0 := by simpa using k' 0 (zero_mem _) 0 (zero_mem _) (acts_zero _)
    exact ⟨{ toFun := f, map_add' := fun x y => by simpa using lin' x y 1,
             map_smul' := fun c y => by simpa [z] using lin' 0 y c }, fun _ => k'⟩
  choose τ hτ using exτ
  have τ1 : τ 1 = 1 := LinearMap.ext fun x => by
    obtain ⟨φ, h1, rfl⟩ := onto₁ x
    exact hτ 1 (one_UAt _) φ h1 φ h1 fun r _ => by rw [show ((1 : UA σ G₁.V.J), (1 : UA σ G₁.W.J)) = 1 from rfl, map_one]; rfl
  have hr : Module.rank ℂ (Rf₁.Pi v) ≤ Cardinal.aleph0 := by
    obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := Fv F v)
    refine le_trans ?_ (rank_SB (Fin a₁ × Fin (a₁ + a₁') → Fv F v))
    rw [← rank_top, ← m₁.fin.onto v]
    exact rank_map_le _ _
  have hi : ∀ N : Submodule ℂ (Rf₁.Pi v), (∀ h ∈ UAt σ G₁.W (evFin F v), ∀ x ∈ N, τ h x ∈ N) → N = ⊥ ∨ N = ⊤ := fun N hN =>
    m₁.fin.irred v N fun h hh φ b1 φ₁ b2 b3 b4 => hτ h hh φ b1 φ₁ b2 b3 ▸ hN h hh _ b4
  have eq : ∀ {lam}, IsFiniteLocalEquivariantMap om om₁ H v χ r (Rf.p v) (Rf₁.p v) lam → Eqv om H χ r τ (lam ∘ₗ Rf.p v) := fun {lam} hl =>
    ⟨fun φ hφ => by rw [LinearMap.mem_ker, LinearMap.comp_apply, m.fin.inv v hφ, map_zero],
      fun z h₁ m' lv hh u hu b1 b2 φ b3 φ' b4 b5 => by
        obtain ⟨φ₁, c1, c2⟩ := onto₁ (lam (Rf.p v φ))
        obtain ⟨φ₂, c3, c4⟩ := ex₁ h₁ hh φ₁ c1
        rw [LinearMap.comp_apply, LinearMap.comp_apply, hl z h₁ m' lv u hu b1 b2 φ b3 φ' b4 φ₁ c1 φ₂ c3 b5 c4 c2.symm, ← c2,
          hτ h₁ hh φ₁ c1 φ₂ c3 c4]⟩
  have eq' : ∀ {lam}, IsFiniteLocalEquivariantMap om om₁ H v χ r (Rf.p v) (Rf₁.p v) lam → Eqv om' H χ r τ (lam ∘ₗ Rf.p' v) := fun {lam} hl =>
    ⟨fun φ hφ => by rw [LinearMap.mem_ker, LinearMap.comp_apply, m.fin.inv' v hφ, map_zero],
      fun z h₁ m' lv hh u hu b1 b2 φ b3 φ' b4 b5 => by
        obtain ⟨ψ, c1, c2⟩ := onto (Rf.p' v φ)
        obtain ⟨ψ', c3, c4⟩ := ex _ (mul_UAt b1 b2) ψ c1
        rw [LinearMap.comp_apply, LinearMap.comp_apply, ← m.fin.equiv v _ (mul_UAt b1 b2) ψ c1 φ b3 ψ' c3 φ' b4 c4 b5 c2, ← c2]
        exact (eq hl).act z h₁ m' lv hh u hu b1 b2 ψ c1 ψ' c3 c4⟩
  obtain ⟨x, hx⟩ : ∃ x, lam x ≠ 0 := by
    by_contra h'
    push Not at h'
    exact h0 (LinearMap.ext h')
  rcases st with ⟨e1, e2, -, -, rfl, -⟩ | ⟨e1, e2, -, -, rfl, -⟩
  · obtain ⟨c, hc⟩ := pair_multiplicity_one_ramified hBe hB T.geo.hV T.geo.hW T₁.geo.hW T.weil
      (show IsHecke F E (X.β / X.α) from ⟨T.chars.heckeβ.1.div' T.chars.heckeα.1, fun x => by
        rw [MonoidHom.div_apply, T.chars.heckeβ.2, T.chars.heckeα.2, div_one]⟩) T.chars.resβ hH t
      (fun hu => ram hv fun y hy => by
        have := hu y hy
        rw [chrW_div] at this
        rw [Chars.ν, chrW_div, ← inv_div, this, inv_one]) (by omega) sW₁ τ1 hr hi (eq hl) (eq hl')
      (let ⟨φ, h1, h2⟩ := onto x; ⟨φ, h1, by rwa [LinearMap.comp_apply, h2]⟩)
    exact ⟨c, LinearMap.ext fun y => let ⟨φ, h1, h2⟩ := onto y; h2 ▸ hc φ h1⟩
  · obtain ⟨c, hc⟩ := pair_multiplicity_one_ramified hBe hB T.geo.hV' T.geo.hW T₁.geo.hW T.weil'
      (show IsHecke F E (X.α / X.β) from ⟨T.chars.heckeα.1.div' T.chars.heckeβ.1, fun x => by
        rw [MonoidHom.div_apply, T.chars.heckeβ.2, T.chars.heckeα.2, div_one]⟩) T.chars.resα hH t
      (ram hv) (by omega) sW₁ τ1 hr hi (eq' hl) (eq' hl')
      (let ⟨φ, h1, h2⟩ := onto' x; ⟨φ, h1, by rwa [LinearMap.comp_apply, h2]⟩)
    exact ⟨c, LinearMap.ext fun y => let ⟨φ, h1, h2⟩ := onto' y; h2 ▸ hc φ h1⟩

end PositivityTheory.ThKG.LocalRamifiedLeviRestriction
end
end
