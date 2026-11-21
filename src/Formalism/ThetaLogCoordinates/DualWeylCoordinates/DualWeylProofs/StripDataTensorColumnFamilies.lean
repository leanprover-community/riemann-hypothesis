import Formalism.ThetaLogCoordinates.DualWeylCoordinates.StripDataTensorColumnFamilies
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QbIndepField

section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} [NeZero n] {κ : Type} [Fintype κ] [DecidableEq κ] {B : Matrix κ κ (GLCoord ℤ n)}
  {be : κ → Fin n → ℤ} {Str : (Fin n → ℤ) → Finset (Fin n → ℤ)}
  {ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ}

lemma qx_ps_equiv (hd : IsStripData B be Str ps) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : nu ∈ Str mu)
    (K : TIdx mu) (k : κ) (I : TIdx nu) :
    ∑ y : TIdx mu × κ, TMat mu K y.1 * B k y.2 * (ps mu nu y I : GLCoord ℤ n) =
      ∑ I', (ps mu nu (K, k) I' : GLCoord ℤ n) * TMat nu I' I :=
  congrFun (congrFun (hd.2.2.2.1 mu hmu nu hnu) (K, k)) I

lemma qx_wt (hd : IsStripData B be Str ps) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : nu ∈ Str mu)
    (K : TIdx mu) (k : κ) (I : TIdx nu) (h : ps mu nu (K, k) I ≠ 0) :
    qb_wtT mu K + be k = qb_wtT nu I := by
  have h1 := congrArg (evGL (torusPt n)) (qx_ps_equiv hd hmu hnu K k I)
  simp only [map_sum, map_mul, map_intCast, qb_evGL_torus_TMat, hd.2.1, Fintype.sum_prod_type,
    ite_mul, zero_mul, mul_ite, mul_zero, sum_ite_eq, sum_ite_eq', mem_univ, if_true,
    AddMonoidAlgebra.single_mul_single, one_mul] at h1
  by_contra hne
  have h2 := congrArg (fun x => x.coeff (qb_wtT nu I)) h1
  simp only [← zsmul_eq_mul', ← zsmul_eq_mul, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, smul_eq_mul, if_neg hne, if_true, mul_zero, mul_one] at h2
  exact h h2.symm

lemma qx_wt_can (hd : IsStripData B be Str ps) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : nu ∈ Str mu)
    (K : TIdx mu) (k : κ) (h : ps mu nu (K, k) (canT nu) ≠ 0) : qb_wtT mu K = nu - be k := by
  have h1 := qx_wt hd hmu hnu K k _ h
  rw [qb_wtT_can (hd.2.2.1 mu hmu nu hnu)] at h1
  rw [← h1, add_sub_cancel_right]

variable {M M' : GLMod n}

abbrev qx_J (Str : (Fin n → ℤ) → Finset (Fin n → ℤ)) (CF : ColFam M) : Type :=
  Σ j : CF.J, ↥(Str (CF.mu j))

def qx_ph (ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ) (e : M'.ι ≃ M.ι × κ) (CF : ColFam M)
    (x : qx_J Str CF) : Matrix M'.ι (TIdx (x.2 : Fin n → ℤ)) ℤ :=
  fun i I => ∑ K : TIdx (CF.mu x.1), CF.ph x.1 (e i).1 K * ps (CF.mu x.1) x.2 (K, (e i).2) I

lemma qx_ph_apply (e : M'.ι ≃ M.ι × κ) (CF : ColFam M) (x : qx_J Str CF) (i : M'.ι)
    (I : TIdx (x.2 : Fin n → ℤ)) :
    qx_ph ps e CF x i I = ∑ K : TIdx (CF.mu x.1), CF.ph x.1 (e i).1 K * ps (CF.mu x.1) x.2 (K, (e i).2) I := rfl

lemma qx_equiv (hd : IsStripData B be Str ps) (e : M'.ι ≃ M.ι × κ) (hT : IsTensor M M' B e) (CF : ColFam M)
    (x : qx_J Str CF) (i : M'.ι) (I : TIdx (x.2 : Fin n → ℤ)) :
    ∑ k, M'.A i k * (qx_ph ps e CF x k I : GLCoord ℤ n) =
      ∑ I', (qx_ph ps e CF x i I' : GLCoord ℤ n) * TMat (x.2 : Fin n → ℤ) I' I := by
  obtain ⟨j, nu, hnu⟩ := x
  have hmu := CF.dom j
  have hT' : ∀ i j, M'.A i j = M.A (e i).1 (e j).1 * B (e i).2 (e j).2 := hT
  simp only [qx_ph_apply, hT', Int.cast_sum, Int.cast_mul]
  rw [← e.symm.sum_comp]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
  calc ∑ m, ∑ k, M.A (e i).1 m * B (e i).2 k *
        ∑ K, (CF.ph j m K : GLCoord ℤ n) * (ps (CF.mu j) nu (K, k) I : GLCoord ℤ n)
      = ∑ K, ∑ k, (∑ m, M.A (e i).1 m * (CF.ph j m K : GLCoord ℤ n)) * (B (e i).2 k *
          (ps (CF.mu j) nu (K, k) I : GLCoord ℤ n)) := by
        simp only [mul_sum, sum_mul]
        rw [sum_comm]
        conv_lhs => enter [2, k]; rw [sum_comm]
        rw [sum_comm]
        refine sum_congr rfl fun K _ => sum_congr rfl fun k _ => sum_congr rfl fun m _ => by ring
    _ = ∑ K', (CF.ph j (e i).1 K' : GLCoord ℤ n) * ∑ y : TIdx (CF.mu j) × κ,
          TMat (CF.mu j) K' y.1 * B (e i).2 y.2 * (ps (CF.mu j) nu y I : GLCoord ℤ n) := by
        simp only [qb_equiv_apply, Fintype.sum_prod_type, mul_sum, sum_mul]
        rw [sum_comm]
        conv_lhs => enter [2, k]; rw [sum_comm]
        rw [sum_comm]
        conv_lhs => enter [2, k]; rw [sum_comm]
        refine sum_congr rfl fun K' _ => sum_congr rfl fun K _ => sum_congr rfl fun k _ => by ring
    _ = _ := by
        simp only [qx_ps_equiv hd hmu hnu, mul_sum, sum_mul]
        rw [sum_comm]
        refine sum_congr rfl fun I' _ => sum_congr rfl fun K _ => by ring

lemma qx_rank (hd : IsStripData B be Str ps) (e : M'.ι ≃ M.ι × κ) (CF : ColFam M) :
    Fintype.card M'.ι = ∑ x : qx_J Str CF, dMu (x.2 : Fin n → ℤ) := by
  rw [Fintype.card_congr e, Fintype.card_prod, CF.rank, sum_mul, Fintype.sum_sigma]
  refine sum_congr rfl fun j _ => ?_
  rw [hd.2.2.2.2.2 _ (CF.dom j)]
  exact (Finset.sum_coe_sort (Str (CF.mu j)) dMu).symm

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} [NeZero n] {κ : Type} [Fintype κ] [DecidableEq κ] {B : Matrix κ κ (GLCoord ℤ n)}
  {be : κ → Fin n → ℤ} {Str : (Fin n → ℤ) → Finset (Fin n → ℤ)}
  {ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ} {M M' : GLMod n}

lemma qx_fst_inj (CF : ColFam M) (nu0 : Fin n → ℤ) (x y : {x : qx_J Str CF // (x.2 : Fin n → ℤ) = nu0})
    (h : x.1.1 = y.1.1) : x = y := by
  obtain ⟨⟨j, nu, hnu⟩, hx⟩ := x
  obtain ⟨⟨j', nu', hnu'⟩, hy⟩ := y
  simp only at h hx hy
  subst h
  subst hx
  subst hy
  rfl

theorem qx_indep (hd : IsStripData B be Str ps) (e : M'.ι ≃ M.ι × κ) (CF : ColFam M) (F : Type) [Field F]
    (nu0 : Fin n → ℤ) :
    LinearIndependent F (fun x : {x : qx_J Str CF // (x.2 : Fin n → ℤ) = nu0} =>
      fun i => ((qx_ph ps e CF x.1 i (canT (x.1.2 : Fin n → ℤ)) : ℤ) : F)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hcon
  push Not at hcon
  obtain ⟨x1, hx1⟩ := hcon
  let s : Finset (Fin n → ℤ) := (univ.filter fun x => g x ≠ 0).image fun x => CF.mu x.1.1
  obtain ⟨mu0, hmu0, hmax⟩ := qb_exists_max s ⟨_, mem_image.2 ⟨x1, by simp [hx1], rfl⟩⟩
  obtain ⟨x0, hx0, rfl⟩ := mem_image.1 hmu0
  replace hx0 : g x0 ≠ 0 := by simpa using hx0
  obtain ⟨k0, hk0, heps⟩ := hd.2.2.2.2.1 (CF.mu x0.1.1) (CF.dom _) x0.1.2 x0.1.2.2
  have hK : ∀ x, g x ≠ 0 → ∀ K, ps (CF.mu x.1.1) x.1.2 (K, k0) (canT (x.1.2 : Fin n → ℤ)) ≠ 0 →
      CF.mu x.1.1 = CF.mu x0.1.1 ∧ K = canT (CF.mu x.1.1) := by
    intro x hgx K hne
    have h1 := qx_wt_can hd (CF.dom _) x.1.2.2 K k0 hne
    have h2 : qb_wtT (CF.mu x.1.1) K = CF.mu x0.1.1 := by
      rw [h1, hk0, x.2, x0.2, sub_sub_cancel]
    have h3 : DomLE (CF.mu x0.1.1) (CF.mu x.1.1) := h2 ▸ qb_wtT_le (CF.dom _) K
    have h4 := hmax _ (mem_image.2 ⟨x, by simp [hgx], rfl⟩) h3
    exact ⟨h4, (qb_wtT_eq_iff (CF.dom _) K).1 (h2.trans h4.symm)⟩
  have hterm : ∀ x (i : M.ι),
      g x * ((qx_ph ps e CF x.1 (e.symm (i, k0)) (canT (x.1.2 : Fin n → ℤ)) : ℤ) : F) =
      if CF.mu x.1.1 = CF.mu x0.1.1 then
        (g x * ((ps (CF.mu x.1.1) x.1.2 (canT (CF.mu x.1.1), k0) (canT (x.1.2 : Fin n → ℤ)) : ℤ) : F)) *
          ((CF.ph x.1.1 i (canT (CF.mu x.1.1)) : ℤ) : F) else 0 := by
    intro x i
    by_cases hgx : g x = 0
    · simp [hgx]
    rw [qx_ph_apply]
    simp only [Equiv.apply_symm_apply]
    split_ifs with hm
    · rw [Finset.sum_eq_single (canT (CF.mu x.1.1))]
      · push_cast; ring
      · intro K _ hKne
        exact mul_eq_zero_of_right _ (by_contra fun h => hKne (hK x hgx K h).2)
      · intro h; exact absurd (mem_univ _) h
    · rw [Finset.sum_eq_zero, Int.cast_zero, mul_zero]
      intro K _
      exact mul_eq_zero_of_right _ (by_contra fun h => hm (hK x hgx K h).1)
  have hrel : ∀ i : M.ι, ∑ x, g x *
      ((qx_ph ps e CF x.1 (e.symm (i, k0)) (canT (x.1.2 : Fin n → ℤ)) : ℤ) : F) = 0 := by
    intro i
    have := congrFun hg (e.symm (i, k0))
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using this
  simp only [hterm] at hrel
  have hli := (qb_indepF CF F (CF.mu x0.1.1)).comp
    (fun x : {x : {x : qx_J Str CF // (x.2 : Fin n → ℤ) = nu0} // CF.mu x.1.1 = CF.mu x0.1.1} =>
      (⟨x.1.1.1, x.2⟩ : {j : CF.J // CF.mu j = CF.mu x0.1.1}))
    (fun x y h => Subtype.ext (qx_fst_inj CF nu0 x.1 y.1 (congrArg Subtype.val h)))
  have h0 := Fintype.linearIndependent_iff.1 hli
    (fun x => g x.1 * ((ps (CF.mu x.1.1.1) x.1.1.2 (canT (CF.mu x.1.1.1), k0)
      (canT (x.1.1.2 : Fin n → ℤ)) : ℤ) : F)) ?_ ⟨x0, rfl⟩
  · simp only at h0
    rcases heps with h | h <;> rw [h] at h0 <;> simp at h0 <;> exact hx0 h0
  · funext i
    have := hrel i
    rw [← Finset.sum_filter, Finset.sum_subtype (p := fun x => CF.mu x.1.1 = CF.mu x0.1.1) _ (by simp)] at this
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Function.comp] using this

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

def qx_colFam {n : ℕ} [NeZero n] {κ : Type} [Fintype κ] [DecidableEq κ] {B : Matrix κ κ (GLCoord ℤ n)}
    {be : κ → Fin n → ℤ} {Str : (Fin n → ℤ) → Finset (Fin n → ℤ)}
    {ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ} (hd : IsStripData B be Str ps)
    {M M' : GLMod n} (e : M'.ι ≃ M.ι × κ) (hT : IsTensor M M' B e) (CF : ColFam M) : ColFam M' where
  J := qx_J Str CF
  mu := fun x => (x.2 : Fin n → ℤ)
  dom := fun x => hd.2.2.1 _ (CF.dom x.1) _ x.2.2
  ph := qx_ph ps e CF
  equiv := fun x => by
    ext i I
    exact qx_equiv hd e hT CF x i I
  indepP := fun p hp nu => by
    have := Fact.mk hp
    exact qx_indep hd e CF (ZMod p) nu
  indepQ := fun nu => qx_indep hd e CF ℚ nu
  rank := qx_rank hd e CF

theorem strip_data_tensor_holds : StripDataTensorColumnFamilies := by
  intro n _ κ _ _ B be Str ps hd M M' e hT ⟨CF⟩
  exact ⟨qx_colFam hd e hT CF⟩

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end
