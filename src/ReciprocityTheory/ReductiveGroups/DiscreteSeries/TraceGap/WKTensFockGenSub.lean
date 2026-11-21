import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.AlgebraMapInvFf
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HasDerivAtInvExpCurveEntry
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.IsInLieAlgebraISmulAddConjTranspose
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bridge
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeWt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFCoreA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Unique
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.GeneratedSubStable

section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

def IsDer (O : Module.End ℂ (Fock n)) (L : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ)) : Prop :=
  ∀ (p : ℕ) (v : Fin p → (Fin n × Fin n → ℂ)),
    O (ExteriorAlgebra.ιMulti ℂ p v) = ∑ i, ExteriorAlgebra.ιMulti ℂ p (Function.update v i (L (v i)))

theorem isDer_zero : IsDer (0 : Module.End ℂ (Fock n)) 0 := by
  intro p v
  simp only [LinearMap.zero_apply]
  refine (Finset.sum_eq_zero fun i _ => ?_).symm
  exact (ExteriorAlgebra.ιMulti ℂ p).map_update_zero v i

theorem isDer_add {O O' : Module.End ℂ (Fock n)} {L L' : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ)}
    (h : IsDer O L) (h' : IsDer O' L') : IsDer (O + O') (L + L') := by
  intro p v
  rw [LinearMap.add_apply, h, h', ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.add_apply, (ExteriorAlgebra.ιMulti ℂ p).map_update_add]

theorem isDer_smul (c : ℂ) {O : Module.End ℂ (Fock n)} {L : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ)}
    (h : IsDer O L) : IsDer (c • O) (c • L) := by
  intro p v
  rw [LinearMap.smul_apply, h, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, (ExteriorAlgebra.ιMulti ℂ p).map_update_smul]

theorem isDer_neg {O : Module.End ℂ (Fock n)} {L : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ)}
    (h : IsDer O L) : IsDer (-O) (-L) := by
  have := isDer_smul (-1) h
  simpa only [neg_one_smul] using this

theorem isDer_sum {ι : Type*} (s : Finset ι) {O : ι → Module.End ℂ (Fock n)}
    {L : ι → (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ)} (h : ∀ j ∈ s, IsDer (O j) (L j)) :
    IsDer (∑ j ∈ s, O j) (∑ j ∈ s, L j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isDer_zero (n := n))
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact isDer_add (h j (Finset.mem_insert_self j s)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem cpV_cmV_ιMulti (u w : Fin n × Fin n → ℂ) : ∀ (p : ℕ) (v : Fin p → (Fin n × Fin n → ℂ)),
    cpV u (cmV w (ExteriorAlgebra.ιMulti ℂ p v)) =
      ∑ i, dualV w (v i) • ExteriorAlgebra.ιMulti ℂ p (Function.update v i u)
  | 0, v => by
    simp only [cmV, ExteriorAlgebra.ιMulti_zero_apply, CliffordAlgebra.contractLeft_one, map_zero]
    rw [Fin.sum_univ_zero]
  | p + 1, v => by
    have ih := cpV_cmV_ιMulti u w p (Matrix.vecTail v)
    simp only [cmV, cpV, LinearMap.mulLeft_apply] at ih ⊢
    have hanti : ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ (v 0) =
        -(ExteriorAlgebra.ι ℂ (v 0) * ExteriorAlgebra.ι ℂ u) :=
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap u (v 0))
    rw [ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι_mul, mul_sub, mul_smul_comm,
      ← mul_assoc (ExteriorAlgebra.ι ℂ u), hanti, neg_mul, sub_neg_eq_add, mul_assoc, ih,
      Fin.sum_univ_succ, Finset.mul_sum]
    congr 1
    · rw [ExteriorAlgebra.ιMulti_succ_apply, Function.update_self]
      congr 3
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul_comm, ExteriorAlgebra.ιMulti_succ_apply,
        Function.update_of_ne (Fin.succ_ne_zero i).symm]
      congr 3
      funext j
      simp only [Matrix.vecTail, Function.comp_apply, Function.update_apply, Fin.succ_inj]

theorem isDer_cpV_cmV (u w : Fin n × Fin n → ℂ) :
    IsDer (cpV u * cmV w) (LinearMap.smulRight (dualV w) u) := by
  intro p v
  rw [Module.End.mul_apply, cpV_cmV_ιMulti]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smulRight_apply, (ExteriorAlgebra.ιMulti ℂ p).map_update_smul]

def Lab (ε : Fin n → Bool) (a b : Fin n) : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ) :=
  if ε a = true ∧ ε b = true then
    ∑ x ∈ minusIdx ε, LinearMap.smulRight (dualV (Pi.single (b, x) (1 : ℂ))) (Pi.single (a, x) 1)
  else if ε a = false ∧ ε b = false then
    -∑ i ∈ plusIdx ε, LinearMap.smulRight (dualV (Pi.single (i, a) (1 : ℂ))) (Pi.single (i, b) 1)
  else 0

theorem isDer_sgE (a b : Fin n) : IsDer (sgE ε (cpFock (n := n)) cmFock a b) (Lab ε a b) := by
  unfold sgE Lab
  split_ifs
  · exact isDer_sum _ fun x _ => by rw [cpFock_eq_cpV, cmFock_eq_cmV]; exact isDer_cpV_cmV _ _
  · exact isDer_neg (isDer_sum _ fun i _ => by rw [cpFock_eq_cpV, cmFock_eq_cmV]; exact isDer_cpV_cmV _ _)
  · exact isDer_zero

def sgX (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (Fock n) :=
  ∑ a, ∑ b, X a b • sgE ε (cpFock (n := n)) cmFock a b

def LX (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ) :=
  ∑ a, ∑ b, X a b • Lab ε a b

theorem isDer_sgX (X : Matrix (Fin n) (Fin n) ℂ) : IsDer (sgX ε X) (LX ε X) :=
  isDer_sum _ fun a _ => isDer_sum _ fun b _ => isDer_smul _ (isDer_sgE a b)

theorem Lab_apply (a b : Fin n) (w : Fin n × Fin n → ℂ) (y : Fin n × Fin n) :
    Lab ε a b w y =
      (if ε a = true ∧ ε b = true ∧ y.1 = a ∧ ε y.2 = false then w (b, y.2) else 0) -
        (if ε a = false ∧ ε b = false ∧ y.2 = b ∧ ε y.1 = true then w (y.1, a) else 0) := by
  obtain ⟨y1, y2⟩ := y
  unfold Lab
  cases ha : ε a <;> cases hb : ε b <;>
    simp [LinearMap.sum_apply, Finset.sum_apply, dualV_single, Pi.single_apply, minusIdx, plusIdx,
      Prod.ext_iff, ite_and, Finset.sum_ite_eq] <;>
    by_cases h1 : ε y1 = true <;> simp [h1]

theorem LX_apply (X : Matrix (Fin n) (Fin n) ℂ) (w : Fin n × Fin n → ℂ) (y : Fin n × Fin n) :
    LX ε X w y = if IsPhys ε y then
      (∑ b ∈ plusIdx ε, X y.1 b * w (b, y.2)) - ∑ a ∈ minusIdx ε, X a y.2 * w (y.1, a) else 0 := by
  obtain ⟨y1, y2⟩ := y
  simp only [LX, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Lab_apply, mul_sub, Finset.sum_sub_distrib]
  have h1 : ∑ a, ∑ b, X a b * (if ε a = true ∧ ε b = true ∧ y1 = a ∧ ε y2 = false then w (b, y2) else 0) =
      if IsPhys ε (y1, y2) then ∑ b ∈ plusIdx ε, X y1 b * w (b, y2) else 0 := by
    rw [Finset.sum_eq_single y1 (fun a _ ha => Finset.sum_eq_zero fun b _ => by simp [Ne.symm ha])
      (by simp)]
    unfold IsPhys
    by_cases hy1 : ε y1 = true <;> by_cases hy2 : ε y2 = false <;>
      simp [hy1, hy2, plusIdx, Finset.sum_filter]
  have h2 : ∑ a, ∑ b, X a b * (if ε a = false ∧ ε b = false ∧ y2 = b ∧ ε y1 = true then w (y1, a) else 0) =
      if IsPhys ε (y1, y2) then ∑ a ∈ minusIdx ε, X a y2 * w (y1, a) else 0 := by
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_eq_single y2
      (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    unfold IsPhys
    by_cases hy1 : ε y1 = true <;> by_cases hy2 : ε y2 = false <;>
      simp [hy1, hy2, minusIdx, Finset.sum_filter]
  rw [h1, h2]
  split_ifs <;> simp

def adD (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n × Fin n) : ℂ :=
  if IsPhys ε x ∧ IsPhys ε y then
    X x.1 y.1 * star ((1 : Matrix (Fin n) (Fin n) ℂ) x.2 y.2) + (1 : Matrix (Fin n) (Fin n) ℂ) x.1 y.1 * star (X x.2 y.2)
  else 0

theorem adMat_exp_hasDeriv (X : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n × Fin n) :
    HasDerivAt (fun t : ℝ => adMat ε (NormedSpace.exp ((t : ℂ) • X)) x y) (adD ε X x y) 0 := by
  have he : ∀ c d, HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) c d) (X c d) 0 := by
    intro c d
    have := hasDerivAt_exp_curve_entry (1 : Matrix (Fin n) (Fin n) ℂ) X c d
    simpa only [Matrix.one_mul] using this
  have h0 : ∀ c d, NormedSpace.exp (((0 : ℝ) : ℂ) • X) c d = (1 : Matrix (Fin n) (Fin n) ℂ) c d := by
    intro c d
    simp
  unfold adMat adD
  by_cases hx : IsPhys ε x <;> by_cases hy : IsPhys ε y
  · simp only [hx, hy, if_true, and_self]
    have h := (he x.1 y.1).fun_mul (he x.2 y.2).star
    rw [h0, h0] at h
    exact h
  · simp only [hx, hy, if_true, if_false, and_false]
    exact hasDerivAt_const _ _
  · simp only [hx, if_false, false_and]
    exact hasDerivAt_const _ _
  · simp only [hx, if_false, false_and]
    exact hasDerivAt_const _ _

theorem adPhys_exp_hasDeriv (X : Matrix (Fin n) (Fin n) ℂ) (w : Fin n × Fin n → ℂ) (x : Fin n × Fin n) :
    HasDerivAt (fun t : ℝ => adPhys ε (NormedSpace.exp ((t : ℂ) • X)) w x) (∑ y, adD ε X x y * w y) 0 := by
  simp only [adPhys, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  exact HasDerivAt.fun_sum fun y _ => (adMat_exp_hasDeriv X x y).mul_const (w y)

theorem sum_adD_eq_LX {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ = -X) (w : Fin n × Fin n → ℂ)
    (x : Fin n × Fin n) : ∑ y, adD ε X x y * w y = LX ε X w x := by
  have hs : ∀ c d, star (X c d) = -X d c := by
    intro c d
    have := congrFun (congrFun hX d) c
    simpa [Matrix.conjTranspose_apply] using this
  rw [LX_apply]
  obtain ⟨x1, x2⟩ := x
  unfold adD IsPhys
  have hst : ∀ c d : Fin n, star ((1 : Matrix (Fin n) (Fin n) ℂ) c d) = (1 : Matrix (Fin n) (Fin n) ℂ) c d := by
    intro c d
    rw [Matrix.one_apply]
    split_ifs <;> simp
  by_cases hx : ε x1 = true ∧ ε x2 = false
  · simp only [hx, true_and, if_true]
    rw [Fintype.sum_prod_type]
    trans ∑ b, ∑ c, ((if ε b = true ∧ c = x2 then X x1 b * w (b, c) else 0) +
      (if b = x1 ∧ ε c = false then -X c x2 * w (b, c) else 0))
    · refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
      by_cases hb : ε b = true <;> by_cases hc : c = x2 <;> by_cases hb1 : b = x1 <;>
        simp_all [Matrix.one_apply, Ne.symm] <;> ring
    · simp only [Finset.sum_add_distrib]
      simp [ite_and, plusIdx, minusIdx, Finset.sum_filter, sub_eq_add_neg]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs <;> simp
  · simp only [hx, false_and, if_false, zero_mul, Finset.sum_const_zero]

theorem adPhys_one' (w : Fin n × Fin n → ℂ) : adPhys ε 1 w = w := by
  simp [adPhys, adMat_one]

def wedgeCoord (p : ℕ) :
    MultilinearMap ℂ (fun _ : Fin p => Fin n × Fin n → ℂ) (Finset (Fin (n * n)) → ℂ) :=
  (fockBasis n).equivFun.toLinearMap.compMultilinearMap (ExteriorAlgebra.ιMulti ℂ p).toMultilinearMap

theorem wedgeCoord_eq_sum (p : ℕ) (v : Fin p → (Fin n × Fin n → ℂ)) :
    wedgeCoord p v = ∑ r : Fin p → Fin n × Fin n,
      (∏ i, v i (r i)) • wedgeCoord p (fun i => Pi.single (r i) (1 : ℂ)) := by
  classical
  have hv : v = fun i => ∑ x, v i x • Pi.single x (1 : ℂ) := by
    funext i y
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [MultilinearMap.map_smul_univ]

theorem wedgeCoord_continuous (p : ℕ) : Continuous (wedgeCoord (n := n) p) := by
  have h : (wedgeCoord (n := n) p : (Fin p → (Fin n × Fin n → ℂ)) → (Finset (Fin (n * n)) → ℂ)) =
      fun v => ∑ r : Fin p → Fin n × Fin n,
        (∏ i, v i (r i)) • wedgeCoord p (fun i => Pi.single (r i) (1 : ℂ)) :=
    funext (wedgeCoord_eq_sum p)
  rw [h]
  fun_prop

def wedgeCoordC (p : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin p => Fin n × Fin n → ℂ) (Finset (Fin (n * n)) → ℂ) :=
  { toMultilinearMap := wedgeCoord p, cont := wedgeCoord_continuous p }

theorem ff_exp_wedge_hasDeriv {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ = -X) (p : ℕ)
    (v : Fin p → (Fin n × Fin n → ℂ)) :
    HasDerivAt (fun t : ℝ => (fockBasis n).equivFun
        (ff ε (NormedSpace.exp ((t : ℂ) • X)) (ExteriorAlgebra.ιMulti ℂ p v)))
      ((fockBasis n).equivFun (sgX ε X (ExteriorAlgebra.ιMulti ℂ p v))) 0 := by
  classical
  set c : ℝ → (Fin p → (Fin n × Fin n → ℂ)) :=
    fun t i => adPhys ε (NormedSpace.exp ((t : ℂ) • X)) (v i) with hcdef
  have hc : HasDerivAt c (fun i => LX ε X (v i)) 0 := by
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun x => ?_
    rw [← sum_adD_eq_LX hX]
    exact adPhys_exp_hasDeriv X (v i) x
  have hc0 : c 0 = v := by
    funext i
    simp [c, adPhys_one']
  have hF := (wedgeCoordC (n := n) p).hasFDerivAt (c 0)
  have h := (hF.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) hc
  have hfun : (fun t : ℝ => (fockBasis n).equivFun
      (ff ε (NormedSpace.exp ((t : ℂ) • X)) (ExteriorAlgebra.ιMulti ℂ p v))) = (wedgeCoordC (n := n) p) ∘ c := by
    funext t
    simp only [Function.comp_apply, ff, ExteriorAlgebra.map_apply_ιMulti]
    rfl
  rw [hfun]
  convert h using 1
  all_goals try rfl
  rw [ContinuousLinearMap.coe_restrictScalars', ContinuousMultilinearMap.linearDeriv_apply, hc0, isDer_sgX,
    map_sum]
  rfl

theorem ff_exp_hasDeriv {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ = -X) (f : Fock n) :
    HasDerivAt (fun t : ℝ => (fockBasis n).equivFun (ff ε (NormedSpace.exp ((t : ℂ) • X)) f))
      ((fockBasis n).equivFun (sgX ε X f)) 0 := by
  have hf : f = ∑ S, (fockBasis n).repr f S • fockBasis n S := ((fockBasis n).sum_repr f).symm
  rw [hf]
  simp only [map_sum, map_smul]
  refine HasDerivAt.fun_sum fun S _ => ?_
  refine HasDerivAt.const_smul ((fockBasis n).repr f S) ?_
  rw [fockBasis_eq]
  exact ff_exp_wedge_hasDeriv hX _ _

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

theorem sum_plus_kk {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (c j : Fin n)
    (h : ε c = true ∨ ε j = true) :
    ∑ i ∈ plusIdx ε, k c i * star (k j i) = if c = j then 1 else 0 := by
  have hkk : k * kᴴ = 1 := by
    have := hk.1
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose] at this
    exact this
  rw [Finset.sum_subset (Finset.subset_univ _)]
  · have := congrFun (congrFun hkk c) j
    simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply] at this
    exact this
  · intro i _ hi
    have hi' : ε i = false := by simpa [plusIdx] using hi
    rcases h with h | h
    · rw [kset_entry_zero hk (by rw [h, hi']; decide), zero_mul]
    · rw [kset_entry_zero hk (i := j) (by rw [h, hi']; decide), star_zero, mul_zero]

theorem sum_minus_kk {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (c b : Fin n)
    (h : ε c = false ∨ ε b = false) :
    ∑ a ∈ minusIdx ε, k c a * star (k b a) = if c = b then 1 else 0 := by
  have hkk : k * kᴴ = 1 := by
    have := hk.1
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose] at this
    exact this
  rw [Finset.sum_subset (Finset.subset_univ _)]
  · have := congrFun (congrFun hkk c) b
    simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply] at this
    exact this
  · intro a _ ha
    have ha' : ε a = true := by simpa [minusIdx] using ha
    rcases h with h | h
    · rw [kset_entry_zero hk (by rw [h, ha']; decide), zero_mul]
    · rw [kset_entry_zero hk (i := b) (by rw [h, ha']; decide), star_zero, mul_zero]

theorem conj_single_apply (k : Matrix (Fin n) (Fin n) ℂ) (a i c d : Fin n) :
    (k * Matrix.single a i (1 : ℂ) * kᴴ : Matrix (Fin n) (Fin n) ℂ) c d = k c a * star (k d i) := by
  simp [Matrix.mul_apply, Matrix.single_apply, conjTranspose_apply, ite_and, ite_mul, Finset.sum_ite_eq,
]

theorem coef_d {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (c d : Fin n) (x : Fin n × Fin n) :
    ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, (k * Matrix.single a i (1 : ℂ) * kᴴ : Matrix (Fin n) (Fin n) ℂ) c d * adMat ε k x (i, a) =
      if x = (d, c) ∧ ε d = true ∧ ε c = false then 1 else 0 := by
  by_cases hx : IsPhys ε x
  · obtain ⟨j, b⟩ := x
    have hj : ε j = true := hx.1
    have hb : ε b = false := hx.2
    have hterm : ∀ i ∈ plusIdx ε, ∀ a ∈ minusIdx ε,
        (k * Matrix.single a i (1 : ℂ) * kᴴ : Matrix (Fin n) (Fin n) ℂ) c d * adMat ε k (j, b) (i, a) =
          (k j i * star (k d i)) * (k c a * star (k b a)) := by
      intro i hi a ha
      have hia : IsPhys ε (i, a) := ⟨(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp ha).2⟩
      rw [conj_single_apply]
      simp only [adMat, hx, hia, if_true]
      ring
    rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun a ha => hterm i hi a ha,
      ← Finset.sum_mul_sum, sum_plus_kk hk j d (Or.inl hj), sum_minus_kk hk c b (Or.inr hb)]
    rcases eq_or_ne j d with h1 | h1 <;> rcases eq_or_ne c b with h2 | h2
    · subst h1
      subst h2
      simp [hj, hb]
    · rw [if_neg h2, mul_zero, if_neg]
      rintro ⟨h, -⟩
      exact h2 (Prod.ext_iff.mp h).2.symm
    · rw [if_neg h1, zero_mul, if_neg]
      rintro ⟨h, -⟩
      exact h1 (Prod.ext_iff.mp h).1
    · rw [if_neg h1, zero_mul, if_neg]
      rintro ⟨h, -⟩
      exact h1 (Prod.ext_iff.mp h).1
  · rw [if_neg]
    · refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun a ha => ?_
      have hia : IsPhys ε (i, a) := ⟨(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp ha).2⟩
      have hne : x ≠ (i, a) := fun h => hx (h ▸ hia)
      simp [adMat, hx, hne]
    · rintro ⟨rfl, h1, h2⟩
      exact hx ⟨h1, h2⟩

theorem coef_d' {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (c d : Fin n) (x : Fin n × Fin n) :
    ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, (k * Matrix.single i a (1 : ℂ) * kᴴ : Matrix (Fin n) (Fin n) ℂ) c d * star (adMat ε k x (i, a)) =
      if x = (c, d) ∧ ε c = true ∧ ε d = false then 1 else 0 := by
  by_cases hx : IsPhys ε x
  · obtain ⟨j, b⟩ := x
    have hj : ε j = true := hx.1
    have hb : ε b = false := hx.2
    have hterm : ∀ i ∈ plusIdx ε, ∀ a ∈ minusIdx ε,
        (k * Matrix.single i a (1 : ℂ) * kᴴ : Matrix (Fin n) (Fin n) ℂ) c d * star (adMat ε k (j, b) (i, a)) =
          (k c i * star (k j i)) * (k b a * star (k d a)) := by
      intro i hi a ha
      have hia : IsPhys ε (i, a) := ⟨(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp ha).2⟩
      rw [conj_single_apply]
      simp only [adMat, hx, hia, if_true, star_mul', star_star]
      ring
    rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun a ha => hterm i hi a ha,
      ← Finset.sum_mul_sum, sum_plus_kk hk c j (Or.inr hj), sum_minus_kk hk b d (Or.inl hb)]
    rcases eq_or_ne c j with h1 | h1 <;> rcases eq_or_ne b d with h2 | h2
    · subst h1
      subst h2
      simp [hj, hb]
    · rw [if_neg h2, mul_zero, if_neg]
      rintro ⟨h, -⟩
      exact h2 (Prod.ext_iff.mp h).2
    · rw [if_neg h1, zero_mul, if_neg]
      rintro ⟨h, -⟩
      exact h1 (Prod.ext_iff.mp h).1.symm
    · rw [if_neg h1, zero_mul, if_neg]
      rintro ⟨h, -⟩
      exact h1 (Prod.ext_iff.mp h).1.symm
  · rw [if_neg]
    · refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun a ha => ?_
      have hia : IsPhys ε (i, a) := ⟨(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp ha).2⟩
      have hne : x ≠ (i, a) := fun h => hx (h ▸ hia)
      simp [adMat, hx, hne]
    · rintro ⟨rfl, h1, h2⟩
      exact hx ⟨h1, h2⟩

theorem sum_comm_2_3 {M α β γ δ ζ : Type*} [AddCommMonoid M] [Fintype γ] [Fintype δ] [Fintype ζ]
    (s : Finset α) (t : Finset β) (F : α → β → γ → δ → ζ → M) :
    ∑ i ∈ s, ∑ a ∈ t, ∑ c, ∑ d, ∑ x, F i a c d x = ∑ c, ∑ d, ∑ x, ∑ i ∈ s, ∑ a ∈ t, F i a c d x := by
  calc ∑ i ∈ s, ∑ a ∈ t, ∑ c, ∑ d, ∑ x, F i a c d x
      = ∑ i ∈ s, ∑ c, ∑ a ∈ t, ∑ d, ∑ x, F i a c d x := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ c, ∑ i ∈ s, ∑ a ∈ t, ∑ d, ∑ x, F i a c d x := Finset.sum_comm
    _ = ∑ c, ∑ i ∈ s, ∑ d, ∑ a ∈ t, ∑ x, F i a c d x :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ i ∈ s, ∑ a ∈ t, ∑ x, F i a c d x := Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ i ∈ s, ∑ x, ∑ a ∈ t, F i a c d x :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ x, ∑ i ∈ s, ∑ a ∈ t, F i a c d x :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => Finset.sum_comm

section Rep

variable {n : ℕ} {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

def sigD (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : Module.End ℂ D where
  toFun v := ⟨σ k v, hD.kStable k hk v v.2⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

def wK (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    Module.End ℂ (TensorProduct ℂ D (Fock n)) :=
  TensorProduct.map (sigD hD hk) (ff ε k).toLinearMap

theorem actM_single' {M : Type*} [AddCommGroup M] [Module ℂ M] (F : Fin n → Fin n → Module.End ℂ M)
    (a i : Fin n) : actM F (Matrix.single a i (1 : ℂ)) = F a i := by
  simp [actM, Matrix.single_apply, ite_and, ite_smul, Finset.sum_ite_eq]

theorem sigD_E (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) (a i : Fin n) (v : D) :
    sigD hD hk (E a i v) = actM E (k * Matrix.single a i (1 : ℂ) * kᴴ) (sigD hD hk v) := by
  apply Subtype.ext
  have h := derived_adK hσ hD hk (Matrix.single a i (1 : ℂ)) v
  rw [actM_single'] at h
  exact h

theorem adPhys_apply_single (k : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n × Fin n) :
    adPhys ε k (Pi.single y 1) x = adMat ε k x y := by
  simp [adPhys, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem ff_cpFock_apply (k : Matrix (Fin n) (Fin n) ℂ) (i a : Fin n) (f : Fock n) :
    ff ε k (cpFock i a f) = ∑ x, adMat ε k x (i, a) • cpFock x.1 x.2 (ff ε k f) := by
  have h := LinearMap.congr_fun (ff_cpV (ε := ε) k (Pi.single (i, a) 1)) f
  simp only [Module.End.mul_apply, AlgHom.toLinearMap_apply] at h
  rw [cpFock_eq_cpV i a, h, cpV_eq_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [LinearMap.smul_apply, adPhys_apply_single]

theorem ff_cmFock_apply {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (i a : Fin n) (f : Fock n) :
    ff ε k (cmFock i a f) = ∑ x, star (adMat ε k x (i, a)) • cmFock x.1 x.2 (ff ε k f) := by
  have h := LinearMap.congr_fun (ff_cmV hk (Pi.single (i, a) 1)) f
  simp only [Module.End.mul_apply, AlgHom.toLinearMap_apply] at h
  rw [cmFock_eq_cmV i a, h, cmV_eq_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [LinearMap.smul_apply, adPhys_apply_single]

theorem wK_dOp (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) :
    wK hD hk * dOp ε (eT E) cpT = dOp ε (eT E) cpT * wK hD hk := by
  apply TensorProduct.ext'
  intro v f
  simp only [Module.End.mul_apply, dOp, LinearMap.sum_apply, map_sum, eT, cpT, TensorProduct.map_tmul,
    LinearMap.id_apply, wK, AlgHom.toLinearMap_apply]
  have key : ∀ i a, sigD hD hk (E a i v) ⊗ₜ[ℂ] ff ε k (cpFock i a f) =
      ∑ c, ∑ d, ∑ x : Fin n × Fin n,
        ((k * Matrix.single a i (1 : ℂ) * kᴴ : Matrix (Fin n) (Fin n) ℂ) c d * adMat ε k x (i, a)) •
          (E c d (sigD hD hk v) ⊗ₜ[ℂ] cpFock x.1 x.2 (ff ε k f)) := by
    intro i a
    rw [sigD_E hσ hD hk, ff_cpFock_apply, actM, LinearMap.sum_apply, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [LinearMap.sum_apply, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [LinearMap.smul_apply, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
  simp only [key]
  rw [sum_comm_2_3]
  have hcoef : ∀ c d (x : Fin n × Fin n),
      ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε,
        ((k * Matrix.single a i (1 : ℂ) * kᴴ : Matrix (Fin n) (Fin n) ℂ) c d * adMat ε k x (i, a)) •
          (E c d (sigD hD hk v) ⊗ₜ[ℂ] cpFock x.1 x.2 (ff ε k f)) =
        (if x = (d, c) ∧ ε d = true ∧ ε c = false then (1 : ℂ) else 0) •
          (E c d (sigD hD hk v) ⊗ₜ[ℂ] cpFock x.1 x.2 (ff ε k f)) := by
    intro c d x
    rw [← coef_d hk c d x, Finset.sum_smul]
    exact Finset.sum_congr rfl fun i _ => (Finset.sum_smul ..).symm
  simp only [hcoef]
  simp only [ite_smul, one_smul, zero_smul, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  simp only [plusIdx, minusIdx, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hd : ε d = true <;> simp [hd]

theorem wK_dOp' (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) :
    wK hD hk * dOp' ε (eT E) cmT = dOp' ε (eT E) cmT * wK hD hk := by
  apply TensorProduct.ext'
  intro v f
  simp only [Module.End.mul_apply, dOp', LinearMap.neg_apply, map_neg, LinearMap.sum_apply, map_sum, eT, cmT,
    TensorProduct.map_tmul, LinearMap.id_apply, wK, AlgHom.toLinearMap_apply]
  congr 1
  have key : ∀ i a, sigD hD hk (E i a v) ⊗ₜ[ℂ] ff ε k (cmFock i a f) =
      ∑ c, ∑ d, ∑ x : Fin n × Fin n,
        ((k * Matrix.single i a (1 : ℂ) * kᴴ : Matrix (Fin n) (Fin n) ℂ) c d * star (adMat ε k x (i, a))) •
          (E c d (sigD hD hk v) ⊗ₜ[ℂ] cmFock x.1 x.2 (ff ε k f)) := by
    intro i a
    rw [sigD_E hσ hD hk, ff_cmFock_apply hk, actM, LinearMap.sum_apply, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [LinearMap.sum_apply, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [LinearMap.smul_apply, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
  simp only [key]
  rw [sum_comm_2_3]
  have hcoef : ∀ c d (x : Fin n × Fin n),
      ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε,
        ((k * Matrix.single i a (1 : ℂ) * kᴴ : Matrix (Fin n) (Fin n) ℂ) c d * star (adMat ε k x (i, a))) •
          (E c d (sigD hD hk v) ⊗ₜ[ℂ] cmFock x.1 x.2 (ff ε k f)) =
        (if x = (c, d) ∧ ε c = true ∧ ε d = false then (1 : ℂ) else 0) •
          (E c d (sigD hD hk v) ⊗ₜ[ℂ] cmFock x.1 x.2 (ff ε k f)) := by
    intro c d x
    rw [← coef_d' hk c d x, Finset.sum_smul]
    exact Finset.sum_congr rfl fun i _ => (Finset.sum_smul ..).symm
  simp only [hcoef]
  simp only [ite_smul, one_smul, zero_smul, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [plusIdx, minusIdx, Finset.sum_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : ε c = true <;> simp [hc]

end Rep

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

section T

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem sgE_cpT (a b : Fin n) :
    sgE ε (cpT (N := N)) cmT a b = LinearMap.lTensor N (sgE ε (cpFock (n := n)) cmFock a b) := by
  have e : ∀ f : Module.End ℂ (Fock n), LinearMap.lTensor N f = Module.End.lTensorAlgHom ℂ (Fock n) N f :=
    fun f => rfl
  unfold sgE
  split_ifs <;> rw [e] <;> simp only [map_sum, map_mul, map_neg, map_zero] <;> rfl

theorem tcoef_eq_sum (φ : Module.Dual ℂ (Fock n)) (y : TensorProduct ℂ N (Fock n)) :
    tcoef φ y = ∑ s : Finset (Fin (n * n)), φ (fockBasis n s) • tcoef ((fockBasis n).coord s) y := by
  conv_lhs => rw [tcoef_expand y]
  simp only [map_sum, tcoef_tmul]

theorem tco_actDiag (E : Fin n → Fin n → Module.End ℂ N) (X : Matrix (Fin n) (Fin n) ℂ)
    (y : TensorProduct ℂ N (Fock n)) (s : Finset (Fin (n * n))) :
    tcoef ((fockBasis n).coord s) (actM (diagE ε (eT E) cpT cmT) X y) =
      actM E X (tcoef ((fockBasis n).coord s) y) + tcoef ((fockBasis n).coord s ∘ₗ sgX ε X) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul m f =>
    simp only [actM, diagE, sgE_cpT, eT, sgX, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply,
      TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.id_apply, map_sum, map_smul, map_add,
      tcoef_tmul, LinearMap.coe_comp, Function.comp_apply, smul_add, Finset.sum_add_distrib, smul_smul]
    rw [Finset.smul_sum, Finset.sum_smul]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [smul_smul, mul_comm]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [smul_eq_mul]
  | add y y' hy hy' =>
    rw [map_add, map_add, hy, hy', map_add, map_add, map_add]
    abel

end T

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem tco_wK (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    (y : TensorProduct ℂ D (Fock n)) (s : Finset (Fin (n * n))) :
    tcoef ((fockBasis n).coord s) (wK hD hk y) =
      ∑ s', (fockBasis n).coord s (ff ε k (fockBasis n s')) • sigD hD hk (tcoef ((fockBasis n).coord s') y) := by
  conv_lhs => rw [tcoef_expand y]
  simp only [map_sum, wK, TensorProduct.map_tmul, tcoef_tmul, AlgHom.toLinearMap_apply]

theorem tco_wK_hasDeriv (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inK ε X) (y : TensorProduct ℂ D (Fock n)) (s : Finset (Fin (n * n))) :
    HasDerivAt (fun t : ℝ => ((tcoef ((fockBasis n).coord s)
        (wK hD (exp_mem_Kset (USum.inK_real_smul hX t)) y) : D) : H))
      ((tcoef ((fockBasis n).coord s) (actM (diagE ε (eT E) cpT cmT) X y) : D) : H) 0 := by
  have hXh : Xᴴ = -X := ((HW.inK_iff' ε X).1 hX).1
  have hfun : (fun t : ℝ => ((tcoef ((fockBasis n).coord s)
      (wK hD (exp_mem_Kset (USum.inK_real_smul hX t)) y) : D) : H)) =
      fun t : ℝ => ∑ s', (fockBasis n).coord s (ff ε (NormedSpace.exp ((t : ℂ) • X)) (fockBasis n s')) •
        σ (NormedSpace.exp ((t : ℂ) • X)) ((tcoef ((fockBasis n).coord s') y : D) : H) := by
    funext t
    rw [tco_wK, Submodule.coe_sum]
    rfl
  rw [hfun]
  have hc : ∀ s', HasDerivAt (fun t : ℝ => (fockBasis n).coord s (ff ε (NormedSpace.exp ((t : ℂ) • X))
      (fockBasis n s'))) ((fockBasis n).coord s (sgX ε X (fockBasis n s'))) 0 := by
    intro s'
    have := hasDerivAt_pi.1 (ff_exp_hasDeriv (ε := ε) hXh (fockBasis n s')) s
    simpa only [Module.Basis.equivFun_apply, Module.Basis.coord_apply] using this
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun s' _ =>
    (hc s').fun_smul (hD.deriv X hX.1 (tcoef ((fockBasis n).coord s') y))
  convert h using 1
  have h0 : NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1 := by simp
  simp only [h0, ff_one, AlgHom.id_apply, hσ.1.1, ContinuousLinearMap.one_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  rw [tco_actDiag, Submodule.coe_add, tcoef_eq_sum ((fockBasis n).coord s ∘ₗ sgX ε X) y, Submodule.coe_sum,
    Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single s (fun b _ hb => by simp [hb]) (by simp)]
    simp

def coordH : TensorProduct ℂ D (Fock n) →ₗ[ℂ] (Finset (Fin (n * n)) → H) :=
  LinearMap.pi fun s => D.subtype ∘ₗ tcoef ((fockBasis n).coord s)

theorem coordH_apply (y : TensorProduct ℂ D (Fock n)) (s : Finset (Fin (n * n))) :
    coordH y s = ((tcoef ((fockBasis n).coord s) y : D) : H) := rfl

theorem coordH_injective : Function.Injective (coordH (D := D) (n := n)) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro y hy
  rw [LinearMap.mem_ker] at hy
  rw [Submodule.mem_bot, tcoef_expand y]
  refine Finset.sum_eq_zero fun s _ => ?_
  have : ((tcoef ((fockBasis n).coord s) y : D) : H) = 0 := congrFun hy s
  rw [show tcoef ((fockBasis n).coord s) y = 0 from Subtype.ext this, TensorProduct.zero_tmul]

theorem actDiag_mem_of_wK (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (S' : Submodule ℂ (TensorProduct ℂ D (Fock n))) (hS : FiniteDimensional ℂ S')
    (hK : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ S', wK hD hk y ∈ S')
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) {y : TensorProduct ℂ D (Fock n)} (hy : y ∈ S') :
    actM (diagE ε (eT E) cpT cmT) X y ∈ S' := by
  let T := S'.map (coordH (D := D) (n := n))
  have : FiniteDimensional ℂ T := Module.Finite.map S' coordH
  have hTc : IsClosed (T : Set (Finset (Fin (n * n)) → H)) := Submodule.closed_of_finiteDimensional T
  have hder : HasDerivAt (fun t : ℝ => coordH (wK hD (exp_mem_Kset (USum.inK_real_smul hX t)) y))
      (coordH (actM (diagE ε (eT E) cpT cmT) X y)) 0 :=
    hasDerivAt_pi.2 fun s => tco_wK_hasDeriv hσ hD hX y s
  have h1 : ∀ t : ℝ, coordH (wK hD (exp_mem_Kset (USum.inK_real_smul hX t)) y) ∈ T :=
    fun t => Submodule.mem_map_of_mem (hK _ _ y hy)
  have hmem : coordH (actM (diagE ε (eT E) cpT cmT) X y) ∈ T :=
    hTc.mem_of_tendsto hder.tendsto_slope_zero (Filter.Eventually.of_forall fun t =>
      Submodule.smul_of_tower_mem _ _ (Submodule.sub_mem _ (h1 _) (h1 _)))
  obtain ⟨w, hw, hweq⟩ := Submodule.mem_map.1 hmem
  rwa [coordH_injective hweq] at hw

theorem diagE_mem_of_wK (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (S' : Submodule ℂ (TensorProduct ℂ D (Fock n))) (hS : FiniteDimensional ℂ S')
    (hK : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ S', wK hD hk y ∈ S')
    {a b : Fin n} (hab : ε a = ε b) {y : TensorProduct ℂ D (Fock n)} (hy : y ∈ S') :
    diagE ε (eT E) cpT cmT a b y ∈ S' := by
  have h1 := actDiag_mem_of_wK hσ hD S' hS hK (USum.inK_zM hab 1) hy
  have h2 := actDiag_mem_of_wK hσ hD S' hS hK (USum.inK_zM hab Complex.I) hy
  rw [USum.actM_zM] at h1 h2
  have gen : ∀ x y : TensorProduct ℂ D (Fock n),
      x = (1 / 2 : ℂ) • ((x - y) - Complex.I • (Complex.I • x - (-Complex.I) • y)) := by
    intro x y
    rw [smul_sub Complex.I, smul_smul, smul_smul, show Complex.I * Complex.I = -1 from Complex.I_mul_I,
      show Complex.I * -Complex.I = 1 by rw [mul_neg, Complex.I_mul_I, neg_neg]]
    module
  have key : diagE ε (eT E) cpT cmT a b y = (1 / 2 : ℂ) •
      ((((1 : ℂ) • diagE ε (eT E) cpT cmT a b - star (1 : ℂ) • diagE ε (eT E) cpT cmT b a) y) -
        Complex.I • (((Complex.I • diagE ε (eT E) cpT cmT a b - star Complex.I • diagE ε (eT E) cpT cmT b a)) y)) := by
    simp only [Complex.star_def, Complex.conj_I, map_one]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, one_smul]
    exact gen _ _
  rw [key]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ h1 (Submodule.smul_mem _ _ h2))

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

section
noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

section Straight

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}

theorem lowerWord_weight (hE : Formalism.REAL.KRel ε E) {μ : Fin n → ℝ} {y : M}
    (hy : ∀ a, E a a y = (μ a : ℂ) • y) :
    ∀ (l : List (Fin n × Fin n)), (∀ p ∈ l, IsKLow ε p) → ∀ (a : Fin n),
      E a a (lowWord E y l) = (lowWt μ l a : ℂ) • lowWord E y l
  | [], _, a => by simpa [lowWord, lowWt] using hy a
  | p :: l, hl, a => by
    obtain ⟨c, d⟩ := p
    have hcd : IsKLow ε (c, d) := hl _ (List.mem_cons_self ..)
    have h := congrArg (fun X : Module.End ℂ M => X (lowWord E y l)) (hE a a c d rfl hcd.2)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [lowerWord_weight hE hy l (fun q hq => hl q (List.mem_cons_of_mem _ hq)) a, map_smul,
      sub_eq_iff_eq_add] at h
    simp only [lowWord, lowWt]
    rw [h]
    simp only [root, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
    by_cases hac : a = c <;> by_cases had : a = d
    · subst hac; subst had; simp
    · subst hac
      simp only [if_neg had, if_neg (Ne.symm had), LinearMap.zero_apply, sub_zero]
      push_cast
      module
    · subst had
      simp only [if_neg hac, LinearMap.zero_apply, zero_sub]
      push_cast
      module
    · simp [hac, had, Ne.symm had]

theorem compactLoweringSpan_diag_stable (hE : Formalism.REAL.KRel ε E) {μ : Fin n → ℝ} {y : M}
    (hy : ∀ a, E a a y = (μ a : ℂ) • y) (a : Fin n) :
    ∀ x ∈ kLowSpan ε E y, E a a x ∈ kLowSpan ε E y := by
  have : kLowSpan ε E y ≤ (kLowSpan ε E y).comap (E a a) := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨l, hl, rfl⟩
    show E a a (lowWord E y l) ∈ kLowSpan ε E y
    rw [lowerWord_weight hE hy l hl a]
    exact Submodule.smul_mem _ _ (lowWord_mem hl)
  exact fun x hx => this hx

theorem lowerWord_mem_span_of_ge (hE : Formalism.REAL.KRel ε E) {μ : Fin n → ℝ} {y : M}
    (hy : ∀ a, E a a y = (μ a : ℂ) • y)
    {l : List (Fin n × Fin n)} (hl : ∀ p ∈ l, IsKLow ε p) {a b : Fin n} (hab : b ≤ a)
    (hε : ε a = ε b) : E a b (lowWord E y l) ∈ kLowSpan ε E y := by
  rcases hab.lt_or_eq with h | rfl
  · exact kLowSpan_low_stable (c := a) (d := b) ⟨h, hε⟩ _ (lowWord_mem hl)
  · exact compactLoweringSpan_diag_stable hE hy b _ (lowWord_mem hl)

theorem lowerWord_raise_mem_span (hE : Formalism.REAL.KRel ε E) {μ : Fin n → ℝ} {y : M} (hy : IsKHWVec ε E μ y) :
    ∀ (l : List (Fin n × Fin n)), (∀ p ∈ l, IsKLow ε p) → ∀ a b : Fin n, a < b → ε a = ε b →
      E a b (lowWord E y l) ∈ kLowSpan ε E y
  | [], _, a, b, hab, hε => by
    simp only [lowWord]
    rw [hy.2 a b hab hε]
    exact Submodule.zero_mem _
  | p :: l, hl, a, b, hab, hε => by
    obtain ⟨c, d⟩ := p
    have hcd : IsKLow ε (c, d) := hl _ (List.mem_cons_self ..)
    have hl' : ∀ p ∈ l, IsKLow ε p := fun p hp => hl p (List.mem_cons_of_mem _ hp)
    have ih := lowerWord_raise_mem_span hE hy l hl'
    have key : ∀ a' b' : Fin n, ε a' = ε b' → E a' b' (lowWord E y l) ∈ kLowSpan ε E y := by
      intro a' b' h'
      rcases lt_or_ge a' b' with h | h
      · exact ih a' b' h h'
      · exact lowerWord_mem_span_of_ge hE hy.1 hl' h h'
    have h := congrArg (fun X : Module.End ℂ M => X (lowWord E y l)) (hE a b c d hε hcd.2)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [sub_eq_iff_eq_add] at h
    simp only [lowWord]
    rw [h]
    refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) (kLowSpan_low_stable hcd _ (ih a b hab hε))
    · split_ifs with hbc
      · subst hbc; exact key a d (hε.trans hcd.2)
      · simp
    · split_ifs with hda
      · subst hda; exact key c b (hcd.2.trans hε)
      · simp

theorem compactLoweringSpan_kStable (hE : Formalism.REAL.KRel ε E) {μ : Fin n → ℝ} {y : M} (hy : IsKHWVec ε E μ y) :
    IsKStableSub ε E (kLowSpan ε E y) := by
  intro a b hab
  rcases lt_or_ge a b with h | h
  · have : kLowSpan ε E y ≤ (kLowSpan ε E y).comap (E a b) := by
      refine Submodule.span_le.2 ?_
      rintro x ⟨l, hl, rfl⟩
      exact lowerWord_raise_mem_span hE hy l hl a b h hab
    exact fun x hx => this hx
  · rcases h.lt_or_eq with h | rfl
    · exact kLowSpan_low_stable ⟨h, hab⟩
    · exact compactLoweringSpan_diag_stable hE hy.1 b

end Straight


end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

section T

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem tco_diagE (E : Fin n → Fin n → Module.End ℂ N) (a b : Fin n)
    (y : TensorProduct ℂ N (Fock n)) (s : Finset (Fin (n * n))) :
    tcoef ((fockBasis n).coord s) (diagE ε (eT E) cpT cmT a b y) =
      E a b (tcoef ((fockBasis n).coord s) y) +
        tcoef ((fockBasis n).coord s ∘ₗ sgE ε (cpFock (n := n)) cmFock a b) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul m f =>
    simp only [diagE, sgE_cpT, eT, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.lTensor_tmul,
      LinearMap.id_apply, map_add, tcoef_tmul, LinearMap.coe_comp, Function.comp_apply, map_smul]
  | add y y' hy hy' =>
    rw [map_add, map_add, hy, hy', map_add, map_add, map_add]
    abel

theorem tco_diagE_wt (E : Fin n → Fin n → Module.End ℂ N) (a : Fin n)
    (y : TensorProduct ℂ N (Fock n)) (s : Finset (Fin (n * n))) :
    tcoef ((fockBasis n).coord s) (diagE ε (eT E) cpT cmT a a y) =
      E a a (tcoef ((fockBasis n).coord s) y) + ((fockWt ε s a : ℝ) : ℂ) • tcoef ((fockBasis n).coord s) y := by
  rw [tco_diagE, tcoef_eq_sum ((fockBasis n).coord s ∘ₗ sgE ε (cpFock (n := n)) cmFock a a) y]
  congr 1
  rw [Finset.sum_eq_single s]
  · simp [fockBasis_wt]
  · intro b _ hb
    simp [fockBasis_wt, Finsupp.single_apply, hb]
  · simp

end T

theorem modeChar_exp (θ : Fin n → ℝ) (x : Fin n × Fin n) :
    modeChar ε (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) x =
      Complex.exp (((∑ a, modeWt ε x a * θ a : ℝ) : ℂ) * Complex.I) := by
  unfold modeChar modeWt
  by_cases h : IsPhys ε x
  · rw [if_pos h, if_pos (show ε x.1 = true ∧ ε x.2 = false from h), Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [root, Pi.sub_apply, Pi.single_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  · rw [if_neg h, if_neg (show ¬(ε x.1 = true ∧ ε x.2 = false) from h)]
    simp

theorem prod_modeChar_exp (θ : Fin n → ℝ) (s : Finset (Fin (n * n))) :
    ∏ m ∈ s, modeChar ε (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) (finProdFinEquiv.symm m) =
      Complex.exp (((∑ a, fockWt ε s a * θ a : ℝ) : ℂ) * Complex.I) := by
  simp only [modeChar_exp]
  rw [← Complex.exp_sum]
  congr 1
  rw [← Finset.sum_mul, ← Complex.ofReal_sum]
  congr 2
  simp only [fockWt, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem diag_mem_Kset' (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset ε :=
  bwt_diag_mem_Kset ε θ

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem wK_diag_wt (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {μ : Fin n → ℝ}
    {y : TensorProduct ℂ D (Fock n)} (hy : ∀ a, diagE ε (eT E) cpT cmT a a y = ((μ a : ℝ) : ℂ) • y)
    (θ : Fin n → ℝ) :
    wK hD (diag_mem_Kset' ε θ) y = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • y := by
  apply coordH_injective
  funext s
  rw [map_smul, Pi.smul_apply, coordH_apply, coordH_apply, tco_wK]
  rw [Finset.sum_eq_single s]
  · rw [ff_diag, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
      smul_eq_mul, mul_one, prod_modeChar_exp]
    have hts : ∀ a, E a a (tcoef ((fockBasis n).coord s) y) =
        (((μ - fockWt ε s) a : ℝ) : ℂ) • tcoef ((fockBasis n).coord s) y := by
      intro a
      have h := congrArg (tcoef ((fockBasis n).coord s)) (hy a)
      rw [tco_diagE_wt, map_smul] at h
      rw [Pi.sub_apply, Complex.ofReal_sub, sub_smul, ← h]
      abel
    have hw := (isWtOn_iff hσ hD (tcoef ((fockBasis n).coord s) y) (μ - fockWt ε s)).2 hts θ
      (bwt_diag_mem_Kset ε θ)
    rw [Submodule.coe_smul]
    change _ • σ _ _ = _
    rw [hw, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    simp only [Pi.sub_apply, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  · intro b _ hb
    rw [ff_diag, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
      if_neg hb, smul_zero, zero_smul]
  · simp

theorem bwtDiag_inK (ε : Fin n → Bool) (θ : Fin n → ℝ) : inK ε (bwtDiag θ) := by
  refine ⟨bwtDiag_inG ε θ, ?_⟩
  unfold bwtDiag Jm
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext a
  ring

theorem wK_congr (hD : IsDerivedOn ε σ D E) {k k' : Matrix (Fin n) (Fin n) ℂ} (h : k = k')
    (hk : k ∈ Kset ε) (hk' : k' ∈ Kset ε) (y : TensorProduct ℂ D (Fock n)) :
    wK hD hk y = wK hD hk' y := by
  subst h
  rfl

theorem diagE_wt_of_wK (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {μ : Fin n → ℝ}
    {y : TensorProduct ℂ D (Fock n)}
    (hy : ∀ θ : Fin n → ℝ, wK hD (diag_mem_Kset' ε θ) y = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • y)
    (a : Fin n) : diagE ε (eT E) cpT cmT a a y = ((μ a : ℝ) : ℂ) • y := by
  set θ : Fin n → ℝ := Pi.single a 1 with hθ
  have hX := bwtDiag_inK ε θ
  have hcurve : ∀ t : ℝ, coordH (wK hD (exp_mem_Kset (USum.inK_real_smul hX t)) y) =
      Complex.exp (((t * μ a : ℝ) : ℂ) * Complex.I) • coordH y := by
    intro t
    rw [wK_congr hD (bwt_exp θ t) _ (diag_mem_Kset' ε (fun b => t * θ b)), hy, map_smul]
    congr 4
    rw [Finset.sum_eq_single a (fun b _ hb => by simp [hθ, Pi.single_apply, hb]) (by simp)]
    simp [hθ]
    ring
  have hder1 : HasDerivAt (fun t : ℝ => coordH (wK hD (exp_mem_Kset (USum.inK_real_smul hX t)) y))
      (coordH (actM (diagE ε (eT E) cpT cmT) (bwtDiag θ) y)) 0 :=
    hasDerivAt_pi.2 fun s => tco_wK_hasDeriv hσ hD hX y s
  have he : HasDerivAt (fun t : ℝ => Complex.exp (((t * μ a : ℝ) : ℂ) * Complex.I))
      (((μ a : ℝ) : ℂ) * Complex.I) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => ((t * μ a : ℝ) : ℂ)) ((1 * μ a : ℝ) : ℂ) 0 :=
      ((hasDerivAt_id (0 : ℝ)).mul_const (μ a)).ofReal_comp
    have h2 := (h1.mul_const Complex.I).cexp
    convert h2 using 1
    simp
  have hder2 := he.smul_const (coordH y)
  rw [funext hcurve] at hder1
  have heq := hder1.unique hder2
  have h2 : actM (diagE ε (eT E) cpT cmT) (bwtDiag θ) y = (((μ a : ℝ) : ℂ) * Complex.I) • y :=
    coordH_injective (by rw [heq, map_smul])
  rw [bwtDiag, bwt_actM_diag, LinearMap.sum_apply,
    Finset.sum_eq_single a (fun b _ hb => by simp [hθ, Pi.single_apply, hb]) (by simp)] at h2
  simp only [hθ, Pi.single_eq_same, Complex.ofReal_one, one_mul, LinearMap.smul_apply] at h2
  have h3 := congrArg (fun v => (-Complex.I) • v) h2
  simp only [smul_smul] at h3
  have hI : -Complex.I * Complex.I = 1 := by rw [neg_mul, Complex.I_mul_I, neg_neg]
  have hI' : -Complex.I * (((μ a : ℝ) : ℂ) * Complex.I) = ((μ a : ℝ) : ℂ) := by
    linear_combination (-((μ a : ℝ) : ℂ)) * Complex.I_mul_I
  rw [hI, one_smul, hI'] at h3
  exact h3

section Orth

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem kLow_wt_eq_lowWt {A : Fin n → Fin n → Module.End ℂ (TensorProduct ℂ M (Fock n))}
    (hK : Formalism.REAL.KRel ε A)
    (hA : ∀ (a : Fin n) (y y' : TensorProduct ℂ M (Fock n)), tform (A a a y) y' = tform y (A a a y'))
    {γ : Fin n → ℝ} {z : TensorProduct ℂ M (Fock n)} (hz : IsKHWVec ε A γ z)
    {y : TensorProduct ℂ M (Fock n)} (hy : y ∈ kLowSpan ε A z) (hy0 : y ≠ 0) {μ : Fin n → ℝ}
    (hμ : ∀ a, A a a y = ((μ a : ℝ) : ℂ) • y) :
    ∃ l : List (Fin n × Fin n), (∀ p ∈ l, IsKLow ε p) ∧ μ = lowWt γ l := by
  by_contra hne
  push Not at hne
  have horth : ∀ l : List (Fin n × Fin n), (∀ p ∈ l, IsKLow ε p) → tform y (lowWord A z l) = 0 := by
    intro l hl
    obtain ⟨a, ha⟩ : ∃ a, μ a ≠ lowWt γ l a := by
      by_contra h
      push Not at h
      exact hne l hl (funext h)
    have h1 := hA a y (lowWord A z l)
    rw [hμ a, lowerWord_weight hK hz.1 l hl a, tensorForm_smul_left, tform_smul_right, Complex.star_def,
      Complex.conj_ofReal] at h1
    have h2 : (((μ a : ℝ) : ℂ) - ((lowWt γ l a : ℝ) : ℂ)) * tform y (lowWord A z l) = 0 := by
      rw [sub_mul, h1, sub_self]
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd (by exact_mod_cast sub_eq_zero.1 h) ha
    · exact h
  have hall : ∀ w ∈ kLowSpan ε A z, tform y w = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      exact horth l hl
    | zero => simp [tform]
    | add x x' _ _ hx hx' => rw [tform_add_right, hx, hx', add_zero]
    | smul c x _ hx => rw [tform_smul_right, hx, mul_zero]
  have := tform_self_re_pos hy0
  rw [hall y hy] at this
  simp at this

end Orth

theorem cdom_lowWt (γ : Fin n → ℝ) :
    ∀ l : List (Fin n × Fin n), (∀ p ∈ l, IsKLow ε p) → Formalism.MainNotions.S.CDom ε (lowWt γ l) γ
  | [], _ => ⟨fun _ _ => 0, fun a b h => absurd rfl h, by simp [lowWt]⟩
  | p :: l, hl => by
    obtain ⟨c, hc, heq⟩ := cdom_lowWt γ l fun q hq => hl q (List.mem_cons_of_mem _ hq)
    obtain ⟨c0, d0⟩ := p
    have hp : IsKLow ε (c0, d0) := hl _ (List.mem_cons_self ..)
    refine ⟨fun a b => c a b + if a = d0 ∧ b = c0 then 1 else 0, ?_, ?_⟩
    · intro a b h
      by_cases h' : a = d0 ∧ b = c0
      · obtain ⟨rfl, rfl⟩ := h'
        exact ⟨hp.1, hp.2.symm⟩
      · dsimp only at h
        rw [if_neg h', add_zero] at h
        exact hc a b h
    · have hs : (∑ a, ∑ b, (((if a = d0 ∧ b = c0 then 1 else 0 : ℕ)) : ℝ) • Formalism.REAL.root a b) =
          Formalism.REAL.root d0 c0 := by
        rw [Finset.sum_eq_single d0 (fun a _ ha => Finset.sum_eq_zero fun b _ => by simp [ha]) (by simp),
          Finset.sum_eq_single c0 (fun b _ hb => by simp [hb]) (by simp)]
        simp
      simp only [Nat.cast_add, add_smul, Finset.sum_add_distrib, hs, ← heq, lowWt]
      ext i
      simp only [Pi.sub_apply, Pi.add_apply, root, Formalism.REAL.root]
      ring

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

theorem kset_mem_UJset {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : k ∈ UJset ε := by
  show kᴴ * Jm ε * k = Jm ε
  rw [mul_assoc, ← hk.2, ← mul_assoc, ← Matrix.star_eq_conjTranspose,
    (Matrix.mem_unitaryGroup_iff').1 hk.1, one_mul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem inner_sigD (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) (u v : D) : inner ℂ (sigD hD hk u) (sigD hD hk v) = inner ℂ u v := by
  let Lk : H →ₗᵢ[ℂ] H := { toLinearMap := (σ k : H →ₗ[ℂ] H), norm_map' := hσ.2.1 k (kset_mem_UJset hk) }
  rw [Submodule.coe_inner, Submodule.coe_inner]
  exact Lk.inner_map_map u v

theorem coord_ff_basis (k : Matrix (Fin n) (Fin n) ℂ) (s s' : Finset (Fin (n * n))) :
    (fockBasis n).coord s (ff ε k (fockBasis n s')) = ffMat ε k s s' := by
  rw [ffMat, LinearMap.toMatrix_apply, Module.Basis.coord_apply, AlgHom.toLinearMap_apply]

theorem tform_wK (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) (y y' : TensorProduct ℂ D (Fock n)) :
    tform (wK hD hk y) (wK hD hk y') = tform y y' := by
  have hU := (Matrix.mem_unitaryGroup_iff').1 (ffMat_unitary (ε := ε) hk)
  unfold tform
  simp only [tco_wK, coord_ff_basis, sum_inner, inner_sum, inner_smul_left, inner_smul_right, inner_sigD hσ hD hk,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [Finset.sum_comm]
  have h1 : ∀ s'' : Finset (Fin (n * n)), ∑ x, ffMat ε k x s' * ((starRingEnd ℂ) (ffMat ε k x s'') *
      inner ℂ (tcoef ((fockBasis n).coord s'') y) (tcoef ((fockBasis n).coord s') y')) =
      (1 : Matrix (Finset (Fin (n * n))) (Finset (Fin (n * n))) ℂ) s'' s' *
        inner ℂ (tcoef ((fockBasis n).coord s'') y) (tcoef ((fockBasis n).coord s') y') := by
    intro s''
    rw [← hU, Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.star_apply, Complex.star_def]
    ring
  rw [Finset.sum_congr rfl fun s'' _ => h1 s'']
  simp [Matrix.one_apply]

theorem sigD_one (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε) :
    sigD hD h1 = LinearMap.id := by
  ext v
  simp [sigD, hσ.1.1]

theorem wK_one (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε) :
    wK hD h1 = LinearMap.id := by
  rw [wK, sigD_one hσ hD h1, ff_one]
  exact TensorProduct.map_id

theorem wK_mul (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {a b : Matrix (Fin n) (Fin n) ℂ}
    (ha : a ∈ Kset ε) (hb : b ∈ Kset ε) (hab : a * b ∈ Kset ε) :
    wK hD hab = wK hD ha ∘ₗ wK hD hb := by
  have hs : sigD hD hab = sigD hD ha ∘ₗ sigD hD hb := by
    ext v
    simp [sigD, hσ.1.2 a (kset_mem_UJset ha) b (kset_mem_UJset hb)]
  rw [wK, wK, wK, hs, ff_mul ha hb, ← TensorProduct.map_comp]
  rfl

theorem one_mem_Kset' : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε :=
  ⟨one_mem _, by rw [one_mul, mul_one]⟩

theorem mul_mem_Kset' {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ Kset ε) (hb : b ∈ Kset ε) : a * b ∈ Kset ε :=
  ⟨mul_mem ha.1 hb.1, by rw [mul_assoc, hb.2, ← mul_assoc, ha.2, mul_assoc]⟩

section TSubSec

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

def TSub (S : Submodule ℂ (TensorProduct ℂ M (Fock n))) : Type _ := S

variable {S : Submodule ℂ (TensorProduct ℂ M (Fock n))}

instance : AddCommGroup (TSub S) := inferInstanceAs (AddCommGroup S)

instance : Module ℂ (TSub S) := inferInstanceAs (Module ℂ S)

def tsubVal (S : Submodule ℂ (TensorProduct ℂ M (Fock n))) : TSub S →ₗ[ℂ] TensorProduct ℂ M (Fock n) :=
  S.subtype

theorem tsubVal_injective : Function.Injective (tsubVal S) := Subtype.val_injective

theorem tsubVal_mem (x : TSub S) : tsubVal S x ∈ S := (x : S).2

instance tsubCore : InnerProductSpace.Core ℂ (TSub S) where
  inner x y := tform (tsubVal S x) (tsubVal S y)
  conj_inner_symm x y := tform_conj _ _
  re_inner_nonneg x := by
    by_cases h : tsubVal S x = 0
    · rw [h]
      simp [tform]
    · exact (tform_self_re_pos h).le
  add_left x y z := by
    simp only [map_add]
    exact tform_add_left _ _ _
  smul_left x y r := by
    simp only [map_smul]
    exact tensorForm_smul_left r _ _
  definite x h := by
    by_contra hx
    have hx' : tsubVal S x ≠ 0 := fun h0 => hx (tsubVal_injective (h0.trans (map_zero _).symm))
    have h' : tform (tsubVal S x) (tsubVal S x) = 0 := h
    have := tform_self_re_pos hx'
    rw [h'] at this
    simp at this

instance : NormedAddCommGroup (TSub S) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

instance : InnerProductSpace ℂ (TSub S) := InnerProductSpace.ofCore _

theorem tsub_inner (x y : TSub S) : inner ℂ x y = tform (tsubVal S x) (tsubVal S y) := rfl

instance [h : FiniteDimensional ℂ S] : FiniteDimensional ℂ (TSub S) := h

end TSubSec

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

def tOp (hD : IsDerivedOn ε σ D E) {S : Submodule ℂ (TensorProduct ℂ D (Fock n))} [FiniteDimensional ℂ S]
    (hSK : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ S, wK hD hk y ∈ S)
    (k : Matrix (Fin n) (Fin n) ℂ) : TSub S →L[ℂ] TSub S :=
  @dite _ (k ∈ Kset ε) (Classical.propDecidable _)
    (fun hk => LinearMap.toContinuousLinearMap
      (((wK hD hk).restrict (hSK k hk) : S →ₗ[ℂ] S) : TSub S →ₗ[ℂ] TSub S)) (fun _ => 0)

section Op

variable (hD : IsDerivedOn ε σ D E) {S : Submodule ℂ (TensorProduct ℂ D (Fock n))} [FiniteDimensional ℂ S]
  (hSK : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ S, wK hD hk y ∈ S)

theorem tOp_apply {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (x : TSub S) :
    tsubVal S (tOp hD hSK k x) = wK hD hk (tsubVal S x) := by
  simp only [tOp, dif_pos hk]
  rfl

theorem tOp_isURepOn (hσ : IsURepOn (UJset ε) σ) :
    Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) (tOp hD hSK) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · ext x
    apply tsubVal_injective
    rw [tOp_apply hD hSK one_mem_Kset', wK_one hσ hD]
    rfl
  · intro a ha b hb
    ext x
    apply tsubVal_injective
    rw [tOp_apply hD hSK (mul_mem_Kset' ha hb), ContinuousLinearMap.comp_apply, tOp_apply hD hSK ha,
      tOp_apply hD hSK hb, wK_mul hσ hD ha hb]
    rfl
  · intro g hg v
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), tsub_inner, tsub_inner,
      tOp_apply hD hSK hg, tform_wK hσ hD hg]
  · intro v
    have hΨ : Set.EqOn (fun g => coordH (tsubVal S (tOp hD hSK g v)))
        (fun g => fun s => ∑ s', ffMat ε g s s' • σ g ((tcoef ((fockBasis n).coord s') (tsubVal S v) : D) : H))
        (Formalism.REAL.Kset ε) := by
      intro g hg
      have hg' : g ∈ Kset ε := hg
      funext s
      simp only
      rw [tOp_apply hD hSK hg', coordH_apply, tco_wK, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun s' _ => ?_
      rw [coord_ff_basis]
      rfl
    have hc : ContinuousOn (fun g => coordH (tsubVal S (tOp hD hSK g v))) (Formalism.REAL.Kset ε) := by
      refine ContinuousOn.congr ?_ hΨ
      refine continuousOn_pi.2 fun s => continuousOn_finsetSum _ fun s' _ => ?_
      exact (ffMat_continuous s s').continuousOn.smul
        ((hσ.2.2 _).mono fun g hg => kset_mem_UJset hg)
    have hinj : Function.Injective (coordH ∘ₗ tsubVal S) := coordH_injective.comp tsubVal_injective
    let e := LinearEquiv.ofInjective _ hinj
    have hcont : Continuous e.symm := LinearMap.continuous_of_finiteDimensional e.symm.toLinearMap
    have hfe : (fun g => tOp hD hSK g v) =
        fun g => e.symm ⟨(coordH ∘ₗ tsubVal S) (tOp hD hSK g v), LinearMap.mem_range_self _ _⟩ := by
      funext g
      refine (e.symm_apply_apply (tOp hD hSK g v)).symm.trans ?_
      congr 1
    rw [hfe, continuousOn_iff_continuous_restrict]
    exact hcont.comp ((continuousOn_iff_continuous_restrict.1 hc).subtype_mk _)

end Op

section KType

variable (hD : IsDerivedOn ε σ D E) {S : Submodule ℂ (TensorProduct ℂ D (Fock n))} [FiniteDimensional ℂ S]
  (hSK : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ S, wK hD hk y ∈ S)

theorem tOp_trace {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    LinearMap.trace ℂ (TSub S) (tOp hD hSK k : TSub S →ₗ[ℂ] TSub S) =
      LinearMap.trace ℂ S ((wK hD hk).restrict (hSK k hk)) := by
  simp only [tOp, dif_pos hk]
  rfl

theorem tOp_isKTypeOf (hσ : IsURepOn (UJset ε) σ) {γ : Fin n → ℝ}
    (hS : IsKIrrHW ε (diagE ε (eT E) cpT cmT) γ S) :
    Formalism.MainNotions.S.IsKTypeOf ε (tOp hD hSK) γ ⊤ := by
  classical
  have hE : IsGlRep E := hD.glRep
  have hU : IsInfUnitary ε E := isInfUnitary_of_isDerivedOn hσ hD
  have hKA : Formalism.REAL.KRel ε (diagE ε (eT E) cpT cmT) :=
    fun a b c d hab hcd => diagAction_commutator (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) ε a b c d hab hcd
  obtain ⟨_, hSs, hirr, w, hwS, hw0, hwK⟩ := hS
  have hSeq : kLowSpan ε (diagE ε (eT E) cpT cmT) w = S := by
    have hle := kLowSpan_le hSs hwS
    rcases hirr _ hle (compactLoweringSpan_kStable hKA hwK) with h | h
    · exfalso
      apply hw0
      have := self_mem_kLowSpan (ε := ε) (E := diagE ε (eT E) cpT cmT) w
      rw [h, Submodule.mem_bot] at this
      exact this
    · exact h
  refine ⟨inferInstance, fun g _ v _ => Submodule.mem_top, ?_, ?_, ?_⟩
  · intro S'' _ hK''
    let P : Submodule ℂ (TensorProduct ℂ D (Fock n)) := S''.map (tsubVal S)
    have hPS : P ≤ S := by
      rintro _ ⟨x, _, rfl⟩
      exact tsubVal_mem x
    have hPfd : FiniteDimensional ℂ P := Module.Finite.map S'' (tsubVal S)
    have hPK : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ P, wK hD hk y ∈ P := by
      rintro k hk _ ⟨x, hx, rfl⟩
      exact ⟨tOp hD hSK k x, hK'' k hk x hx, tOp_apply hD hSK hk x⟩
    have hPs : IsKStableSub ε (diagE ε (eT E) cpT cmT) P := fun a b hab y hy =>
      diagE_mem_of_wK hσ hD P hPfd hPK hab hy
    rcases hirr P hPS hPs with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      have : tsubVal S x ∈ P := ⟨x, hx, rfl⟩
      rw [h, Submodule.mem_bot] at this
      rw [Submodule.mem_bot]
      exact tsubVal_injective (this.trans (map_zero _).symm)
    · right
      rw [eq_top_iff]
      intro x _
      have hxP : tsubVal S x ∈ P := by
        rw [h]
        exact tsubVal_mem x
      obtain ⟨x', hx', hxx⟩ := hxP
      exact (tsubVal_injective hxx) ▸ hx'
  · refine ⟨(show TSub S from ⟨w, hwS⟩), Submodule.mem_top, ?_, ?_⟩
    · intro h
      apply hw0
      have := congrArg (tsubVal S) h
      rwa [map_zero] at this
    · intro θ _
      apply tsubVal_injective
      rw [tOp_apply hD hSK (diag_mem_Kset' ε θ), map_smul]
      exact wK_diag_wt hσ hD hwK.1 θ
  · intro μ v _ hv0 hwt
    have hy : ∀ θ : Fin n → ℝ, wK hD (diag_mem_Kset' ε θ) (tsubVal S v) =
        Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • tsubVal S v := by
      intro θ
      rw [← tOp_apply hD hSK (diag_mem_Kset' ε θ), hwt θ (bwt_diag_mem_Kset ε θ), map_smul]
    have hμ := diagE_wt_of_wK hσ hD hy
    have hvS : tsubVal S v ∈ kLowSpan ε (diagE ε (eT E) cpT cmT) w := hSeq ▸ tsubVal_mem v
    have hv0' : tsubVal S v ≠ 0 := fun h => hv0 (tsubVal_injective (h.trans (map_zero _).symm))
    obtain ⟨l, hl, rfl⟩ := kLow_wt_eq_lowWt hKA (fun a y y' => tensorForm_diagAction_adjoint hU rfl y y') hwK hvS hv0' hμ
    exact cdom_lowWt γ l hl

theorem tSub_nontrivial {γ : Fin n → ℝ} (hS : IsKIrrHW ε (diagE ε (eT E) cpT cmT) γ S) : Nontrivial (TSub S) := by
  obtain ⟨_, _, _, w, hwS, hw0, _⟩ := hS
  refine ⟨⟨(show TSub S from ⟨w, hwS⟩), 0, fun h => hw0 ?_⟩⟩
  have := congrArg (tsubVal S) h
  rwa [map_zero] at this

end KType

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

theorem ff_cmFock_nonphys {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) {j b : Fin n}
    (hjb : ¬(ε j = true ∧ ε b = false)) (f : Fock n) : cmFock j b (ff ε k f) = ff ε k (cmFock j b f) := by
  have hk' : kᴴ ∈ Kset ε := kset_conjTranspose hk
  have hkk : kᴴ * k = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (Matrix.mem_unitaryGroup_iff').1 hk.1
  have hkk' : k * kᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (Matrix.mem_unitaryGroup_iff).1 hk.1
  have hcomm : ∀ g : Fock n, ff ε kᴴ (cmFock j b g) = cmFock j b (ff ε kᴴ g) := by
    intro g
    rw [ff_cmFock_apply hk' j b g, Finset.sum_eq_single (j, b)]
    · simp [adMat, IsPhys, hjb]
    · intro z _ hz
      have : adMat ε kᴴ z (j, b) = 0 := by
        unfold adMat
        by_cases h1 : IsPhys ε z
        · rw [if_pos h1, if_neg (show ¬IsPhys ε (j, b) from hjb)]
        · rw [if_neg h1, if_neg hz]
      rw [this, star_zero, zero_smul]
    · simp
  have h1 : ff ε kᴴ (ff ε k f) = f := by
    rw [← AlgHom.comp_apply, ← ff_mul hk' hk, hkk, ff_one, AlgHom.id_apply]
  have h2 : ∀ g : Fock n, ff ε k (ff ε kᴴ g) = g := by
    intro g
    rw [← AlgHom.comp_apply, ← ff_mul hk hk', hkk', ff_one, AlgHom.id_apply]
  have := congrArg (ff ε k) (hcomm (ff ε k f))
  rw [h1, h2] at this
  exact this

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem cmT_wK (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) {j b : Fin n}
    (hjb : ¬(ε j = true ∧ ε b = false)) :
    cmT (N := D) j b ∘ₗ wK hD hk = wK hD hk ∘ₗ cmT j b := by
  apply TensorProduct.ext'
  intro v f
  simp only [LinearMap.comp_apply, wK, cmT, TensorProduct.map_tmul, LinearMap.id_apply,
    AlgHom.toLinearMap_apply, ff_cmFock_nonphys hk hjb]

theorem wK_physSub (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    {y : TensorProduct ℂ D (Fock n)} (hy : y ∈ physicalSubspace ε) : wK hD hk y ∈ physicalSubspace ε := by
  rw [mem_physicalSubspace_iff] at hy ⊢
  intro j b hjb
  have := LinearMap.congr_fun (cmT_wK hD hk hjb) y
  simp only [LinearMap.comp_apply] at this
  rw [this, hy j b hjb, map_zero]

theorem sigD_genSub (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {V : Submodule ℂ D}
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    {v : D} (hv : v ∈ genSub E V) : sigD hD hk v ∈ genSub E V := by
  let T : Submodule ℂ D := (genSub E V).comap (sigD hD hk)
  have hVG : V ≤ genSub E V := fun v hv => Submodule.mem_sInf.2 fun T hT => hT.1 hv
  have hT : genSub E V ≤ T := by
    refine sInf_le ⟨fun x hx => ?_, fun a b x hx => ?_⟩
    · obtain ⟨w, hw, hweq⟩ := hVK k hk x hx
      have : sigD hD hk x = w := Subtype.ext hweq.symm
      show sigD hD hk x ∈ genSub E V
      rw [this]
      exact hVG hw
    · show sigD hD hk (E a b x) ∈ genSub E V
      rw [sigD_E hσ hD hk a b x, actM]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply]
      exact Submodule.sum_mem _ fun c _ => Submodule.sum_mem _ fun d _ =>
        Submodule.smul_mem _ _ (generatedSub_stable E V c d hx)
  exact hT hv

theorem wK_tensFock_genSub (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {V : Submodule ℂ D}
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    {y : TensorProduct ℂ D (Fock n)} (hy : y ∈ tensFock (genSub E V)) : wK hD hk y ∈ tensFock (genSub E V) := by
  obtain ⟨x, rfl⟩ := hy
  let sG : genSub E V →ₗ[ℂ] genSub E V := (sigD hD hk).restrict fun v hv => sigD_genSub hσ hD hVK hk hv
  refine ⟨TensorProduct.map sG (ff ε k).toLinearMap x, ?_⟩
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
  show _ = (TensorProduct.map (sigD hD hk) (ff ε k).toLinearMap ∘ₗ
    TensorProduct.map (genSub E V).subtype LinearMap.id) x
  rw [← TensorProduct.map_comp]
  rfl

theorem wK_KK (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {V : Submodule ℂ D}
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε) :
    ∀ y ∈ LinearMap.ker (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) ⊓ tensFock (genSub E V) ⊓ physicalSubspace ε,
      wK hD hk y ∈ LinearMap.ker (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) ⊓ tensFock (genSub E V) ⊓ physicalSubspace ε := by
  rintro y ⟨⟨hyD, hyT⟩, hyP⟩
  refine ⟨⟨?_, wK_tensFock_genSub hσ hD hVK hk hyT⟩, wK_physSub hD hk hyP⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker] at hyD ⊢
  have h1 := LinearMap.congr_fun (wK_dOp hσ hD hk) y
  have h2 := LinearMap.congr_fun (wK_dOp' hσ hD hk) y
  simp only [Module.End.mul_apply] at h1 h2
  rw [LinearMap.add_apply, ← h1, ← h2, ← map_add, ← LinearMap.add_apply, hyD, map_zero]

theorem kType_clause {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {lam : Fin n → ℝ} {h : ℝ}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hint : ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) (hanti : StrictAnti lam)
    (hgap : GapAtLeast ε lam h) (hthr : thrStar ε < h) (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) :
    ∃ (W : Type) (_ : NormedAddCommGroup W) (_ : InnerProductSpace ℂ W) (_ : FiniteDimensional ℂ W)
      (T : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)),
      Nontrivial W ∧ Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T ∧ Formalism.MainNotions.S.IsKTypeOf ε T (gaW ε lam) ⊤ ∧
      ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε),
        LinearMap.trace ℂ W (T k : W →ₗ[ℂ] W) =
          LinearMap.trace ℂ (LinearMap.ker (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) ⊓ tensFock (genSub E V) ⊓
            physicalSubspace ε : Submodule ℂ (TensorProduct ℂ D (Fock n))) ((wK hD hk).restrict (wK_KK hσ hD hVK k hk)) := by
  obtain ⟨z, _, _, _, _, hKK, hirr⟩ := ker_D_eq_kLowSpan hσ hD hV hc hVK hint hanti hgap hthr hp hq
  have hirr' : IsKIrrHW ε (diagE ε (eT E) cpT cmT) (gaW ε lam)
      (LinearMap.ker (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) ⊓ tensFock (genSub E V) ⊓ physicalSubspace ε) := by
    rw [hKK]
    exact hirr
  have : FiniteDimensional ℂ
      (LinearMap.ker (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) ⊓ tensFock (genSub E V) ⊓ physicalSubspace ε :
        Submodule ℂ (TensorProduct ℂ D (Fock n))) := hirr'.1
  exact ⟨TSub _, inferInstance, inferInstance, inferInstance, tOp hD (wK_KK hσ hD hVK),
    tSub_nontrivial hirr', tOp_isURepOn hD _ hσ, tOp_isKTypeOf hD _ hσ hirr', fun k hk => tOp_trace hD _ hk⟩

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end
