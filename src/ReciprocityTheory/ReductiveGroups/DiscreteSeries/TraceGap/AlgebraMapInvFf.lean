import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.FockWeights

section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

def IsPhys (ε : Fin n → Bool) (x : Fin n × Fin n) : Prop := ε x.1 = true ∧ ε x.2 = false

instance (ε : Fin n → Bool) : DecidablePred (IsPhys ε) := fun x =>
  inferInstanceAs (Decidable (ε x.1 = true ∧ ε x.2 = false))

def adMat (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ := fun x y =>
  if IsPhys ε x then (if IsPhys ε y then k x.1 y.1 * star (k x.2 y.2) else 0)
  else if x = y then 1 else 0

def adPhys (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) :
    (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ) :=
  Matrix.mulVecLin (adMat ε k)

def ff (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) : Fock n →ₐ[ℂ] Fock n :=
  ExteriorAlgebra.map (adPhys ε k)

def cpV (v : Fin n × Fin n → ℂ) : Module.End ℂ (Fock n) :=
  LinearMap.mulLeft ℂ (ExteriorAlgebra.ι ℂ v)

def dualV (v : Fin n × Fin n → ℂ) : Module.Dual ℂ (Fin n × Fin n → ℂ) :=
  ∑ x, star (v x) • LinearMap.proj (R := ℂ) (φ := fun _ : Fin n × Fin n => ℂ) x

def cmV (v : Fin n × Fin n → ℂ) : Module.End ℂ (Fock n) :=
  CliffordAlgebra.contractLeft (dualV v)

def ffMat (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Finset (Fin (n * n))) (Finset (Fin (n * n))) ℂ :=
  LinearMap.toMatrix (fockBasis n) (fockBasis n) (ff ε k).toLinearMap

def IsPhysSet (ε : Fin n → Bool) (S : Finset (Fin (n * n))) : Prop :=
  ∀ m ∈ S, IsPhys ε (finProdFinEquiv.symm m)

instance (ε : Fin n → Bool) : DecidablePred (IsPhysSet ε) := fun S =>
  inferInstanceAs (Decidable (∀ m ∈ S, IsPhys ε (finProdFinEquiv.symm m)))

def strPhys (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ S ∈ univ.filter (IsPhysSet ε), (-1 : ℂ) ^ S.card * ffMat ε k S S

def physDet (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  Matrix.det (fun x y : {x : Fin n × Fin n // IsPhys ε x} =>
    (if x = y then 1 else 0) - k x.1.1 y.1.1 * star (k x.1.2 y.1.2))

def modeChar (ε : Fin n → Bool) (s : Fin n → ℂ) (x : Fin n × Fin n) : ℂ :=
  if IsPhys ε x then s x.1 * star (s x.2) else 1

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

theorem kset_entry_zero {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) {i j : Fin n}
    (h : ε i ≠ ε j) : k i j = 0 := by
  have h1 := congrFun (congrFun hk.2 i) j
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  have h2 : k i j * ((if ε j then (1 : ℂ) else -1) - (if ε i then 1 else -1)) = 0 := by
    linear_combination h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact h3
  · exfalso
    clear h1 h2 hk
    revert h h3
    cases ε i <;> cases ε j <;> norm_num

theorem adMat_mul {k k' : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (_hk' : k' ∈ Kset ε) :
    adMat ε (k * k') = adMat ε k * adMat ε k' := by
  ext x y
  rw [Matrix.mul_apply]
  by_cases hx : IsPhys ε x
  · by_cases hy : IsPhys ε y
    · simp only [adMat, hx, hy, if_true]
      rw [Fintype.sum_prod_type, Matrix.mul_apply, Matrix.mul_apply, star_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      by_cases hz : IsPhys ε (u, v)
      · simp only [hz, if_true, star_mul']
        ring
      · simp only [hz, if_false, zero_mul]
        have hz' : ¬ (ε u = true ∧ ε v = false) := hz
        by_cases hu : ε u = true
        · have hv : ε v ≠ false := fun hv => hz' ⟨hu, hv⟩
          have : k x.2 v = 0 := kset_entry_zero hk (by rw [hx.2]; exact Ne.symm hv)
          simp [this]
        · have : k x.1 u = 0 := kset_entry_zero hk (by rw [hx.1]; exact Ne.symm hu)
          simp [this]
    · simp only [adMat, hx, hy, if_true, if_false]
      refine (Finset.sum_eq_zero fun z _ => ?_).symm
      split_ifs <;> simp
  · simp only [adMat, hx, if_false, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem adPhys_mul {k k' : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (hk' : k' ∈ Kset ε) :
    adPhys ε (k * k') = adPhys ε k ∘ₗ adPhys ε k' := by
  rw [adPhys, adPhys, adPhys, adMat_mul hk hk', Matrix.mulVecLin_mul]

theorem ff_mul {k k' : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (hk' : k' ∈ Kset ε) :
    ff ε (k * k') = (ff ε k).comp (ff ε k') := by
  rw [ff, ff, ff, adPhys_mul hk hk', ExteriorAlgebra.map_comp_map]

theorem adMat_one : adMat ε (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext x y
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  by_cases hx : IsPhys ε (x1, x2) <;> by_cases hy : IsPhys ε (y1, y2)
  · simp only [adMat, hx, hy, if_true, Matrix.one_apply, Prod.mk.injEq]
    by_cases h1 : x1 = y1 <;> by_cases h2 : x2 = y2 <;> simp [h1, h2]
  · have : (x1, x2) ≠ (y1, y2) := fun h => hy (h ▸ hx)
    simp only [adMat, hx, hy, if_true, if_false, Matrix.one_apply, this]
  · simp only [adMat, hx, if_false, Matrix.one_apply]
  · simp only [adMat, hx, if_false, Matrix.one_apply]

theorem ff_one : ff ε 1 = AlgHom.id ℂ (Fock n) := by
  rw [ff, adPhys, adMat_one, Matrix.mulVecLin_one, ExteriorAlgebra.map_id]

theorem ff_comp_involute (k : Matrix (Fin n) (Fin n) ℂ) :
    (ff ε k).comp CliffordAlgebra.involute = CliffordAlgebra.involute.comp (ff ε k) := by
  apply ExteriorAlgebra.hom_ext
  refine LinearMap.ext fun m => ?_
  simp [ff, ExteriorAlgebra.map_apply_ι]

theorem ff_involute (k : Matrix (Fin n) (Fin n) ℂ) (x : Fock n) :
    ff ε k (CliffordAlgebra.involute x) = CliffordAlgebra.involute (ff ε k x) :=
  AlgHom.congr_fun (ff_comp_involute k) x

theorem map_contractLeft {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (f : M →ₗ[ℂ] N) (d : Module.Dual ℂ N) (x : ExteriorAlgebra ℂ M) :
    ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (d ∘ₗ f) x) =
      CliffordAlgebra.contractLeft d (ExteriorAlgebra.map f x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x m hx =>
    rw [CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul, hx, map_mul,
      ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul, LinearMap.comp_apply]

theorem cpFock_eq_cpV (i a : Fin n) : cpFock i a = cpV (Pi.single (i, a) (1 : ℂ)) := rfl

theorem dualV_single (x : Fin n × Fin n) :
    dualV (Pi.single x (1 : ℂ)) = LinearMap.proj (R := ℂ) (φ := fun _ : Fin n × Fin n => ℂ) x := by
  refine LinearMap.ext fun w => ?_
  simp [dualV, Pi.single_apply]

theorem cmFock_eq_cmV (i a : Fin n) : cmFock i a = cmV (Pi.single (i, a) (1 : ℂ)) := by
  rw [cmV, dualV_single]
  rfl

theorem ff_cpV (k : Matrix (Fin n) (Fin n) ℂ) (v : Fin n × Fin n → ℂ) :
    (ff ε k).toLinearMap * cpV v = cpV (adPhys ε k v) * (ff ε k).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  simp only [Module.End.mul_apply, cpV, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply, map_mul, ff,
    ExteriorAlgebra.map_apply_ι]

theorem adMat_conjTranspose (k : Matrix (Fin n) (Fin n) ℂ) : (adMat ε k)ᴴ = adMat ε kᴴ := by
  ext x y
  simp only [Matrix.conjTranspose_apply, adMat]
  by_cases hx : IsPhys ε x <;> by_cases hy : IsPhys ε y
  · simp [hx, hy, star_mul', mul_comm]
  · have : y ≠ x := fun h => hy (h ▸ hx)
    simp [hx, hy, this]
  · have : x ≠ y := fun h => hx (h ▸ hy)
    simp [hx, hy, this, Ne.symm this]
  · simp only [hx, hy, if_false]
    by_cases h : y = x
    · subst h; simp
    · simp [h, Ne.symm h]

theorem kset_conjTranspose {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : kᴴ ∈ Kset ε := by
  refine ⟨?_, ?_⟩
  · have := hk.1
    rw [Matrix.mem_unitaryGroup_iff] at this ⊢
    rw [star_eq_conjTranspose, conjTranspose_conjTranspose]
    rw [star_eq_conjTranspose] at this
    exact mul_eq_one_comm.mp this
  · have hJ : (Jm ε)ᴴ = Jm ε := by
      simp only [Jm, Matrix.diagonal_conjTranspose]
      congr 1
      funext a
      by_cases h : ε a = true <;> simp [h]
    have := congrArg Matrix.conjTranspose hk.2
    rw [conjTranspose_mul, conjTranspose_mul, hJ] at this
    exact this.symm

theorem adMat_unitary {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : (adMat ε k)ᴴ * adMat ε k = 1 := by
  rw [adMat_conjTranspose, ← adMat_mul (kset_conjTranspose hk) hk]
  have : kᴴ * k = 1 := by
    have := hk.1
    rw [Matrix.mem_unitaryGroup_iff'] at this
    rwa [star_eq_conjTranspose] at this
  rw [this, adMat_one]

theorem dualV_eq_dot (w u : Fin n × Fin n → ℂ) : dualV w u = star w ⬝ᵥ u := by
  simp [dualV, dotProduct]

theorem dualV_adPhys {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (v : Fin n × Fin n → ℂ) :
    dualV v = dualV (adPhys ε k v) ∘ₗ adPhys ε k := by
  refine LinearMap.ext fun u => ?_
  rw [LinearMap.comp_apply, dualV_eq_dot, dualV_eq_dot]
  simp only [adPhys, Matrix.mulVecLin_apply]
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, adMat_unitary hk, Matrix.vecMul_one]

theorem ff_cmV {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (v : Fin n × Fin n → ℂ) :
    (ff ε k).toLinearMap * cmV v = cmV (adPhys ε k v) * (ff ε k).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  simp only [Module.End.mul_apply, cmV, AlgHom.toLinearMap_apply, ff]
  rw [dualV_adPhys hk v, map_contractLeft]

theorem ff_physFock (k : Matrix (Fin n) (Fin n) ℂ) {x : Fock n} (hx : x ∈ physFock ε) :
    ff ε k x ∈ physFock ε := by
  simp only [physFock, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  intro i a hia
  have hproj : (LinearMap.proj (R := ℂ) (φ := fun _ : Fin n × Fin n => ℂ) (i, a)) ∘ₗ adPhys ε k =
      LinearMap.proj (i, a) := by
    refine LinearMap.ext fun u => ?_
    have hp : ¬ IsPhys ε (i, a) := hia
    simp [adPhys, Matrix.mulVec, dotProduct, adMat, hp]
  have h := map_contractLeft (adPhys ε k) (LinearMap.proj (i, a)) x
  rw [hproj] at h
  simp only [cmFock, ff] at hx ⊢
  rw [← h, hx i a hia, map_zero]

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

theorem fockBasis_eq (S : Finset (Fin (n * n))) :
    fockBasis n S = ExteriorAlgebra.ιMulti ℂ S.card
      (fun i => Pi.single (finProdFinEquiv.symm (S.orderEmbOfFin rfl i)) (1 : ℂ)) := by
  have hb : fockBasis n S = ExteriorAlgebra.ιMulti ℂ S.card
      (((Pi.basisFun ℂ (Fin n × Fin n)).reindex finProdFinEquiv) ∘ S.orderEmbOfFin rfl) := by
    rw [fockBasis, ExteriorAlgebra.basis_apply]
    rfl
  have hv : ((Pi.basisFun ℂ (Fin n × Fin n)).reindex finProdFinEquiv) ∘ S.orderEmbOfFin rfl =
      fun i => Pi.single (finProdFinEquiv.symm (S.orderEmbOfFin rfl i)) (1 : ℂ) := by
    funext i
    simp
  rw [hb, hv]

theorem adPhys_single (k : Matrix (Fin n) (Fin n) ℂ) (y : Fin n × Fin n) :
    adPhys ε k (Pi.single y 1) = ∑ x, adMat ε k x y • Pi.single x (1 : ℂ) := by
  funext z
  simp [adPhys, Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]

theorem adPhys_diag_single (s : Fin n → ℂ) (x : Fin n × Fin n) :
    adPhys ε (Matrix.diagonal s) (Pi.single x 1) = modeChar ε s x • Pi.single x (1 : ℂ) := by
  funext y
  simp only [adPhys, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.smul_apply, smul_eq_mul]
  by_cases h : y = x
  · subst h
    by_cases hy : IsPhys ε y <;> simp [adMat, modeChar, hy]
  · simp only [h, if_false]
    obtain ⟨y1, y2⟩ := y
    obtain ⟨x1, x2⟩ := x
    simp only [adMat, Matrix.diagonal_apply]
    split_ifs <;> simp_all

theorem ff_diag (s : Fin n → ℂ) (S : Finset (Fin (n * n))) :
    ff ε (Matrix.diagonal s) (fockBasis n S) =
      (∏ m ∈ S, modeChar ε s (finProdFinEquiv.symm m)) • fockBasis n S := by
  rw [fockBasis_eq, ff, ExteriorAlgebra.map_apply_ιMulti]
  simp only [Function.comp_def, adPhys_diag_single]
  rw [AlternatingMap.map_smul_univ]
  congr 1
  conv_rhs => rw [← S.map_orderEmbOfFin_univ rfl]
  rw [Finset.prod_map]
  rfl

def adPoly (ε : Fin n → Bool) (x y : Fin n × Fin n) : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ :=
  if IsPhys ε x then
    (if IsPhys ε y then MvPolynomial.X (Sum.inl (x.1, y.1)) * MvPolynomial.X (Sum.inr (x.2, y.2)) else 0)
  else if x = y then 1 else 0

theorem eval_adPoly (k : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n × Fin n) :
    MvPolynomial.eval (Sum.elim (fun p => k p.1 p.2) (fun p => star (k p.1 p.2))) (adPoly ε x y) =
      adMat ε k x y := by
  unfold adPoly adMat
  split_ifs <;> simp

theorem ffMat_eq (k : Matrix (Fin n) (Fin n) ℂ) (S T : Finset (Fin (n * n))) :
    ffMat ε k S T = ∑ h : Fin T.card → Fin n × Fin n,
      (∏ i, adMat ε k (h i) (finProdFinEquiv.symm (T.orderEmbOfFin rfl i))) *
        (fockBasis n).repr (ExteriorAlgebra.ιMulti ℂ T.card (fun i => Pi.single (h i) (1 : ℂ))) S := by
  rw [ffMat, LinearMap.toMatrix_apply, AlgHom.toLinearMap_apply, fockBasis_eq, ff,
    ExteriorAlgebra.map_apply_ιMulti]
  simp only [Function.comp_def, adPhys_single]
  have h := (ExteriorAlgebra.ιMulti ℂ T.card).toMultilinearMap.map_sum
    (fun i x => adMat ε k x (finProdFinEquiv.symm (T.orderEmbOfFin rfl i)) • Pi.single x (1 : ℂ))
  simp only [AlternatingMap.coe_multilinearMap] at h
  rw [h, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [AlternatingMap.map_smul_univ, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem ffMat_poly (S T : Finset (Fin (n * n))) :
    ∃ P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ, ∀ k : Matrix (Fin n) (Fin n) ℂ,
      ffMat ε k S T = MvPolynomial.eval (Sum.elim (fun p => k p.1 p.2) (fun p => star (k p.1 p.2))) P := by
  refine ⟨∑ h : Fin T.card → Fin n × Fin n,
    (∏ i, adPoly ε (h i) (finProdFinEquiv.symm (T.orderEmbOfFin rfl i))) *
      MvPolynomial.C ((fockBasis n).repr (ExteriorAlgebra.ιMulti ℂ T.card (fun i => Pi.single (h i) (1 : ℂ))) S),
    fun k => ?_⟩
  rw [ffMat_eq, map_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_mul, map_prod, MvPolynomial.eval_C]
  simp only [eval_adPoly]

theorem ffMat_continuous (S T : Finset (Fin (n * n))) :
    Continuous fun k : Matrix (Fin n) (Fin n) ℂ => ffMat ε k S T := by
  obtain ⟨P, hP⟩ := ffMat_poly (ε := ε) S T
  simp only [hP]
  refine (MvPolynomial.continuous_eval P).comp ?_
  refine continuous_pi fun p => ?_
  rcases p with p | p
  · exact (continuous_apply p.2).comp (continuous_apply p.1)
  · exact continuous_star.comp ((continuous_apply p.2).comp (continuous_apply p.1))

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

theorem cpV_eq_sum (v : Fin n × Fin n → ℂ) : cpV v = ∑ x, v x • cpFock (n := n) x.1 x.2 := by
  refine LinearMap.ext fun y => ?_
  have hv : v = ∑ x, v x • Pi.single x (1 : ℂ) := by
    funext z
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [cpV, cpFock, LinearMap.sum_apply, Finset.sum_mul]

theorem cmV_eq_sum (v : Fin n × Fin n → ℂ) : cmV v = ∑ x, star (v x) • cmFock (n := n) x.1 x.2 := by
  rw [cmV, dualV, map_sum]
  simp only [map_smul]
  rfl

theorem toMatrix_cmV (v : Fin n × Fin n → ℂ) :
    LinearMap.toMatrix (fockBasis n) (fockBasis n) (cmV v) =
      (LinearMap.toMatrix (fockBasis n) (fockBasis n) (cpV v))ᴴ := by
  rw [cmV_eq_sum, cpV_eq_sum, map_sum, map_sum, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, map_smul, Matrix.conjTranspose_smul, lf_toMatrix_cm, lf_toMatrix_cp, fockMatrix_conjTranspose_eq_transpose]

theorem adPhys_kkH {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (w : Fin n × Fin n → ℂ) :
    adPhys ε k (adPhys ε kᴴ w) = w := by
  have hkk : k * kᴴ = 1 := by
    have := hk.1
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose] at this
    exact this
  rw [← LinearMap.comp_apply, ← adPhys_mul hk (kset_conjTranspose hk), hkk]
  simp [adPhys, adMat_one]

theorem ffMat_H_cp {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (w : Fin n × Fin n → ℂ) :
    LinearMap.toMatrix (fockBasis n) (fockBasis n) (cpV (adPhys ε kᴴ w)) * (ffMat ε k)ᴴ =
      (ffMat ε k)ᴴ * LinearMap.toMatrix (fockBasis n) (fockBasis n) (cpV w) := by
  have h := congrArg (LinearMap.toMatrix (fockBasis n) (fockBasis n)) (ff_cmV hk (adPhys ε kᴴ w))
  rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, adPhys_kkH hk, toMatrix_cmV, toMatrix_cmV] at h
  have h2 := congrArg Matrix.conjTranspose h
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_conjTranspose] at h2
  exact h2

theorem nH_cpV {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (w : Fin n × Fin n → ℂ) (z : Fock n) :
    Matrix.toLin (fockBasis n) (fockBasis n) (ffMat ε k)ᴴ (cpV w z) =
      cpV (adPhys ε kᴴ w) (Matrix.toLin (fockBasis n) (fockBasis n) (ffMat ε k)ᴴ z) := by
  have h := congrArg (Matrix.toLin (fockBasis n) (fockBasis n)) (ffMat_H_cp hk w)
  rw [Matrix.toLin_mul (v₁ := fockBasis n) (v₂ := fockBasis n) (v₃ := fockBasis n),
    Matrix.toLin_mul (v₁ := fockBasis n) (v₂ := fockBasis n) (v₃ := fockBasis n),
    Matrix.toLin_toMatrix, Matrix.toLin_toMatrix] at h
  have h3 := LinearMap.congr_fun h z
  simp only [LinearMap.comp_apply] at h3
  exact h3.symm

theorem algebraMapInv_ff (k : Matrix (Fin n) (Fin n) ℂ) (x : Fock n) :
    ExteriorAlgebra.algebraMapInv (ff ε k x) = ExteriorAlgebra.algebraMapInv x := by
  have : (ExteriorAlgebra.algebraMapInv (R := ℂ) (M := Fin n × Fin n → ℂ)).comp (ff ε k) =
      ExteriorAlgebra.algebraMapInv := by
    apply ExteriorAlgebra.hom_ext
    refine LinearMap.ext fun m => ?_
    simp [ff, ExteriorAlgebra.algebraMapInv]
  exact AlgHom.congr_fun this x

theorem ιMulti_card_zero (p : ℕ) (v : Fin p → (Fin n × Fin n → ℂ)) (hp : p = 0) :
    ExteriorAlgebra.ιMulti ℂ p v = 1 := by
  subst hp
  exact ExteriorAlgebra.ιMulti_zero_apply v

theorem algebraMapInv_ιMulti_pos (p : ℕ) (v : Fin p → (Fin n × Fin n → ℂ)) (hp : 0 < p) :
    ExteriorAlgebra.algebraMapInv (ExteriorAlgebra.ιMulti ℂ p v) = 0 := by
  cases p with
  | zero => omega
  | succ p =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, map_mul]
    simp [ExteriorAlgebra.algebraMapInv]

theorem repr_empty (x : Fock n) : (fockBasis n).repr x ∅ = ExteriorAlgebra.algebraMapInv x := by
  have : Finsupp.lapply ∅ ∘ₗ (fockBasis n).repr.toLinearMap =
      (ExteriorAlgebra.algebraMapInv (R := ℂ) (M := Fin n × Fin n → ℂ)).toLinearMap := by
    refine (fockBasis n).ext fun T => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply,
      AlgHom.toLinearMap_apply]
    rw [fockBasis_eq]
    rcases Nat.eq_zero_or_pos T.card with h | h
    · have hT : T = ∅ := Finset.card_eq_zero.mp h
      rw [ιMulti_card_zero _ _ h, map_one, hT, Finsupp.single_eq_same]
    · have hT : T ≠ ∅ := Finset.nonempty_iff_ne_empty.mp (Finset.card_pos.mp h)
      rw [algebraMapInv_ιMulti_pos _ _ h]
      simp [hT]
  exact LinearMap.congr_fun this x

theorem ffMat_empty_row (k : Matrix (Fin n) (Fin n) ℂ) (T : Finset (Fin (n * n))) :
    ffMat ε k ∅ T = if T = ∅ then 1 else 0 := by
  rw [ffMat, LinearMap.toMatrix_apply, AlgHom.toLinearMap_apply, repr_empty, algebraMapInv_ff, ← repr_empty,
    Module.Basis.repr_self, Finsupp.single_apply]

theorem nH_one (k : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.toLin (fockBasis n) (fockBasis n) (ffMat ε k)ᴴ 1 = 1 := by
  have h1 : (1 : Fock n) = fockBasis n ∅ := by
    rw [fockBasis_eq, ιMulti_card_zero _ _ Finset.card_empty]
  rw [h1, Matrix.toLin_self, Finset.sum_eq_single ∅]
  · simp [conjTranspose_apply, ffMat_empty_row]
  · intro T _ hT
    simp [conjTranspose_apply, ffMat_empty_row, hT]
  · simp

theorem nH_mul {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (x : Fock n) :
    ∀ y : Fock n, Matrix.toLin (fockBasis n) (fockBasis n) (ffMat ε k)ᴴ (x * y) =
      ff ε kᴴ x * Matrix.toLin (fockBasis n) (fockBasis n) (ffMat ε k)ᴴ y := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    intro y
    simp [Algebra.algebraMap_eq_smul_one]
  | add x x' hx hx' =>
    intro y
    rw [add_mul, map_add, hx, hx', map_add, add_mul]
  | ι_mul x m hx =>
    intro y
    have h := nH_cpV hk m (x * y)
    simp only [cpV, LinearMap.mulLeft_apply] at h
    rw [mul_assoc, h, hx, map_mul, ff, ExteriorAlgebra.map_apply_ι, mul_assoc]

theorem nH_eq {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    Matrix.toLin (fockBasis n) (fockBasis n) (ffMat ε k)ᴴ = (ff ε kᴴ).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  have h := nH_mul hk x 1
  rw [mul_one, nH_one, mul_one] at h
  exact h

theorem ffMat_unitary {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    ffMat ε k ∈ Matrix.unitaryGroup (Finset (Fin (n * n))) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
  have h1 : (ffMat ε k)ᴴ = LinearMap.toMatrix (fockBasis n) (fockBasis n) (ff ε kᴴ).toLinearMap := by
    rw [← nH_eq hk, LinearMap.toMatrix_toLin]
  have hkk : kᴴ * k = 1 := by
    have := hk.1
    rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose] at this
    exact this
  have h2 : (ff ε kᴴ).toLinearMap * (ff ε k).toLinearMap = 1 := by
    refine LinearMap.ext fun x => ?_
    rw [Module.End.mul_apply, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, ← AlgHom.comp_apply,
      ← ff_mul (kset_conjTranspose hk) hk, hkk, ff_one]
    rfl
  rw [h1, ffMat, ← LinearMap.toMatrix_mul, h2, LinearMap.toMatrix_one]

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end
