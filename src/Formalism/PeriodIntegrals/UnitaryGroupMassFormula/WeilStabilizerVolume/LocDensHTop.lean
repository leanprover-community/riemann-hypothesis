import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensHI
import ReciprocityTheory.ResidueCardinality.ArtinOntoB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensHF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensFF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.Shared.HermitianInverse
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensHL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensVDx
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensVol

section
noncomputable section

namespace PI.VolStabW

namespace IdxLW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsLocalRing

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem index_maxIdeal :
    (maximalIdeal (v.adicCompletionIntegers F)).toAddSubgroup.index = Nat.card (𝓞 F ⧸ v.asIdeal) := by
  rw [← ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue v]
  rfl

variable {E : Type} [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (a M : ℕ)

def crdL : latSub b v a M →+ (Fin a × Fin M × Fin d → v.adicCompletionIntegers F) where
  toFun x q := ⟨(Algebra.TensorProduct.basis (Fv F v) b).repr ((x : Fin a → Fin M → Fv F v ⊗[F] E)
    q.1 q.2.1) q.2.2, x.2 q.1 q.2.1 q.2.2⟩
  map_zero' := by
    funext q
    apply Subtype.ext
    simp
  map_add' x y := by
    funext q
    apply Subtype.ext
    simp

theorem crdL_surj : Function.Surjective (crdL v b a M) := by
  intro c
  let x : Fin a → Fin M → Fv F v ⊗[F] E := fun i j =>
    (Algebra.TensorProduct.basis (Fv F v) b).repr.symm
      (Finsupp.equivFunOnFinite.symm fun k => (c (i, j, k) : Fv F v))
  have hx : ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (x i j) k = c (i, j, k) := by
    intro i j k
    simp [x]
  refine ⟨⟨x, fun i j k => by rw [hx]; exact (c (i, j, k)).2⟩, ?_⟩
  funext q
  apply Subtype.ext
  exact hx q.1 q.2.1 q.2.2

theorem crd_smul' (s : Fv F v) (y : Fv F v ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (s • y) k =
      s * (Algebra.TensorProduct.basis (Fv F v) b).repr y k := by
  simp [map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem addSubgroupOf_eq :
    (lamF b v a M 0).addSubgroupOf (latSub b v a M) =
      (AddSubgroup.pi Set.univ fun _ : Fin a × Fin M × Fin d =>
        (maximalIdeal (v.adicCompletionIntegers F)).toAddSubgroup).comap (crdL v b a M) := by
  have hv := unifV_val v
  have h0 := (unifV_spec v).1
  ext x
  rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap, AddSubgroup.mem_pi]
  simp only [Set.mem_univ, true_implies, Submodule.mem_toAddSubgroup, ReciprocityTheory.Aut.mem_maxIdeal_iff]
  constructor
  · intro hx q
    simp only [lamF, mem_smulSub, zero_add, pow_one] at hx
    obtain ⟨p, hp, hpx⟩ := hx
    show Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr
      ((x : Fin a → Fin M → Fv F v ⊗[F] E) q.1 q.2.1) q.2.2) < 1
    rw [← hpx]
    simp only [Pi.smul_apply]
    rw [crd_smul', map_mul, hv]
    have hp' : Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr (p q.1 q.2.1) q.2.2) ≤ 1 := by
      have h := hp q.1 q.2.1 q.2.2
      rwa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at h
    calc WithZero.exp (-1 : ℤ) * Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr
          (p q.1 q.2.1) q.2.2) ≤ WithZero.exp (-1 : ℤ) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; decide
  · intro hx
    simp only [lamF, mem_smulSub, zero_add, pow_one]
    refine ⟨(unifV v)⁻¹ • (x : Fin a → Fin M → Fv F v ⊗[F] E), ?_, ?_⟩
    · intro i j k
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      simp only [Pi.smul_apply]
      rw [crd_smul', map_mul, map_inv₀, hv]
      have := ReciprocityTheory.Aut.val_le_exp_neg_one_of_lt_one v (hx (i, j, k))
      calc (WithZero.exp (-1 : ℤ))⁻¹ * Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr
            ((x : Fin a → Fin M → Fv F v ⊗[F] E) i j) k)
          ≤ (WithZero.exp (-1 : ℤ))⁻¹ * WithZero.exp (-1 : ℤ) := by gcongr; exact this
        _ = 1 := inv_mul_cancel₀ (WithZero.exp_ne_zero)
    · rw [smul_smul, mul_inv_cancel₀ h0, one_smul]

end IdxLW

open IdxLW

theorem idxL_holds : IdxL := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT _ d b v
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hd : d = 2 := by
    have := Module.finrank_eq_card_basis b
    rw [hCM.2.2.1, Fintype.card_fin] at this
    exact this.symm
  unfold AddSubgroup.relIndex
  rw [addSubgroupOf_eq, AddSubgroup.index_comap_of_surjective _ (crdL_surj v b a M),
    AddSubgroup.index_pi]
  simp only [index_maxIdeal, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin]
  subst hd
  ring_nf

end PI.VolStabW
end
end

section
noncomputable section

namespace PI.VolStabW

namespace FiniteFieldSplitting

open Matrix

variable {k : Type} [Field k] [Finite k]

def cols {M a : ℕ} (P : Matrix (Fin M) (Fin a) k) : Fin a → Fin M → k := fun j i ↦ P i j

theorem linInd_cols_iff {M a : ℕ} (P : Matrix (Fin M) (Fin a) k) :
    LinearIndependent k (cols P) ↔ ∀ v : Fin a → k, P *ᵥ v = 0 → v = 0 := by
  rw [Fintype.linearIndependent_iff]
  have h : ∀ v : Fin a → k, ∑ j, v j • cols P j = P *ᵥ v := by
    intro v
    ext i
    simp [cols, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  simp_rw [h]
  constructor
  · intro H v hv
    funext j
    exact H v hv j
  · intro H v hv j
    rw [H v hv]
    rfl

theorem exists_left_inv {M a : ℕ} (P : Matrix (Fin M) (Fin a) k)
    (hP : LinearIndependent k (cols P)) : ∃ L : Matrix (Fin a) (Fin M) k, L * P = 1 := by
  have hker : LinearMap.ker (Matrix.mulVecLin P) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    exact (linInd_cols_iff P).mp hP v (by simpa using hv)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have : LinearMap.toMatrix' (g ∘ₗ Matrix.mulVecLin P) = LinearMap.toMatrix' g * P := by
    rw [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  rw [← this, hg, LinearMap.toMatrix'_id]

theorem linInd_of_left_inv {M a : ℕ} (W : Matrix (Fin a) (Fin M) k) (P : Matrix (Fin M) (Fin a) k)
    (h : W * P = 1) : LinearIndependent k (cols P) := by
  refine (linInd_cols_iff P).mpr fun v hv ↦ ?_
  have : W *ᵥ (P *ᵥ v) = (W * P) *ᵥ v := Matrix.mulVec_mulVec _ _ _
  rw [h, Matrix.one_mulVec, hv, Matrix.mulVec_zero] at this
  exact this.symm

theorem card_left_inv {M a : ℕ} (P : Matrix (Fin M) (Fin a) k)
    (hP : LinearIndependent k (cols P)) :
    Nat.card {W : Matrix (Fin a) (Fin M) k // W * P = 1} = Nat.card k ^ (a * (M - a)) := by
  classical
  obtain ⟨L, hL⟩ := exists_left_inv P hP
  let f : Matrix (Fin a) (Fin M) k →ₗ[k] Matrix (Fin a) (Fin a) k :=
    { toFun := fun W ↦ W * P
      map_add' := fun x y ↦ Matrix.add_mul x y P
      map_smul' := fun c x ↦ Matrix.smul_mul c x P }
  have hf : ∀ W, f W = W * P := fun _ ↦ rfl
  have hsurj : Function.Surjective f := fun Z ↦ ⟨Z * L, by rw [hf, Matrix.mul_assoc, hL, Matrix.mul_one]⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_matrix,
    Module.finrank_matrix] at hrk
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at hrk
  have hker : Module.finrank k (LinearMap.ker f) = a * (M - a) := by
    rw [Nat.mul_sub]
    omega
  let e : {W : Matrix (Fin a) (Fin M) k // W * P = 1} ≃ LinearMap.ker f :=
    { toFun := fun W ↦ ⟨W.1 - L, by
        rw [LinearMap.mem_ker, hf, Matrix.sub_mul, W.2, hL, sub_self]⟩
      invFun := fun Z ↦ ⟨Z.1 + L, by
        have h0 := Z.2
        rw [LinearMap.mem_ker, hf] at h0
        rw [Matrix.add_mul, h0, hL, zero_add]⟩
      left_inv := fun W ↦ by
        apply Subtype.ext
        simp
      right_inv := fun Z ↦ by
        apply Subtype.ext
        simp }
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := k), hker]

theorem card_pairs {M a : ℕ} (ha : a ≤ M) :
    Nat.card {WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k // WP.1 * WP.2 = 1} =
      (∏ i : Fin a, (Nat.card k ^ M - Nat.card k ^ (i : ℕ))) * Nat.card k ^ (a * (M - a)) := by
  classical
  have : Fintype k := Fintype.ofFinite k
  let e : {WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k // WP.1 * WP.2 = 1} ≃
      Σ P : {P : Matrix (Fin M) (Fin a) k // LinearIndependent k (cols P)},
        {W : Matrix (Fin a) (Fin M) k // W * P.1 = 1} :=
    { toFun := fun x ↦ ⟨⟨x.1.2, linInd_of_left_inv x.1.1 x.1.2 x.2⟩, ⟨x.1.1, x.2⟩⟩
      invFun := fun y ↦ ⟨(y.2.1, y.1.1), y.2.2⟩
      left_inv := fun x ↦ rfl
      right_inv := fun y ↦ rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  simp_rw [fun P : {P : Matrix (Fin M) (Fin a) k // LinearIndependent k (cols P)} ↦
    card_left_inv P.1 P.2]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  congr 1
  let e2 : {P : Matrix (Fin M) (Fin a) k // LinearIndependent k (cols P)} ≃
      {s : Fin a → Fin M → k // LinearIndependent k s} :=
    { toFun := fun P ↦ ⟨cols P.1, P.2⟩
      invFun := fun s ↦ ⟨fun i j ↦ s.1 j i, s.2⟩
      left_inv := fun P ↦ rfl
      right_inv := fun s ↦ rfl }
  rw [← Nat.card_eq_fintype_card, Nat.card_congr e2, card_linearIndependent
    (by rw [Module.finrank_fin_fun]; exact ha), Module.finrank_fin_fun, Nat.card_eq_fintype_card]

end FiniteFieldSplitting

namespace FiniteFieldSplitting

open Matrix

variable {k : Type} [Field k] [Finite k] {M a : ℕ}

abbrev swapR (k : Type) [Field k] : k × k →+* k × k := (RingEquiv.prodComm (R := k) (S := k)).toRingHom

def U1 (X : Fin a → Fin M → k × k) : Matrix (Fin a) (Fin M) k := fun r i ↦ (X r i).1

def V1 (X : Fin a → Fin M → k × k) : Matrix (Fin a) (Fin M) k := fun r i ↦ (X r i).2

theorem ffH_fst (J : Matrix (Fin M) (Fin M) (k × k)) (x y : Fin M → k × k) :
    (ffH (swapR k) J x y).1 = ∑ i, ∑ j, (x i).2 * (J i j).1 * (y j).1 := by
  simp [ffH, Prod.fst_sum]

theorem ffH_snd (J : Matrix (Fin M) (Fin M) (k × k)) (x y : Fin M → k × k) :
    (ffH (swapR k) J x y).2 = ∑ i, ∑ j, (x i).1 * (J i j).2 * (y j).2 := by
  simp [ffH, Prod.snd_sum]

theorem gram_iff (J : Matrix (Fin M) (Fin M) (k × k)) (hJ : ∀ i j, (J j i).swap = J i j)
    (T : Matrix (Fin a) (Fin a) (k × k)) (hT : ∀ i j, (T j i).swap = T i j)
    (X : Fin a → Fin M → k × k) :
    ffGram (swapR k) J X = T ↔
      V1 X * J.map Prod.fst * (U1 X)ᵀ = T.map Prod.fst := by
  have key : ∀ r s, (ffGram (swapR k) J X r s).1 = (V1 X * J.map Prod.fst * (U1 X)ᵀ) r s := by
    intro r s
    simp only [ffGram, ffH_fst, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, U1,
      V1, Finset.sum_mul]
    exact Finset.sum_comm
  have key2 : ∀ r s, (ffGram (swapR k) J X r s).2 = (ffGram (swapR k) J X s r).1 := by
    intro r s
    simp only [ffGram, ffH_fst, ffH_snd]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    have h1 : (J j i).2 = (J i j).1 := by
      have := congrArg Prod.fst (hJ i j)
      simpa using this
    rw [h1]
    ring
  constructor
  · intro h
    ext r s
    rw [← key, h]
    rfl
  · intro h
    funext r s
    refine Prod.ext ?_ ?_
    · rw [key, h]
      rfl
    · rw [key2, key, h, Matrix.map_apply]
      have := congrArg Prod.fst (hT s r)
      simpa using this.symm

theorem fFSplit_nat (M a : ℕ) (ha : a ≤ M)
    (J : Matrix (Fin M) (Fin M) (k × k)) (hJ : ∀ i j, (J j i).swap = J i j) (hJd : IsUnit J.det)
    (T : Matrix (Fin a) (Fin a) (k × k)) (hT : ∀ i j, (T j i).swap = T i j) (hTd : IsUnit T.det) :
    Nat.card {X : Fin a → Fin M → k × k // ffGram (swapR k) J X = T} =
      (∏ i : Fin a, (Nat.card k ^ M - Nat.card k ^ (i : ℕ))) * Nat.card k ^ (a * (M - a)) := by
  classical
  set A := J.map Prod.fst with hA
  set T1 := T.map Prod.fst with hT1
  have hAd : IsUnit A.det := by
    have := hJd.map (RingHom.fst k k)
    rwa [RingHom.map_det] at this
  have hT1d : IsUnit T1.det := by
    have := hTd.map (RingHom.fst k k)
    rwa [RingHom.map_det] at this
  let e : (Fin a → Fin M → k × k) ≃ Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k :=
    { toFun := fun X ↦ (T1⁻¹ * V1 X, A * (U1 X)ᵀ)
      invFun := fun WP r i ↦ ((A⁻¹ * WP.2)ᵀ r i, (T1 * WP.1) r i)
      left_inv := fun X ↦ by
        funext r i
        simp only [Matrix.nonsing_inv_mul_cancel_left _ _ hAd,
          Matrix.mul_nonsing_inv_cancel_left _ _ hT1d, Matrix.transpose_transpose]
        rfl
      right_inv := fun WP ↦ by
        have h1 : V1 (fun r i ↦ ((A⁻¹ * WP.2)ᵀ r i, (T1 * WP.1) r i)) = T1 * WP.1 := rfl
        have h2 : U1 (fun r i ↦ ((A⁻¹ * WP.2)ᵀ r i, (T1 * WP.1) r i)) = (A⁻¹ * WP.2)ᵀ := rfl
        simp only [h1, h2, Matrix.transpose_transpose, Matrix.nonsing_inv_mul_cancel_left _ _ hT1d,
          Matrix.mul_nonsing_inv_cancel_left _ _ hAd] }
  have hcond : ∀ X, ffGram (swapR k) J X = T ↔ (e X).1 * (e X).2 = 1 := by
    intro X
    rw [gram_iff J hJ T hT X, ← hT1, ← hA]
    change V1 X * A * (U1 X)ᵀ = T1 ↔ T1⁻¹ * V1 X * (A * (U1 X)ᵀ) = 1
    have hre : T1⁻¹ * V1 X * (A * (U1 X)ᵀ) = T1⁻¹ * (V1 X * A * (U1 X)ᵀ) := by
      simp only [Matrix.mul_assoc]
    rw [hre]
    constructor
    · intro h
      rw [h, Matrix.nonsing_inv_mul _ hT1d]
    · intro h
      calc V1 X * A * (U1 X)ᵀ = T1 * (T1⁻¹ * (V1 X * A * (U1 X)ᵀ)) :=
            (Matrix.mul_nonsing_inv_cancel_left _ _ hT1d).symm
        _ = T1 := by rw [h, Matrix.mul_one]
  rw [Nat.card_congr (Equiv.subtypeEquiv (p := fun X ↦ ffGram (swapR k) J X = T)
    (q := fun WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k ↦ WP.1 * WP.2 = 1) e hcond),
    card_pairs ha]

end FiniteFieldSplitting

theorem fFSplit_holds : FFSplit := by
  intro k _ _ M a ha J hJ hJd T hT hTd
  rw [FiniteFieldSplitting.fFSplit_nat M a ha J hJ hJd T hT hTd]
  have hq : 0 < Nat.card k := Nat.card_pos
  push_cast
  congr 1
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Nat.cast_sub (Nat.pow_le_pow_right hq (by omega))]
  push_cast
  rfl

end PI.VolStabW
end
end

section
noncomputable section

namespace PI.VolStabW

namespace FiniteFieldCounting

theorem prod_bound {ι : Type} (δ : ι → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h : ∀ j, |δ j| ≤ t) (s : Finset ι) :
    |∏ j ∈ s, (1 + δ j) - 1| ≤ t * (2 ^ s.card - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.card_insert_of_notMem hj]
    set P := ∏ j ∈ s, (1 + δ j)
    have hP : |P| ≤ 1 + |P - 1| := by
      have := abs_sub_abs_le_abs_sub P 1
      rw [abs_one] at this
      linarith
    have e : (1 + δ j) * P - 1 = (P - 1) + δ j * P := by ring
    rw [e]
    have h1 := abs_add_le (P - 1) (δ j * P)
    rw [abs_mul] at h1
    have hpow : (2 : ℝ) ^ (s.card + 1) = 2 * 2 ^ s.card := by ring
    rw [hpow]
    have h2 : |δ j| * |P| ≤ t * (1 + |P - 1|) := mul_le_mul (h j) hP (abs_nonneg _) ht0
    have h3 : 0 ≤ |P - 1| := abs_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr ht1) h3]

theorem ratio_bound (M a : ℕ) (ha : a ≤ M) (q : ℝ) (hq : 1 ≤ q) (δ : Fin a → ℝ)
    (h : ∀ j, |δ j| ≤ (q⁻¹) ^ 2) : |∏ j, (1 + δ j) - 1| ≤ 2 ^ M * (q⁻¹) ^ 2 := by
  have ht0 : 0 ≤ (q⁻¹) ^ 2 := by positivity
  have ht1 : (q⁻¹) ^ 2 ≤ 1 := pow_le_one₀ (inv_nonneg.mpr (by linarith)) (inv_le_one_of_one_le₀ hq)
  have := prod_bound δ _ ht0 ht1 h Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at this
  have h2 : (2 : ℝ) ^ a ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) ha
  nlinarith

theorem inv_pow_le (q : ℝ) (hq : 1 ≤ q) (m : ℕ) (hm : 2 ≤ m) : (q⁻¹) ^ m ≤ (q⁻¹) ^ 2 :=
  pow_le_pow_of_le_one (inv_nonneg.mpr (by linarith)) (inv_le_one_of_one_le₀ hq) hm

theorem exp_id (M a : ℕ) (ha : a ≤ M) : M * a + a * (M - a) = 2 * M * a - a ^ 2 := by
  have h1 : a ^ 2 ≤ 2 * M * a := by nlinarith
  zify [h1, ha]
  ring

theorem sum_exp (M : ℕ) : ∀ a, a ≤ M →
    ∑ j ∈ Finset.range a, (2 * (M - j) - 1) = 2 * M * a - a ^ 2 := by
  intro a
  induction a with
  | zero => intro _; simp
  | succ a ih =>
    intro ha
    rw [Finset.sum_range_succ, ih (by omega)]
    have h1 : a ^ 2 ≤ 2 * M * a := by nlinarith
    have h2 : (a + 1) ^ 2 ≤ 2 * M * (a + 1) := by nlinarith
    have h3 : a ≤ M := by omega
    have h4 : 1 ≤ 2 * (M - a) := by omega
    zify [h1, h2, h3, h4]
    ring

theorem split_ratio (M a : ℕ) (ha : a ≤ M) (q : ℝ) (hq : q ≠ 0) :
    (∏ i : Fin a, (q ^ M - q ^ (i : ℕ))) * q ^ (a * (M - a)) / q ^ (2 * M * a - a ^ 2) =
      ∏ i : Fin a, (1 + -(q ^ (i : ℕ) / q ^ M)) := by
  have hM : q ^ M ≠ 0 := pow_ne_zero _ hq
  have e1 : ∀ i : Fin a, q ^ M - q ^ (i : ℕ) = q ^ M * (1 + -(q ^ (i : ℕ) / q ^ M)) := by
    intro i
    field_simp
    ring
  rw [Finset.prod_congr rfl fun i _ ↦ e1 i, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← pow_mul, ← exp_id M a ha, pow_add]
  have h1 : q ^ (M * a) ≠ 0 := pow_ne_zero _ hq
  have h2 : q ^ (a * (M - a)) ≠ 0 := pow_ne_zero _ hq
  field_simp

theorem inert_ratio (M a : ℕ) (ha : a ≤ M) (q : ℝ) (hq : q ≠ 0) :
    (∏ j : Fin a, (q ^ (2 * (M - j) - 1) - (-1) ^ (M - j) * q ^ (M - j - 1))) /
        q ^ (2 * M * a - a ^ 2) =
      ∏ j : Fin a, (1 + -((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))) := by
  have e1 : ∀ j : Fin a, q ^ (2 * (M - j) - 1) - (-1) ^ (M - j) * q ^ (M - j - 1) =
      q ^ (2 * (M - j) - 1) *
        (1 + -((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))) := by
    intro j
    have : q ^ (2 * (M - j) - 1) ≠ 0 := pow_ne_zero _ hq
    field_simp
    ring
  rw [Finset.prod_congr rfl fun j _ ↦ e1 j, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range (fun j ↦ 2 * (M - j) - 1) a, sum_exp M a ha]
  have h1 : q ^ (2 * M * a - a ^ 2) ≠ 0 := pow_ne_zero _ hq
  field_simp

theorem split_delta (M a : ℕ) (ha : a + 2 ≤ M) (q : ℝ) (hq : 1 ≤ q) (i : Fin a) :
    |-(q ^ (i : ℕ) / q ^ M)| ≤ (q⁻¹) ^ 2 := by
  have hq0 : q ≠ 0 := by positivity
  have hMi : q ^ M = q ^ (i : ℕ) * q ^ (M - i) := by
    rw [← pow_add]
    congr 1
    omega
  have hi : q ^ (i : ℕ) ≠ 0 := pow_ne_zero _ hq0
  have e : q ^ (i : ℕ) / q ^ M = (q⁻¹) ^ (M - i) := by
    rw [hMi, inv_pow]
    field_simp
  rw [abs_neg, e, abs_of_nonneg (by positivity)]
  exact inv_pow_le q hq _ (by omega)

theorem inert_delta (M a : ℕ) (ha : a + 2 ≤ M) (q : ℝ) (hq : 1 ≤ q) (j : Fin a) :
    |-((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))| ≤ (q⁻¹) ^ 2 := by
  have hq0 : q ≠ 0 := by positivity
  have hexp : q ^ (2 * (M - j) - 1) = q ^ (M - j - 1) * q ^ (M - j) := by
    rw [← pow_add]
    congr 1
    omega
  have hi : q ^ (M - j - 1) ≠ 0 := pow_ne_zero _ hq0
  have e : |-((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))| = (q⁻¹) ^ (M - j) := by
    rw [abs_neg, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, hexp,
      abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), inv_pow]
    field_simp
  rw [e]
  exact inv_pow_le q hq _ (by omega)

theorem swapR_apply (k : Type) [Field k] (y : k × k) : FiniteFieldSplitting.swapR k y = y.swap := rfl

theorem card_transport {k K : Type} [Field k] [CommRing K] [Algebra k K] (σ : K ≃ₐ[k] K)
    (e : K ≃ₐ[k] k × k) (he : ∀ x, e (σ x) = (e x).swap) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) K) (T : Matrix (Fin a) (Fin a) K) :
    Nat.card {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T} =
      Nat.card {Y : Fin a → Fin M → k × k //
        ffGram (FiniteFieldSplitting.swapR k) (J.map e) Y = T.map e} := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (p := fun X ↦ ffGram (σ : K →+* K) J X = T)
    (q := fun Y ↦ ffGram (FiniteFieldSplitting.swapR k) (J.map e) Y = T.map e)
    { toFun := fun X r i ↦ e (X r i)
      invFun := fun Y r i ↦ e.symm (Y r i)
      left_inv := fun X ↦ by
        funext r i
        simp
      right_inv := fun Y ↦ by
        funext r i
        simp } ?_
  intro X
  have key : ∀ r s, ffGram (FiniteFieldSplitting.swapR k) (J.map e) (fun r i ↦ e (X r i)) r s =
      e (ffGram (σ : K →+* K) J X r s) := by
    intro r s
    simp only [ffGram, ffH, map_sum, map_mul, Matrix.map_apply, swapR_apply, ← he]
    rfl
  constructor
  · intro h
    funext r s
    change ffGram (FiniteFieldSplitting.swapR k) (J.map e) (fun r i ↦ e (X r i)) r s = _
    rw [key, h]
    rfl
  · intro h
    funext r s
    apply e.injective
    rw [← key]
    exact congrFun (congrFun h r) s

end FiniteFieldCounting

theorem fFCount_of (hS : FFSplit) (hI : FFInert) : FFCount := by
  intro M
  refine ⟨2 ^ M, ?_⟩
  intro k K _ _ _ _ σ hσ h2 J hJ hJd a ha T hT hTd
  have hq1 : (1 : ℝ) ≤ (Nat.card k : ℝ) := by exact_mod_cast Nat.card_pos (α := k)
  have hq0 : (Nat.card k : ℝ) ≠ 0 := by positivity
  rcases hσ.2 with ⟨hK, hdeg, hne⟩ | ⟨e, he⟩
  · letI : Field K := hK.toField
    rw [hI k K σ hσ.1 hdeg hne h2 M a (by omega) J hJ hJd T hT hTd,
      FiniteFieldCounting.inert_ratio M a (by omega) _ hq0]
    exact FiniteFieldCounting.ratio_bound M a (by omega) _ hq1 _
      (FiniteFieldCounting.inert_delta M a ha _ hq1)
  · have hJ' : ∀ i j, ((J.map e) j i).swap = (J.map e) i j := by
      intro i j
      simp only [Matrix.map_apply, ← he, hJ]
    have hT' : ∀ i j, ((T.map e) j i).swap = (T.map e) i j := by
      intro i j
      simp only [Matrix.map_apply, ← he, hT]
    have hJd' : IsUnit (J.map e).det := by
      have hd : e J.det = (J.map e).det := (e : K →+* k × k).map_det J
      rw [← hd]
      exact hJd.map e
    have hTd' : IsUnit (T.map e).det := by
      have hd : e T.det = (T.map e).det := (e : K →+* k × k).map_det T
      rw [← hd]
      exact hTd.map e
    rw [FiniteFieldCounting.card_transport σ e he J T, hS k M a (by omega) _ hJ' hJd' _ hT' hTd',
      FiniteFieldCounting.split_ratio M a (by omega) _ hq0]
    exact FiniteFieldCounting.ratio_bound M a (by omega) _ hq1 _
      (FiniteFieldCounting.split_delta M a ha _ hq1)

theorem fFCount_of_inert (hI : FFInert) : FFCount := fFCount_of fFSplit_holds hI

end PI.VolStabW
end
end

section
noncomputable section

namespace PI.VolStabW.FFHS

open Module

variable {K : Type} [Field K] {σ : K →+* K}

structure IsSq {V : Type} [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V → V → K) :
    Prop where
  add_right : ∀ x y z, h x (y + z) = h x y + h x z
  smul_right : ∀ (c : K) x y, h x (c • y) = c * h x y
  herm : ∀ x y, h y x = σ (h x y)

structure IsHS {V : Type} [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V → V → K) : Prop
    extends IsSq σ h where
  nondeg : ∀ x, (∀ y, h x y = 0) → x = 0

section basic

variable {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K}

def IsSq.lin (hs : IsSq σ h) (x : V) : V →ₗ[K] K where
  toFun := h x
  map_add' := hs.add_right x
  map_smul' c y := by simp [hs.smul_right]

theorem IsSq.lin_apply (hs : IsSq σ h) (x y : V) : hs.lin x y = h x y := rfl

theorem IsSq.add_left (hs : IsSq σ h) (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [hs.herm z (x + y), hs.add_right, map_add, ← hs.herm z x, ← hs.herm z y]

theorem IsSq.smul_left (hs : IsSq σ h) (c : K) (x y : V) : h (c • x) y = σ c * h x y := by
  rw [hs.herm y (c • x), hs.smul_right, map_mul, ← hs.herm y x]

theorem IsSq.zero_right (hs : IsSq σ h) (x : V) : h x 0 = 0 := by
  simpa using hs.add_right x 0 0

theorem IsSq.zero_left (hs : IsSq σ h) (y : V) : h 0 y = 0 := by
  rw [hs.herm y 0, hs.zero_right, map_zero]

theorem IsSq.sub_right (hs : IsSq σ h) (x y z : V) : h x (y - z) = h x y - h x z :=
  (hs.lin x).map_sub y z

theorem IsSq.self_fixed (hs : IsSq σ h) (x : V) : σ (h x x) = h x x := (hs.herm x x).symm

theorem IsSq.ext_basis {h' : V → V → K} (hs : IsSq σ h) (hs' : IsSq σ h') {ι : Type}
    (b : Basis ι K V) (hb : ∀ i j, h (b i) (b j) = h' (b i) (b j)) (x y : V) : h x y = h' x y := by
  have step1 : ∀ i y, h (b i) y = h' (b i) y := fun i y => by
    have : hs.lin (b i) = hs'.lin (b i) := b.ext (fun j => hb i j)
    exact LinearMap.congr_fun this y
  have step2 : ∀ x, hs.lin x = hs'.lin x := fun x => b.ext (fun i => by
    simp only [IsSq.lin_apply]
    rw [hs.herm (b i) x, hs'.herm (b i) x, step1])
  exact LinearMap.congr_fun (step2 x) y

theorem exists_aniso (h2 : (2 : K) ≠ 0) (hs : IsHS σ h) (x : V) (hx : x ≠ 0) :
    ∃ e, h e e ≠ 0 := by
  have hq := hs.toIsSq
  by_contra H
  push_neg at H
  obtain ⟨y, hy⟩ : ∃ y, h x y ≠ 0 := by
    by_contra H'
    push_neg at H'
    exact hx (hs.nondeg x H')
  have key := H (x + (h x y)⁻¹ • y)
  simp only [hq.add_right, hq.add_left, hq.smul_right, hq.smul_left, H x, H y,
    hq.herm x y] at key
  have e1 : σ (h x y)⁻¹ * σ (h x y) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hy, map_one]
  have e2 : (h x y)⁻¹ * h x y = 1 := inv_mul_cancel₀ hy
  exact h2 (by linear_combination key - e1 - e2)

def perp (hs : IsSq σ h) (e : V) : Submodule K V := LinearMap.ker (hs.lin e)

theorem mem_perp (hs : IsSq σ h) (e w : V) : w ∈ perp hs e ↔ h e w = 0 := LinearMap.mem_ker

theorem perp_isHS (hs : IsHS σ h) (e : V) (he : h e e ≠ 0) :
    IsHS σ (fun w w' : perp hs.toIsSq e => h w w') where
  add_right x y z := hs.add_right x y z
  smul_right c x y := hs.smul_right c x y
  herm x y := hs.herm x y
  nondeg w hw := by
    have hq := hs.toIsSq
    apply Subtype.ext
    apply hs.nondeg
    intro y
    have hm : y - ((h e e)⁻¹ * h e y) • e ∈ perp hq e := by
      have : (h e e)⁻¹ * h e y * h e e = h e y := by
        rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ he, one_mul]
      rw [mem_perp, hq.sub_right, hq.smul_right, this, sub_self]
    have h1 := hw ⟨_, hm⟩
    have hwe : h w e = 0 := by rw [hq.herm e w, (mem_perp hq e w).1 w.2, map_zero]
    calc h w y = h w (((h e e)⁻¹ * h e y) • e + (y - ((h e e)⁻¹ * h e y) • e)) := by
          rw [add_sub_cancel]
      _ = ((h e e)⁻¹ * h e y) * h w e + h w (y - ((h e e)⁻¹ * h e y) • e) := by
          rw [hq.add_right, hq.smul_right]
      _ = 0 := by rw [hwe, h1]; ring

theorem finrank_perp [FiniteDimensional K V] (hs : IsSq σ h) (e : V) (he : h e e ≠ 0) :
    finrank K (perp hs e) + 1 = finrank K V := by
  have hsurj : Function.Surjective (hs.lin e) := fun c =>
    ⟨(c * (h e e)⁻¹) • e, by rw [IsSq.lin_apply, hs.smul_right, mul_assoc, inv_mul_cancel₀ he,
      mul_one]⟩
  have := LinearMap.finrank_range_add_finrank_ker (hs.lin e)
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, finrank_self] at this
  unfold perp
  omega

theorem linIndep_orth (hs : IsSq σ h) {n : ℕ} (f : Fin n → V)
    (h1 : ∀ i j, i ≠ j → h (f i) (f j) = 0) (h2 : ∀ i, h (f i) (f i) ≠ 0) :
    LinearIndependent K f := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have := congrArg (hs.lin (f i)) hg
  rw [map_sum, map_zero, Finset.sum_eq_single i] at this
  · rw [map_smul, IsSq.lin_apply, smul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_right (h2 i)
  · intro j _ hji
    rw [map_smul, IsSq.lin_apply, h1 i j (Ne.symm hji), smul_zero]
  · simp

theorem decomp_val (hs : IsSq σ h) (e w : V) (hw : h e w = 0) (s : K) :
    h (s • e + w) (s • e + w) = σ s * s * h e e + h w w := by
  simp only [hs.add_right, hs.add_left, hs.smul_right, hs.smul_left, hw, hs.herm e w, map_zero]
  ring

end basic

theorem exists_orth (h2 : (2 : K) ≠ 0) : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h : V → V → K), IsHS σ h → finrank K V = m →
    ∃ f : Fin m → V, (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧ ∀ i, h (f i) (f i) ≠ 0 := by
  intro m
  induction m with
  | zero => intro V _ _ _ h _ _; exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ m ih =>
    intro V _ _ _ h hs hm
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hm
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    obtain ⟨e, he⟩ := exists_aniso h2 hs x hx
    have hq := hs.toIsSq
    have hfr : finrank K (perp hq e) = m := by have := finrank_perp hq e he; omega
    obtain ⟨g, hg1, hg2⟩ := ih (perp hq e) (fun w w' => h w w') (perp_isHS hs e he) hfr
    refine ⟨Fin.cons e (fun i => (g i : V)), ?_, ?_⟩
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j => simpa using (mem_perp hq e (g j)).1 (g j).2
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [hq.herm e, (mem_perp hq e (g i)).1 (g i).2, map_zero]
        | succ j =>
          simp only [Fin.cons_succ]
          exact hg1 i j (fun hh => hij (by rw [hh]))
    · intro i
      induction i using Fin.cases with
      | zero => simpa using he
      | succ i => simpa using hg2 i

end PI.VolStabW.FFHS
end
end

section
noncomputable section

namespace PI.VolStabW.FFHS

open Module

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}

theorem perp_sub_mem {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K} (hs : IsSq σ h)
    (e x : V) (he : h e e ≠ 0) : x - ((h e e)⁻¹ * h e x) • e ∈ perp hs e := by
  have : (h e e)⁻¹ * h e x * h e e = h e x := by
    rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ he, one_mul]
  rw [mem_perp, hs.sub_right, hs.smul_right, this, sub_self]

theorem card_decomp {V : Type} [AddCommGroup V] [Module K V] [Finite V] {h : V → V → K}
    (hs : IsSq σ h) (e : V) (he : h e e ≠ 0) (c : K) :
    Nat.card {x : V // h x x = c} =
      ∑ t : K, Nat.card {w : perp hs e // h w w = c - σ t * t * h e e} := by
  let E1 : {x : V // h x x = c} ≃
      {p : K × perp hs e // h p.2 p.2 = c - σ p.1 * p.1 * h e e} :=
    { toFun := fun x => ⟨((h e e)⁻¹ * h e x.1, ⟨_, perp_sub_mem hs e x.1 he⟩), by
        have hw := (mem_perp hs e _).1 (perp_sub_mem hs e x.1 he)
        have := decomp_val hs e _ hw ((h e e)⁻¹ * h e x.1)
        rw [add_sub_cancel, x.2] at this
        simp only
        linear_combination -this⟩
      invFun := fun p => ⟨p.1.1 • e + p.1.2, by
        rw [decomp_val hs e _ ((mem_perp hs e _).1 p.1.2.2), p.2]; ring⟩
      left_inv := fun x => Subtype.ext (add_sub_cancel _ _)
      right_inv := by
        rintro ⟨⟨t, w⟩, hw⟩
        have hew : h e w = 0 := (mem_perp hs e w).1 w.2
        have ht : (h e e)⁻¹ * h e (t • e + (w : V)) = t := by
          rw [hs.add_right, hs.smul_right, hew, add_zero, mul_comm, mul_assoc,
            mul_inv_cancel₀ he, mul_one]
        apply Subtype.ext
        apply Prod.ext
        · exact ht
        · apply Subtype.ext
          show t • e + (w : V) - ((h e e)⁻¹ * h e (t • e + (w : V))) • e = w
          rw [ht, add_sub_cancel_left] }
  rw [Nat.card_congr (E1.trans (Equiv.subtypeProdEquivSigmaSubtype
    (fun t (w : perp hs e) => h w w = c - σ t * t * h e e))), Nat.card_sigma]

theorem card_norm (q : ℕ) (hq0 : 0 < q) (hK : Fintype.card K = q ^ 2) (hσ : ∀ x, σ (σ x) = x)
    (h2 : (2 : K) ≠ 0)
    (hN : ∀ d, σ d = d → Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else q + 1) :
    ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (h : V → V → K), IsHS σ h → finrank K V = m → ∀ c, σ c = c →
      (Nat.card {x : V // h x x = c} : ℝ) = (q : ℝ) ^ (2 * (m : ℤ) - 1) +
        (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) * ((if c = 0 then (q : ℝ) else 0) - 1) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
  intro m
  induction m with
  | zero =>
    intro V _ _ _ h hs hm c _
    have : Subsingleton V := Module.finrank_zero_iff.1 hm
    by_cases hc : c = 0
    · have h1 : Nat.card {x : V // h x x = c} = 1 := Nat.card_eq_one_iff_exists.2
        ⟨⟨0, by rw [hs.toIsSq.zero_left, hc]⟩, fun y => Subtype.ext (Subsingleton.elim _ _)⟩
      rw [h1, if_pos hc]
      simp only [Nat.cast_one, CharP.cast_eq_zero, mul_zero, zero_sub, pow_zero, one_mul]
      rw [zpow_neg_one, ← mul_one_add, add_sub_cancel, inv_mul_cancel₀ hq']
    · have : IsEmpty {x : V // h x x = c} := ⟨fun ⟨x, hx⟩ => hc (by
        rw [← hx, Subsingleton.elim x 0, hs.toIsSq.zero_left])⟩
      rw [Nat.card_of_isEmpty, if_neg hc]
      simp
  | succ m ih =>
    intro V _ _ _ h hs hm c hc
    have hq := hs.toIsSq
    have : Finite V := Module.finite_of_finite K
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hm
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    obtain ⟨e, he⟩ := exists_aniso h2 hs x hx
    have hfr : finrank K (perp hq e) = m := by have := finrank_perp hq e he; omega
    rw [card_decomp hq e he c, Nat.cast_sum]
    have hfix : ∀ t : K, σ (c - σ t * t * h e e) = c - σ t * t * h e e := fun t => by
      rw [map_sub, map_mul, map_mul, hσ, hc, hq.self_fixed]; ring
    rw [Finset.sum_congr rfl (fun t _ => ih (perp hq e) (fun w w' => h w w')
      (perp_isHS hs e he) hfr _ (hfix t))]
    have hcnt : ((Finset.univ.filter (fun t : K => c - σ t * t * h e e = 0)).card : ℝ) =
        if c = 0 then 1 else (q : ℝ) + 1 := by
      have e1 : (Finset.univ.filter (fun t : K => c - σ t * t * h e e = 0)).card =
          Nat.card {t : K // t * σ t = c * (h e e)⁻¹} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        congr 1
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [eq_mul_inv_iff_mul_eq₀ he]
        constructor <;> intro H <;> linear_combination -H
      have hf : σ (c * (h e e)⁻¹) = c * (h e e)⁻¹ := by
        rw [map_mul, map_inv₀, hc, hq.self_fixed]
      rw [e1, hN _ hf]
      by_cases hc0 : c = 0
      · simp [hc0]
      · have : c * (h e e)⁻¹ ≠ 0 := mul_ne_zero hc0 (inv_ne_zero he)
        simp [hc0, this]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hK, ← Finset.mul_sum,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hK, Finset.sum_ite,
      Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
      nsmul_eq_mul, hcnt]
    have e1 : (q : ℝ) ^ (2 * ((m + 1 : ℕ) : ℤ) - 1) = (q : ℝ) ^ (2 * (m : ℤ) - 1) * q ^ 2 := by
      rw [show 2 * ((m + 1 : ℕ) : ℤ) - 1 = (2 * m - 1) + 2 by push_cast; ring, zpow_add₀ hq']
      norm_cast
    have e2 : (q : ℝ) ^ (((m + 1 : ℕ) : ℤ) - 1) = (q : ℝ) ^ ((m : ℤ) - 1) * q := by
      rw [show ((m + 1 : ℕ) : ℤ) - 1 = ((m : ℤ) - 1) + 1 by push_cast; ring, zpow_add₀ hq',
        zpow_one]
    rw [e1, e2, pow_succ]
    by_cases hc0 : c = 0
    · simp only [hc0, if_true]; push_cast; ring
    · simp only [hc0, if_false]; push_cast; ring

theorem card_diag (q : ℕ) (hq0 : 0 < q) (hK : Fintype.card K = q ^ 2) (hσ : ∀ x, σ (σ x) = x)
    (h2 : (2 : K) ≠ 0)
    (hN : ∀ d, σ d = d → Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else q + 1) :
    ∀ (a m : ℕ), a ≤ m → ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (h : V → V → K), IsHS σ h → finrank K V = m → ∀ d : Fin a → K, (∀ i, σ (d i) = d i) →
      (∀ i, d i ≠ 0) →
      (Nat.card {Y : Fin a → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} : ℝ) =
        ∏ j : Fin a, ((q : ℝ) ^ (2 * (m - j) - 1) - (-1) ^ (m - j) * (q : ℝ) ^ (m - j - 1)) := by
  intro a
  induction a with
  | zero =>
    intro m _ V _ _ _ h _ _ d _ _
    have : Nat.card {Y : Fin 0 → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} = 1 :=
      Nat.card_eq_one_iff_exists.2 ⟨⟨Fin.elim0, fun i => i.elim0⟩,
        fun y => Subtype.ext (funext fun i => i.elim0)⟩
    rw [this]
    simp
  | succ a ih =>
    intro m ham V _ _ _ h hs hm d hd hd0
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hq := hs.toIsSq
    have : Finite V := Module.finite_of_finite K
    have : Fintype V := Fintype.ofFinite V
    classical
    let E : {Y : Fin (a + 1) → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} ≃
        Σ x : {x : V // h x x = d 0}, {Z : Fin a → perp hq x.1 //
          ∀ i j, h (Z i) (Z j) = if i = j then d i.succ else 0} :=
      { toFun := fun Y => ⟨⟨Y.1 0, by simpa using Y.2 0 0⟩,
          ⟨fun i => ⟨Y.1 i.succ, (mem_perp hq _ _).2 (by
            have := Y.2 0 i.succ; rwa [if_neg (Fin.succ_ne_zero i).symm] at this)⟩,
            fun i j => by
              have := Y.2 i.succ j.succ
              simpa only [Fin.succ_inj] using this⟩⟩
        invFun := fun p => ⟨Fin.cons p.1.1 (fun i => (p.2.1 i : V)), by
          intro i j
          induction i using Fin.cases with
          | zero =>
            induction j using Fin.cases with
            | zero => simpa using p.1.2
            | succ j =>
              simp only [Fin.cons_zero, Fin.cons_succ]
              rw [if_neg (Fin.succ_ne_zero j).symm]
              exact (mem_perp hq _ _).1 (p.2.1 j).2
          | succ i =>
            induction j using Fin.cases with
            | zero =>
              simp only [Fin.cons_zero, Fin.cons_succ]
              rw [if_neg (Fin.succ_ne_zero i), hq.herm, (mem_perp hq _ _).1 (p.2.1 i).2,
                map_zero]
            | succ j =>
              simp only [Fin.cons_succ, Fin.succ_inj]
              exact p.2.2 i j⟩
        left_inv := fun Y => Subtype.ext (funext fun i => by
          induction i using Fin.cases with
          | zero => rfl
          | succ i => rfl)
        right_inv := fun p => rfl }
    rw [Nat.card_congr E, Nat.card_sigma, Nat.cast_sum]
    have hfr : ∀ x : {x : V // h x x = d 0}, finrank K (perp hq x.1) = m' := fun x => by
      have := finrank_perp hq x.1 (by rw [x.2]; exact hd0 0); omega
    have hsum : ∀ x : {x : V // h x x = d 0}, (Nat.card {Z : Fin a → perp hq x.1 //
        ∀ i j, h (Z i) (Z j) = if i = j then d i.succ else 0} : ℝ) =
        ∏ j : Fin a, ((q : ℝ) ^ (2 * (m' - j) - 1) - (-1) ^ (m' - j) * (q : ℝ) ^ (m' - j - 1)) :=
      fun x => ih m' (by omega) (perp hq x.1) (fun w w' => h w w')
        (perp_isHS hs x.1 (by rw [x.2]; exact hd0 0)) (hfr x) (fun i => d i.succ)
        (fun i => hd i.succ) (fun i => hd0 i.succ)
    rw [Finset.sum_congr rfl (fun x _ => hsum x)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
      card_norm q hq0 hK hσ h2 hN (m' + 1) V h hs hm (d 0) (hd 0), if_neg (hd0 0),
      Fin.prod_univ_succ]
    congr 1
    · simp only [Fin.val_zero, Nat.sub_zero]
      rw [show 2 * ((m' + 1 : ℕ) : ℤ) - 1 = ((2 * (m' + 1) - 1 : ℕ) : ℤ) by omega,
        show ((m' + 1 : ℕ) : ℤ) - 1 = ((m' + 1 - 1 : ℕ) : ℤ) by omega, zpow_natCast,
        zpow_natCast]
      ring
    · refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [Fin.val_succ, show m' + 1 - (j + 1 : ℕ) = m' - j by omega]

end PI.VolStabW.FFHS
end
end

section
noncomputable section

namespace PI.VolStabW.FFHS

open Module Polynomial

section matrix

variable {K : Type} [Field K] {σ : K →+* K}

theorem ffH_isHS (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)
    (hJ : ∀ i j, σ (J j i) = J i j) (hdet : IsUnit J.det) : IsHS σ (ffH σ J) where
  add_right x y z := by
    simp only [ffH, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  smul_right c x y := by
    simp only [ffH, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  herm x y := by
    simp only [ffH, map_sum, map_mul, hσ, hJ]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  nondeg x hx := by
    have hv : Matrix.vecMul (fun i => σ (x i)) J = 0 := by
      funext j0
      have := hx (Pi.single j0 1)
      simpa [ffH, Pi.single_apply, Matrix.vecMul, dotProduct] using this
    have hinv : (fun i => σ (x i)) = 0 := by
      have := congrArg (fun v => Matrix.vecMul v J⁻¹) hv
      simpa only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv J hdet, Matrix.vecMul_one,
        Matrix.zero_vecMul] using this
    funext i
    exact σ.injective (by simpa using congrFun hinv i)

theorem ffH_single {n : ℕ} (T : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    ffH σ T (Pi.single i 1) (Pi.single j 1) = T i j := by
  simp [ffH, Pi.single_apply, apply_ite σ]

end matrix

theorem card_isom {K : Type} [Field K] {σ : K →+* K} {U V : Type} [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] {hU : U → U → K} {hV : V → V → K} (hsU : IsSq σ hU)
    (hsV : IsSq σ hV) {ι : Type} (b : Basis ι K U) :
    Nat.card {φ : U →ₗ[K] V // ∀ x y, hV (φ x) (φ y) = hU x y} =
      Nat.card {Y : ι → V // ∀ i j, hV (Y i) (Y j) = hU (b i) (b j)} :=
  Nat.card_congr (Equiv.subtypeEquiv (b.constr K).symm.toEquiv (fun φ => by
    simp only [LinearEquiv.coe_toEquiv, Basis.constr_symm_apply]
    constructor
    · intro H i j; exact H _ _
    · intro H x y
      have hs2 : IsSq σ (fun x y => hV (φ x) (φ y)) :=
        ⟨fun x y z => by simp only [map_add, hsV.add_right],
          fun c x y => by simp only [map_smul, hsV.smul_right],
          fun x y => hsV.herm _ _⟩
      exact (hs2.ext_basis hsU b H x y)))

section field

variable {k K : Type} [Field k] [Fintype k] [Field K] [Fintype K] [DecidableEq K] [Algebra k K]

theorem frob_of_ne (σ : K ≃ₐ[k] K) (h2 : finrank k K = 2) (hne : σ ≠ AlgEquiv.refl) :
    ∀ x, σ x = x ^ Fintype.card k := by
  obtain ⟨⟨n, hn'⟩, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k K).2 σ
  simp only at hn
  have : n = 0 ∨ n = 1 := by omega
  rcases this with rfl | rfl
  · exact absurd (by rw [← hn, pow_zero]; rfl) hne
  · intro x
    rw [← hn, pow_one]
    rfl

theorem mem_range_of_pow (d : K) (hd : d ^ Fintype.card k = d) :
    ∃ d0 : k, algebraMap k K d0 = d := by
  classical
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  by_contra H
  push_neg at H
  have hdm : d ∉ Finset.univ.image (algebraMap k K) := by simpa using H
  have := card_le_degree_of_subset_roots (p := (X ^ Fintype.card k - X : K[X]))
    (Z := insert d (Finset.univ.image (algebraMap k K))) (fun x hx => by
      rw [mem_roots (FiniteField.X_pow_card_sub_X_ne_zero K hq), IsRoot, eval_sub, eval_pow,
        eval_X, sub_eq_zero]
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hd
      · obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hx
        rw [← map_pow, FiniteField.pow_card])
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq K hq, Finset.card_insert_of_notMem hdm,
    Finset.card_image_of_injective _ (algebraMap k K).injective, Finset.card_univ] at this
  omega

theorem card_norm_fiber (σ : K ≃ₐ[k] K) (hfrob : ∀ x, σ x = x ^ Fintype.card k)
    (h2 : finrank k K = 2) (d : K) (hd : σ d = d) :
    Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else Fintype.card k + 1 := by
  classical
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  obtain ⟨r, hr⟩ : ∃ r, Fintype.card k = r + 1 := ⟨Fintype.card k - 1, by omega⟩
  have hr0 : 0 < r := by omega
  have hK : Fintype.card K = Fintype.card k ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := k), h2]
  have hnorm : ∀ t : K, t * σ t = algebraMap k K (Algebra.norm k t) := by
    intro t
    rw [FiniteField.algebraMap_norm_eq_pow, hfrob, ← pow_succ', Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, hK, hr, Nat.add_sub_cancel,
      Nat.sub_eq_of_eq_add (show (r + 1) ^ 2 = (r + 2) * r + 1 by ring),
      Nat.mul_div_cancel _ hr0]
  by_cases hd0 : d = 0
  · rw [if_pos hd0]
    subst hd0
    exact Nat.card_eq_one_iff_exists.2 ⟨⟨0, by simp⟩, fun y => Subtype.ext (by
      rcases mul_eq_zero.1 y.2 with h | h
      · exact h
      · exact (map_eq_zero_iff σ σ.injective).1 h)⟩
  rw [if_neg hd0]
  have hfix : d ^ Fintype.card k = d := by rw [← hfrob, hd]
  obtain ⟨d0, hd0e⟩ := mem_range_of_pow d hfix
  have hd00 : d0 ≠ 0 := by rintro rfl; exact hd0 (by rw [← hd0e, map_zero])
  let f : Kˣ →* kˣ := Units.map (Algebra.norm k (S := K) : K →* k)
  have hsurj : Function.Surjective f := FiniteField.unitsMap_norm_surjective k K
  have hall : ∀ y : kˣ, (Finset.univ.filter (fun g => f g = y)).card =
      (Finset.univ.filter (fun g => f g = 1)).card := fun y =>
    MonoidHom.card_fiber_eq_of_mem_range f (hsurj y) (hsurj 1)
  have htot := Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ)
    (t := Finset.univ) (fun x _ => Finset.mem_coe.2 (Finset.mem_univ _))
  rw [Finset.sum_congr rfl (fun y _ => hall y), Finset.sum_const, Finset.card_univ,
    Finset.card_univ, smul_eq_mul, Fintype.card_units, Fintype.card_units, hK, hr,
    Nat.add_sub_cancel, Nat.sub_eq_of_eq_add (show (r + 1) ^ 2 = (r + 2) * r + 1 by ring),
    mul_comm] at htot
  have hF : (Finset.univ.filter (fun g => f g = 1)).card = r + 2 :=
    (Nat.eq_of_mul_eq_mul_left hr0 htot).symm
  let E : {t : K // t * σ t = d} ≃ {g : Kˣ // f g = Units.mk0 d0 hd00} :=
    { toFun := fun t => ⟨Units.mk0 t.1 (fun h0 => hd0 (by rw [← t.2, h0, zero_mul])),
        Units.ext (by
          simp only [f, Units.coe_map, Units.val_mk0, MonoidHom.coe_coe]
          apply (algebraMap k K).injective
          rw [← hnorm, t.2, hd0e])⟩
      invFun := fun g => ⟨g.1.1, by
        have := congrArg Units.val g.2
        simp only [f, Units.coe_map, Units.val_mk0, MonoidHom.coe_coe] at this
        rw [hnorm, this, hd0e]⟩
      left_inv := fun t => rfl
      right_inv := fun g => Subtype.ext (Units.ext rfl) }
  rw [Nat.card_congr E, Nat.card_eq_fintype_card, Fintype.card_subtype, hall, hF, hr]

end field

theorem fFInert_holds : FFInert := by
  intro k K _ _ _ _ σ hσ h2 hne h2k M a haM J hJ hdJ T hT hdT
  classical
  have := Fintype.ofFinite k
  have : Module.Finite k K := Module.finite_of_finrank_pos (by omega)
  have : Finite K := Module.finite_of_finite k
  have := Fintype.ofFinite K
  have hq1 : 1 < Fintype.card k := Fintype.one_lt_card
  have hK : Fintype.card K = Fintype.card k ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := k), h2]
  have hfrob := frob_of_ne σ h2 hne
  have hσ' : ∀ x, (σ : K →+* K) ((σ : K →+* K) x) = x := fun x => hσ x
  have hN : ∀ d : K, (σ : K →+* K) d = d →
      Nat.card {t : K // t * (σ : K →+* K) t = d} = if d = 0 then 1 else Fintype.card k + 1 :=
    fun d hd => card_norm_fiber σ hfrob h2 d hd
  have h2K : (2 : K) ≠ 0 := by
    intro h
    exact h2k ((algebraMap k K).injective (by rw [map_ofNat, map_zero]; exact h))
  have hJs := ffH_isHS hσ' J hJ hdJ
  have hTs := ffH_isHS hσ' T hT hdT
  obtain ⟨f, hf1, hf2⟩ := exists_orth h2K a (Fin a → K) (ffH (σ : K →+* K) T) hTs
    (Module.finrank_fin_fun K)
  let b := basisOfLinearIndependentOfCardEqFinrank' f (linIndep_orth hTs.toIsSq f hf1 hf2)
    (by simp)
  have e1 : Nat.card {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T} =
      Nat.card {Y : Fin a → Fin M → K // ∀ i j, ffH (σ : K →+* K) J (Y i) (Y j) =
        ffH (σ : K →+* K) T (Pi.basisFun K (Fin a) i) (Pi.basisFun K (Fin a) j)} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight (fun X => ?_))
    rw [← Matrix.ext_iff]
    simp only [ffGram, Pi.basisFun_apply, ffH_single]
  have e3 : Nat.card {Y : Fin a → Fin M → K // ∀ i j, ffH (σ : K →+* K) J (Y i) (Y j) =
        ffH (σ : K →+* K) T (b i) (b j)} =
      Nat.card {Y : Fin a → Fin M → K // ∀ i j, ffH (σ : K →+* K) J (Y i) (Y j) =
        if i = j then ffH (σ : K →+* K) T (f i) (f i) else 0} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight (fun Y => ?_))
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank']
    refine forall_congr' (fun i => forall_congr' (fun j => ?_))
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij, hf1 i j hij]
  rw [e1, ← card_isom hTs.toIsSq hJs.toIsSq (Pi.basisFun K (Fin a)),
    card_isom hTs.toIsSq hJs.toIsSq b, e3,
    card_diag (Fintype.card k) (by omega) hK hσ' h2K hN a M haM (Fin M → K) _ hJs
      (Module.finrank_fin_fun K) _ (fun i => hTs.toIsSq.self_fixed (f i)) hf2,
    Nat.card_eq_fintype_card (α := k)]

end PI.VolStabW.FFHS
end
end

section
namespace PI.VolStabW

theorem fFCount_holds : FFCount := fFCount_of_inert FFHS.fFInert_holds

end PI.VolStabW
end

section
noncomputable section

namespace PI.VolStabW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  Matrix

section Mat

variable {A : Type} [CommRing A] (s : A →+* A)

theorem hform_mul_right {M a : ℕ} (Jm : Matrix (Fin M) (Fin M) A) (Y : Fin a → Fin M → A)
    (C : Matrix (Fin a) (Fin a) A) (i j : Fin a) :
    Formalism.UG.hform s Jm (Y i) (fun l => ∑ k, C j k * Y k l) =
      ∑ k, Formalism.UG.hform s Jm (Y i) (Y k) * C j k := by
  calc Formalism.UG.hform s Jm (Y i) (fun l => ∑ k, C j k * Y k l)
      = ∑ p, ∑ q, ∑ k, s (Y i p) * Jm p q * (C j k * Y k q) := by
        simp only [Formalism.UG.hform, Finset.mul_sum]
    _ = ∑ p, ∑ k, ∑ q, s (Y i p) * Jm p q * (C j k * Y k q) :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ k, ∑ p, ∑ q, s (Y i p) * Jm p q * (C j k * Y k q) := Finset.sum_comm
    _ = ∑ k, Formalism.UG.hform s Jm (Y i) (Y k) * C j k := by
        simp only [Formalism.UG.hform, Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun p _ =>
          Finset.sum_congr rfl fun q _ => by ring

theorem hform_mul_left {M a : ℕ} (Jm : Matrix (Fin M) (Fin M) A) (Y : Fin a → Fin M → A)
    (C : Matrix (Fin a) (Fin a) A) (i j : Fin a) :
    Formalism.UG.hform s Jm (fun l => ∑ k, C i k * Y k l) (Y j) =
      ∑ k, s (C i k) * Formalism.UG.hform s Jm (Y k) (Y j) := by
  calc Formalism.UG.hform s Jm (fun l => ∑ k, C i k * Y k l) (Y j)
      = ∑ p, ∑ q, ∑ k, s (C i k) * s (Y k p) * Jm p q * Y j q := by
        simp only [Formalism.UG.hform, map_sum, map_mul, Finset.sum_mul]
    _ = ∑ p, ∑ k, ∑ q, s (C i k) * s (Y k p) * Jm p q * Y j q :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ k, ∑ p, ∑ q, s (C i k) * s (Y k p) * Jm p q * Y j q := Finset.sum_comm
    _ = ∑ k, s (C i k) * Formalism.UG.hform s Jm (Y k) (Y j) := by
        simp only [Formalism.UG.hform, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun p _ =>
          Finset.sum_congr rfl fun q _ => by ring

theorem pol_solve {a : ℕ} (h πA : A) (hh : h + h = 1) (hsh : s h = h)
    (Γ Tm Tinv Sm E0 : Matrix (Fin a) (Fin a) A) (hΓ : Γ = Tm + πA • E0)
    (hTT : Tm * Tinv = 1) (hTs : (Tinv.map s)ᵀ * Tm = 1) (hS : ∀ i k, s (Sm k i) = Sm i k) :
    Γ * ((h • (Tinv * Sm))ᵀ)ᵀ + ((h • (Tinv * Sm))ᵀ).map s * Γ =
      Sm + πA • (h • (E0 * Tinv * Sm + Sm * (Tinv.map s)ᵀ * E0)) := by
  set Ts := (Tinv.map s)ᵀ with hTsdef
  have hC1 : ((h • (Tinv * Sm))ᵀ)ᵀ = h • (Tinv * Sm) := transpose_transpose _
  have hC2 : ((h • (Tinv * Sm))ᵀ).map s = h • (Sm * Ts) := by
    ext i j
    simp only [hTsdef, Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.mul_apply,
      smul_eq_mul, map_mul, map_sum, hsh, hS]
    congr 1
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  calc Γ * ((h • (Tinv * Sm))ᵀ)ᵀ + ((h • (Tinv * Sm))ᵀ).map s * Γ
      = (Tm + πA • E0) * (h • (Tinv * Sm)) + h • (Sm * Ts) * (Tm + πA • E0) := by
        rw [hC1, hC2, hΓ]
    _ = h • ((Tm * Tinv) * Sm) + (πA * h) • (E0 * Tinv * Sm) +
          (h • (Sm * (Ts * Tm)) + (h * πA) • (Sm * Ts * E0)) := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.mul_assoc, smul_smul]
        try module
    _ = (h + h) • Sm + πA • (h • (E0 * Tinv * Sm + Sm * Ts * E0)) := by
        rw [hTT, hTs, Matrix.one_mul, Matrix.mul_one]
        module
    _ = _ := by rw [hh, one_smul]

end Mat

section Int

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))

def intA (z : Fv F v ⊗[F] E) : Prop :=
  ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr z k ∈ v.adicCompletionIntegers F

variable {b v}

theorem intA_zero : intA b v 0 := fun k => by simp [zero_mem]

theorem intA_add {z w : Fv F v ⊗[F] E} (hz : intA b v z) (hw : intA b v w) : intA b v (z + w) :=
  fun k => by rw [map_add, Finsupp.add_apply]; exact add_mem (hz k) (hw k)

theorem intA_sum {ι : Type} (t : Finset ι) (f : ι → Fv F v ⊗[F] E) (hf : ∀ i ∈ t, intA b v (f i)) :
    intA b v (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using intA_zero
  | insert x t hx ih =>
    rw [Finset.sum_insert hx]
    exact intA_add (hf x (Finset.mem_insert_self x t))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem intA_smul {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) {z : Fv F v ⊗[F] E}
    (hz : intA b v z) : intA b v (c • z) :=
  fun k => by rw [map_smul, Finsupp.smul_apply, smul_eq_mul]; exact mul_mem hc (hz k)

theorem intA_incl (e : E) (h : ∀ m, algebraMap F (Fv F v) (b.repr e m) ∈ v.adicCompletionIntegers F) :
    intA b v (inclR (Fv F v) e) := fun m => by
  have := PositiveNearLattice.crd_incl b (Fv F v) e m
  simp only [PositiveNearLattice.crd] at this
  rw [this]
  exact h m

theorem incl_eq_tmul (e : E) : inclR (Fv F v) e = (1 : Fv F v) ⊗ₜ[F] e := rfl

theorem intA_mul (hg : ∀ k l m, algebraMap F (Fv F v) (b.repr (b k * b l) m) ∈
      v.adicCompletionIntegers F)
    {z w : Fv F v ⊗[F] E} (hz : intA b v z) (hw : intA b v w) : intA b v (z * w) := by
  rw [PositiveNearLattice.eq_sum_crd b (Fv F v) z, PositiveNearLattice.eq_sum_crd b (Fv F v) w, Finset.sum_mul_sum]
  refine intA_sum _ _ fun i _ => intA_sum _ _ fun j _ => ?_
  rw [smul_mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← incl_eq_tmul]
  exact intA_smul (mul_mem (hz i) (hw j)) (intA_incl _ (hg i j))

theorem sigR_incl (σ : E →ₐ[F] E) (e : E) :
    sigR (Fv F v) σ (inclR (Fv F v) e) = inclR (Fv F v) (σ e) := by
  simp [sigR, inclR, Algebra.TensorProduct.map_tmul]

theorem sigR_smul (σ : E →ₐ[F] E) (c : Fv F v) (z : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (c • z) = c • sigR (Fv F v) σ z := by
  rw [Algebra.smul_def, map_mul, sigR_algebraMap, ← Algebra.smul_def]

theorem intA_sig (σ : E →ₐ[F] E)
    (hg : ∀ k m, algebraMap F (Fv F v) (b.repr (σ (b k)) m) ∈ v.adicCompletionIntegers F)
    {z : Fv F v ⊗[F] E} (hz : intA b v z) : intA b v (sigR (Fv F v) σ z) := by
  rw [PositiveNearLattice.eq_sum_crd b (Fv F v) z, map_sum]
  refine intA_sum _ _ fun i _ => ?_
  rw [sigR_smul, ← incl_eq_tmul, sigR_incl]
  exact intA_smul (hz i) (intA_incl _ (hg i))

theorem aaInt (x : F) : ∀ᶠ v in cofinite,
    algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F := by
  have h := HeightOneSpectrum.Support.finite (𝓞 F) x
  refine Filter.eventually_cofinite.2 (h.subset fun v hv => ?_)
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hv
  rw [not_le] at hv
  show 1 < v.valuation F x
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact hv

def GoodV (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (Tinv : Matrix (Fin a) (Fin a) E) : Prop :=
  (∀ k l m, algebraMap F (Fv F v) (b.repr (b k * b l) m) ∈ v.adicCompletionIntegers F) ∧
  (∀ k m, algebraMap F (Fv F v) (b.repr (σ (b k)) m) ∈ v.adicCompletionIntegers F) ∧
  (∀ i j m, algebraMap F (Fv F v) (b.repr (J i j) m) ∈ v.adicCompletionIntegers F) ∧
  (∀ m, algebraMap F (Fv F v) (b.repr (1 / 2 : E) m) ∈ v.adicCompletionIntegers F) ∧
  (∀ i j m, algebraMap F (Fv F v) (b.repr (Tinv i j) m) ∈ v.adicCompletionIntegers F)

theorem goodV_aa (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (Tinv : Matrix (Fin a) (Fin a) E) :
    ∀ᶠ v in cofinite, GoodV b v σ J Tinv := by
  have k1 : ∀ᶠ v in cofinite, ∀ k l m : Fin d,
      algebraMap F (Fv F v) (b.repr (b k * b l) m) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun l =>
      Filter.eventually_all.2 fun m => aaInt _
  have k2 : ∀ᶠ v in cofinite, ∀ k m : Fin d,
      algebraMap F (Fv F v) (b.repr (σ (b k)) m) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun m => aaInt _
  have k3 : ∀ᶠ v in cofinite, ∀ (i j : Fin M) (m : Fin d),
      algebraMap F (Fv F v) (b.repr (J i j) m) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      Filter.eventually_all.2 fun m => aaInt _
  have k4 : ∀ᶠ v in cofinite, ∀ m : Fin d,
      algebraMap F (Fv F v) (b.repr (1 / 2 : E) m) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun m => aaInt _
  have k5 : ∀ᶠ v in cofinite, ∀ (i j : Fin a) (m : Fin d),
      algebraMap F (Fv F v) (b.repr (Tinv i j) m) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      Filter.eventually_all.2 fun m => aaInt _
  filter_upwards [k1, k2, k3, k4, k5] with v h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

end Int

theorem map_smulSub' {K V X : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup X]
    [Module K X] (D : V →+ X) (hDs : ∀ (t : K) w, D (t • w) = t • D w) (t : K)
    (L : AddSubgroup V) : (smulSub t L).map D = smulSub t (L.map D) := by
  ext z
  rw [AddSubgroup.mem_map, mem_smulSub]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨l, hl, rfl⟩ := (mem_smulSub _ _ _).1 hw
    exact ⟨D l, AddSubgroup.mem_map_of_mem _ hl, (hDs t l).symm⟩
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨l, hl, rfl⟩ := AddSubgroup.mem_map.1 hq
    exact ⟨t • l, (mem_smulSub _ _ _).2 ⟨l, hl, rfl⟩, hDs t l⟩

theorem hensAA_holds : HensAA := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a ha1 ha2 X0 hT hdet d b
  have : FiniteDimensional F E := Module.Finite.of_basis b
  have hσ := sigma_invol σ hCM.2.2.2
  set TE := gramE σ J X0 with hTE
  have hu : IsUnit TE.det := isUnit_iff_ne_zero.2 hdet
  filter_upwards [goodV_aa b σ J TE⁻¹] with v hg
  obtain ⟨g1, g2, g3, g4, g5⟩ := hg
  intro y hy hyT
  have := locallyCompact_Fv F v
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  have : T2Space (Fv F v ⊗[F] E) := by
    obtain ⟨ι, _, ⟨h⟩⟩ := PI.AdicCompletionValuation.exists_homeomorph_tens (F := F) (E := E) (Fv F v)
    exact h.isEmbedding.t2Space
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  obtain ⟨hπ0, hπ, hπO⟩ := unifV_spec v
  set π := unifV v with hπdef
  set s := sigR (Fv F v) σ with hsdef
  set L := latSub b v a M with hLdef
  have hLc : IsCompact (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) :=
    PositiveNearLattice.isCompact_latV b v a M
  have hπL : ∀ w ∈ L, π • w ∈ L := fun w hw => LatFactsW.smul_mem_latSub b v hπO hw
  have hyL : ∀ i l, intA b v (y i l) := fun i l => hy i l

  let D : (Fin a → Fin M → Fv F v ⊗[F] E) →+ HermR (Fv F v) σ a :=
    { toFun := fun W => ⟨gramB (Fv F v) σ J y W, gramB_mem (Fv F v) σ hσ J hJ.1 y W⟩
      map_zero' := by
        apply Subtype.ext
        funext i j
        simp [gramB, hR, Formalism.UG.hform]
      map_add' := fun W W' => Subtype.ext (gramB_add_right (Fv F v) σ J y W W') }
  have hDv : ∀ W, (D W : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = gramB (Fv F v) σ J y W :=
    fun _ => rfl
  have hDc : Continuous D :=
    ((continuous_gramB (Fv F v) σ J).comp (Continuous.prodMk continuous_const continuous_id)).subtype_mk _
  have hDs : ∀ (t : Fv F v) W, D (t • W) = t • D W := by
    intro t W
    apply Subtype.ext
    funext i j
    show gramB (Fv F v) σ J y (t • W) i j = t • gramB (Fv F v) σ J y W i j
    simp only [gramB, Pi.smul_apply, hR_smul_left, hR_smul_right, smul_add]

  have hJi : ∀ i j, intA b v (JR (Fv F v) J i j) := fun i j => intA_incl _ (g3 i j)
  have hmul : ∀ {z w : Fv F v ⊗[F] E}, intA b v z → intA b v w → intA b v (z * w) :=
    fun hz hw => intA_mul g1 hz hw
  have hsig : ∀ {z : Fv F v ⊗[F] E}, intA b v z → intA b v (s z) := fun hz => intA_sig σ g2 hz
  have hRi : ∀ x z : Fin M → Fv F v ⊗[F] E, (∀ l, intA b v (x l)) → (∀ l, intA b v (z l)) →
      intA b v (hR (Fv F v) σ J x z) := by
    intro x z hx hz
    have e : hR (Fv F v) σ J x z = ∑ i, ∑ j, s (x i) * JR (Fv F v) J i j * z j := rfl
    rw [e]
    exact intA_sum _ _ fun i _ => intA_sum _ _ fun j _ =>
      hmul (hmul (hsig (hx i)) (hJi i j)) (hz j)
  have hgB : ∀ u w, u ∈ L → w ∈ L →
      (⟨gramB (Fv F v) σ J u w, gramB_mem (Fv F v) σ hσ J hJ.1 u w⟩ : HermR (Fv F v) σ a) ∈
        hermO b v σ a := by
    intro u w hu' hw' i j
    exact intA_add (hRi _ _ (hu' i) (hw' j)) (hRi _ _ (hw' i) (hu' j))
  have hgR : ∀ w, w ∈ L → gramH (Fv F v) σ hσ J hJ.1 w ∈ hermO b v σ a := by
    intro w hw' i j
    exact hRi _ _ (hw' i) (hw' j)
  have hOsm : ∀ {c : Fv F v}, c ∈ v.adicCompletionIntegers F → ∀ S ∈ hermO b v σ a,
      c • S ∈ hermO b v σ a := by
    intro c hc S hS i j
    exact intA_smul hc (hS i j)

  set Tm : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := TE.map (inclR (Fv F v)) with hTm
  set Ti : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := TE⁻¹.map (inclR (Fv F v)) with hTi
  have hTT : Tm * Ti = 1 := by
    rw [hTm, hTi, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _)
      (map_one _)]
  have hTh : (TE.map (σ : E →+* E))ᵀ = TE := by
    ext i j
    exact hT i j
  have hE1 : (TE⁻¹.map (σ : E →+* E))ᵀ * TE = 1 :=
    Formalism.MassFormulaShared.inverseAdjoint_mul (σ : E →+* E) TE hTh hu
  have hTs : (Ti.map s)ᵀ * Tm = 1 := by
    have e : (Ti.map s)ᵀ = ((TE⁻¹.map (σ : E →+* E))ᵀ).map (inclR (Fv F v)) := by
      ext i j
      simp [hTi, hsdef, sigR_incl]
    rw [e, hTm, ← Matrix.map_mul, hE1, Matrix.map_one _ (map_zero _) (map_one _)]
  have hTii : ∀ i j, intA b v (Ti i j) := fun i j => intA_incl _ (g5 i j)

  set h : Fv F v ⊗[F] E := inclR (Fv F v) (1 / 2 : E) with hhdef
  have hh : h + h = 1 := by rw [hhdef, ← map_add, add_halves, map_one]
  have hsh : s h = h := by
    rw [hsdef, hhdef, sigR_incl]
    congr 1
    rw [map_div₀, map_one, map_ofNat]
  have hhi : intA b v h := intA_incl _ g4

  have hyT' : gramH (Fv F v) σ hσ J hJ.1 y - hermOf (Fv F v) σ TE hT ∈ smulSub π (hermO b v σ a) := by
    have := hyT
    simp only [hF, zero_add, pow_one] at this
    exact this
  obtain ⟨E0h, hE0, hE0eq⟩ := (mem_smulSub _ _ _).1 hyT'
  set πA : Fv F v ⊗[F] E := algebraMap (Fv F v) (Fv F v ⊗[F] E) π with hπA
  have hΓ : gramR (Fv F v) σ J y = Tm + πA • (E0h : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) := by
    have e := congrArg Subtype.val hE0eq
    have e2 : π • (E0h : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = gramR (Fv F v) σ J y - Tm := e
    rw [hπA, algebraMap_smul, e2]
    abel

  have hbase : ∀ S ∈ hermO b v σ a, ∃ l ∈ L, S - D l ∈ smulSub π (hermO b v σ a) := by
    intro S hS
    set Sm : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := S.1 with hSm
    have hSh : ∀ i k, s (Sm k i) = Sm i k := fun i k => S.2 i k
    set C : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := (h • (Ti * Sm))ᵀ with hC
    set W : Fin a → Fin M → Fv F v ⊗[F] E := fun j l => ∑ k, C j k * y k l with hW
    have hCi : ∀ j k, intA b v (C j k) := by
      intro j k
      simp only [hC, Matrix.transpose_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
      exact hmul hhi (intA_sum _ _ fun m _ => hmul (hTii k m) (hS m j))
    have hWL : W ∈ L := fun j l => intA_sum _ _ fun k _ => hmul (hCi j k) (hyL k l)
    have hgW : gramB (Fv F v) σ J y W = gramR (Fv F v) σ J y * Cᵀ + C.map s * gramR (Fv F v) σ J y := by
      ext i j
      simp only [gramB, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
      rw [show hR (Fv F v) σ J (y i) (W j) = ∑ k, hR (Fv F v) σ J (y i) (y k) * C j k from
          hform_mul_right s (JR (Fv F v) J) y C i j,
        show hR (Fv F v) σ J (W i) (y j) = ∑ k, s (C i k) * hR (Fv F v) σ J (y k) (y j) from
          hform_mul_left s (JR (Fv F v) J) y C i j]
      rfl
    have hsol := pol_solve s h πA hh hsh (gramR (Fv F v) σ J y) Tm Ti Sm E0h hΓ hTT hTs hSh
    set R : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) :=
      h • ((E0h : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) * Ti * Sm + Sm * (Ti.map s)ᵀ * E0h)
      with hRdef
    have hRi' : ∀ i j, intA b v (R i j) := by
      intro i j
      simp only [hRdef, Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.map_apply, smul_eq_mul]
      refine hmul hhi (intA_add (intA_sum _ _ fun k _ => hmul (intA_sum _ _ fun m _ =>
        hmul (hE0 i m) (hTii m k)) (hS k j)) (intA_sum _ _ fun k _ => hmul (intA_sum _ _ fun m _ =>
        hmul (hS i m) (hsig (hTii k m))) (hE0 k j)))
    have hsol' : gramR (Fv F v) σ J y * Cᵀ + C.map s * gramR (Fv F v) σ J y = Sm + πA • R := hsol
    have hDW : (D W : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = Sm + π • R := by
      rw [hDv, hgW, hsol', hπA, algebraMap_smul]
    set Rh : HermR (Fv F v) σ a := π⁻¹ • (D W - S) with hRh
    have hRhv : (Rh : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = R := by
      show π⁻¹ • ((D W : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) - Sm) = R
      rw [hDW, add_sub_cancel_left, inv_smul_smul₀ hπ0]
    have hRhO : Rh ∈ hermO b v σ a := by
      intro i j
      show intA b v ((Rh : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j)
      rw [hRhv]
      exact hRi' i j
    refine ⟨W, hWL, (mem_smulSub _ _ _).2 ⟨-Rh, (hermO b v σ a).neg_mem hRhO, ?_⟩⟩
    rw [hRh, smul_neg, smul_inv_smul₀ hπ0, neg_sub]
  have hreach := reach_of_approx π hπ L hLc hπL D hDc hDs (hermO b v σ a)
    (LatFactsW.isCompact_hermO b v σ a) hbase
  have hDL : L.map D = hermO b v σ a := by
    refine le_antisymm ?_ fun p hp => ?_
    · rintro _ ⟨W, hW, rfl⟩
      exact hgB y W hy hW
    · obtain ⟨l, hl, e⟩ := hreach p hp
      exact AddSubgroup.mem_map.2 ⟨l, hl, e⟩
  refine ⟨D, fun n => ?_, fun n Z hZ W hW => ?_⟩
  · rw [lamF, hF, map_smulSub' D hDs, hDL]
  · obtain ⟨z, hz, rfl⟩ := (mem_smulSub _ _ _).1 hZ
    obtain ⟨w, hw, rfl⟩ := (mem_smulSub _ _ _).1 hW
    rw [hF, mem_smulSub]
    have hB : (⟨gramB (Fv F v) σ J z w, gramB_mem (Fv F v) σ hσ J hJ.1 z w⟩ :
        HermR (Fv F v) σ a) ∈ hermO b v σ a := hgB z w hz hw
    have hG : π ^ n • gramH (Fv F v) σ hσ J hJ.1 w ∈ hermO b v σ a :=
      hOsm (pow_mem hπO n) _ (hgR w hw)
    refine ⟨_, (hermO b v σ a).add_mem hB hG, ?_⟩
    apply Subtype.ext
    show π ^ (n + 1 + 1) • (gramB (Fv F v) σ J z w + π ^ n • gramR (Fv F v) σ J w) =
      gramR (Fv F v) σ J (y + unifV v ^ (0 + 1) • z + unifV v ^ (n + 1) • w) -
        gramR (Fv F v) σ J (y + unifV v ^ (0 + 1) • z) - gramB (Fv F v) σ J y (unifV v ^ (n + 1) • w)
    have e2 : gramR (Fv F v) σ J (y + unifV v ^ (0 + 1) • z + unifV v ^ (n + 1) • w) -
        gramR (Fv F v) σ J (y + unifV v ^ (0 + 1) • z) - gramB (Fv F v) σ J y (unifV v ^ (n + 1) • w) =
        gramB (Fv F v) σ J (unifV v ^ (0 + 1) • z) (unifV v ^ (n + 1) • w) +
          gramR (Fv F v) σ J (unifV v ^ (n + 1) • w) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, gramB, gramR, Pi.add_apply, hR_add_left,
        hR_add_right]
      ring
    have gBs : ∀ (t t' : Fv F v) (u u' : Fin a → Fin M → Fv F v ⊗[F] E),
        gramB (Fv F v) σ J (t • u) (t' • u') = (t * t') • gramB (Fv F v) σ J u u' := by
      intro t t' u u'
      ext i j
      simp only [gramB, Pi.smul_apply, hR_smul_left, hR_smul_right, Matrix.smul_apply]
      module
    have gRs : ∀ (t : Fv F v) (u : Fin a → Fin M → Fv F v ⊗[F] E),
        gramR (Fv F v) σ J (t • u) = (t * t) • gramR (Fv F v) σ J u := by
      intro t u
      ext i j
      simp only [gramR, Pi.smul_apply, hR_smul_left, hR_smul_right, Matrix.smul_apply]
      module
    rw [e2, gBs, gRs, ← hπdef]
    module

end PI.VolStabW
end
end

section
namespace PI.VolStabW

theorem densAA_of_open (hV : VolAA) (hH : HensAA) (hI : IdxH) (hC : CntAA) : DensAA :=
  densAA_of fibLat_holds fFCount_holds
    (resAA_of hV latFacts_holds hH (idxAA_of idxL_holds hI) hC)

end PI.VolStabW
end
