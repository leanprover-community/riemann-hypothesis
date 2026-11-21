import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerDecompositionFockNoncompactParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockAdjoints
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
import BuildAid.ForwardExisting
import ReciprocityTheory.SemistableReduction.AlgebraicIndependentOfDerivations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFirstActionMatrixUnitEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerPairingAdjointMixedLowerStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.DetDer

section
noncomputable section
namespace GlobalTheory.FockAdj
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

variable {σ : Type} [DecidableEq σ] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : MvPolynomial σ ℂ →ₗ[ℂ] H}

theorem inner_monomial_left (hι : IsFockIP ι) (α : σ →₀ ℕ) (Q : MvPolynomial σ ℂ) :
    inner ℂ (ι (monomial α 1)) (ι Q) =
      coeff α Q * α.prod (fun _ k => (k.factorial : ℂ)) := by
  induction Q using MvPolynomial.induction_on' with
  | add Q Q' h h' => simp only [map_add, inner_add_right, h, h', coeff_add, add_mul]
  | monomial β b =>
    have hm : (monomial β b : MvPolynomial σ ℂ) = b • monomial β 1 := by
      rw [smul_monomial]; simp
    rw [coeff_monomial]
    conv_lhs => rw [hm]
    rw [map_smul, inner_smul_right, hι]
    by_cases h : α = β
    · subst h; simp
    · simp [h, Ne.symm h]

theorem inner_eq_zero_of_isHomogeneous (hι : IsFockIP ι) {d e : ℕ} {P Q : MvPolynomial σ ℂ}
    (hde : d ≠ e) (hP : P.IsHomogeneous d) (hQ : Q.IsHomogeneous e) :
    inner ℂ (ι P) (ι Q) = 0 := by
  rw [P.as_sum, map_sum, sum_inner]
  refine Finset.sum_eq_zero fun α hα => ?_
  have hm : (monomial α (coeff α P) : MvPolynomial σ ℂ) = coeff α P • monomial α 1 := by
    rw [smul_monomial]; simp
  have h0 : coeff α Q = 0 := by
    by_contra hc
    exact hde ((hP (mem_support_iff.mp hα)).symm.trans (hQ hc))
  rw [hm, map_smul, inner_smul_left, inner_monomial_left hι, h0, zero_mul, mul_zero]

theorem injective_of_isFockIP (hι : IsFockIP ι) : Function.Injective ι := by
  rw [injective_iff_map_eq_zero]
  intro P hP
  ext α
  have h := inner_monomial_left hι α P
  rw [hP, inner_zero_right] at h
  have hne : α.prod (fun _ k => (k.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  simpa [hne] using h.symm


end GlobalTheory.FockAdj
end
end

section
section
noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair GlobalTheory.FockAlg

namespace GlobalTheory.FockProj

variable {σ : Type} [DecidableEq σ] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : MvPolynomial σ ℂ →ₗ[ℂ] H}

theorem inner_homog_eq (hι : IsFockIP ι) {n : ℕ} {h : MvPolynomial σ ℂ} (hh : h.IsHomogeneous n)
    (g : MvPolynomial σ ℂ) :
    inner ℂ (ι h) (ι g) = inner ℂ (ι h) (ι (homogeneousComponent n g)) := by
  conv_lhs => rw [← sum_homogeneousComponent g]
  rw [map_sum, inner_sum]
  by_cases hn : n ∈ Finset.range (g.totalDegree + 1)
  · rw [Finset.sum_eq_single_of_mem n hn]
    intro m _ hmn
    exact GlobalTheory.FockAdj.inner_eq_zero_of_isHomogeneous hι (Ne.symm hmn) hh
      (homogeneousComponent_isHomogeneous m g)
  · have hlt : g.totalDegree < n := by simp at hn; omega
    rw [homogeneousComponent_eq_zero n g hlt, map_zero, inner_zero_right]
    refine Finset.sum_eq_zero fun m hm => ?_
    have : m ≠ n := by simp at hm; omega
    exact GlobalTheory.FockAdj.inner_eq_zero_of_isHomogeneous hι (Ne.symm this) hh
      (homogeneousComponent_isHomogeneous m g)

theorem isCompl_orth [Finite σ] (hι : IsFockIP ι) (hinj : Function.Injective ι)
    (W : Submodule ℂ (MvPolynomial σ ℂ)) (hW : ∀ f ∈ W, ∀ n, homogeneousComponent n f ∈ W) :
    IsCompl W ((W.map ι)ᗮ.comap ι) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hxC
    have h0 : inner ℂ (ι x) (ι x) = 0 :=
      (Submodule.mem_orthogonal _ _).1 (Submodule.mem_comap.1 hxC) (ι x) (Submodule.mem_map_of_mem hx)
    rw [inner_self_eq_zero] at h0
    exact hinj (by rw [h0, map_zero])
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro f
    rw [← sum_homogeneousComponent f]
    refine Submodule.sum_mem _ fun n _ => ?_
    set h := homogeneousComponent n f
    have hh : h.IsHomogeneous n := homogeneousComponent_isHomogeneous n f
    let Wn : Submodule ℂ (MvPolynomial σ ℂ) := W ⊓ homogeneousSubmodule σ ℂ n
    haveI : FiniteDimensional ℂ (homogeneousSubmodule σ ℂ n) :=
      Module.Finite.iff_fg.2 (homogeneousSubmodule_fg σ ℂ n)
    haveI : FiniteDimensional ℂ Wn := Submodule.finiteDimensional_of_le inf_le_right
    let K : Submodule ℂ H := Wn.map ι
    haveI : FiniteDimensional ℂ K := inferInstance
    obtain ⟨w, hwWn, hwk⟩ := Submodule.mem_map.1 (K.starProjection_apply_mem (ι h))
    have hwn : w.IsHomogeneous n := (mem_homogeneousSubmodule n w).1 hwWn.2
    refine Submodule.mem_sup.2 ⟨w, hwWn.1, h - w, ?_, add_sub_cancel _ _⟩
    rw [Submodule.mem_comap, Submodule.mem_orthogonal]
    rintro v ⟨w', hw', rfl⟩
    rw [inner_eq_zero_symm, inner_homog_eq hι (hh.sub hwn), map_sub, hwk]
    refine Submodule.starProjection_inner_eq_zero (K := K) _ _ ?_
    exact Submodule.mem_map_of_mem ⟨hW w' hw' n, homogeneousComponent_mem n w'⟩

theorem exists_equivariant_proj : ∀ (p q r s : ℕ) (W : Submodule ℂ (Pol p q r s)),
    (∀ Z, ∀ f ∈ W, fockAct1 p q r s Z f ∈ W) → (∀ f ∈ W, ∀ n, homogeneousComponent n f ∈ W) →
    ∃ π : Pol p q r s →ₗ[ℂ] Pol p q r s, (∀ f, π f ∈ W) ∧ (∀ f ∈ W, π f = f) ∧
      ∀ Z f, π (fockAct1 p q r s Z f) = fockAct1 p q r s Z (π f) := by
  intro p q r s W hst hgr
  obtain ⟨ι, hι, hinj⟩ := GlobalTheory.FischerParts.exists_fockIP (Ln p q r s)
  set C : Submodule ℂ (Pol p q r s) := (W.map ι)ᗮ.comap ι with hCdef
  have hc : IsCompl W C := isCompl_orth hι hinj W hgr
  have hCst : ∀ Z, ∀ u ∈ C, fockAct1 p q r s Z u ∈ C := by
    intro Z u hu
    rw [hCdef, Submodule.mem_comap, Submodule.mem_orthogonal] at hu ⊢
    rintro v ⟨w, hw, rfl⟩
    rw [inner_eq_zero_symm,
      (GlobalTheory.FockAdj.fock_adjoints p q r s _ ι hι).2.1 Z u w, inner_eq_zero_symm]
    exact hu _ (Submodule.mem_map_of_mem (hst _ w hw))
  let π : Pol p q r s →ₗ[ℂ] Pol p q r s := W.subtype ∘ₗ W.linearProjOfIsCompl C hc
  have hmem : ∀ f, π f ∈ W := fun f => (W.linearProjOfIsCompl C hc f).2
  have hπW : ∀ f ∈ W, π f = f := fun f hf =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨f, hf⟩)
  have hπC : ∀ u ∈ C, π u = 0 := fun u hu => by
    have h0 := (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc).2 hu
    exact (congrArg Subtype.val h0).trans rfl
  have hsub : ∀ f, f - π f ∈ C := fun f => by
    have key : W.linearProjOfIsCompl C hc (π f) = W.linearProjOfIsCompl C hc f :=
      Submodule.linearProjOfIsCompl_apply_left hc (W.linearProjOfIsCompl C hc f)
    have h1 := (W.linearProjOfIsCompl C hc).map_sub f (π f)
    rw [key, sub_self] at h1
    exact (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc).1 h1
  refine ⟨π, hmem, hπW, fun Z f => ?_⟩
  have hf : f = π f + (f - π f) := (add_sub_cancel _ _).symm
  conv_lhs => rw [hf]
  rw [map_add, map_add, hπW _ (hst Z _ (hmem f)), hπC _ (hCst Z _ (hsub f)), add_zero]

end GlobalTheory.FockProj
end
end

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_invariant_subspace_equivariant_projection : ∀ (p q r s : ℕ) (W : Submodule ℂ (Pol p q r s)), (∀ Z, ∀ f ∈ W, fockAct1 p q r s Z f ∈ W) → (∀ f ∈ W, ∀ n, homogeneousComponent n f ∈ W) → ∃ π : Pol p q r s →ₗ[ℂ] Pol p q r s, (∀ f, π f ∈ W) ∧ (∀ f ∈ W, π f = f) ∧ ∀ Z f, π (fockAct1 p q r s Z f) = fockAct1 p q r s Z (π f) := by
  atlas_forward_decl GlobalTheory.FockProj.exists_equivariant_proj
end

section
section
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair.GradR

theorem mR_isHomogeneous (P Q R : ℕ) (a : Fin P) (b : Fin Q) : (mR P Q R a b).IsHomogeneous 2 := by
  unfold mR
  exact IsHomogeneous.sum _ _ _ fun c _ => (isHomogeneous_X ℂ _).mul (isHomogeneous_X ℂ _)

theorem detR_isHomogeneous (P Q R : ℕ) (h : P ≤ R) : (detR P Q R h).IsHomogeneous P := by
  unfold detR
  rw [Matrix.det_apply']
  refine IsHomogeneous.sum _ _ _ fun σ _ => ?_
  have h1 : (∏ i : Fin P, (Matrix.of fun a c : Fin P =>
      (X (Sum.inl a, Sum.inl (Fin.castLE h c)) : Pol P Q R 0)) (σ i) i).IsHomogeneous (∑ _i : Fin P, 1) :=
    IsHomogeneous.prod _ _ _ fun i _ => isHomogeneous_X ℂ _
  have h0 : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : Pol P Q R 0).IsHomogeneous 0 := by
    have := isHomogeneous_C (Ix P Q × Ix R 0) (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)
    rwa [map_intCast] at this
  simpa using h0.mul h1

theorem embR_isHomogeneous (P Q R : ℕ) (h : P ≤ R) (k : ℕ) {G : Mdl P Q} {m : ℕ} (hG : G.IsHomogeneous m) :
    (embR P Q R h k G).IsHomogeneous (2 * m + P * k) :=
  (hG.aeval _ fun ab => mR_isHomogeneous P Q R ab.1 ab.2).mul ((detR_isHomogeneous P Q R h).pow k)

theorem homogeneousComponent_embR_mem (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (G : Mdl P Q) (n : ℕ) :
    homogeneousComponent n (embR P Q R h k G) ∈ LinearMap.range (embR P Q R h k) := by
  rw [← sum_homogeneousComponent G, map_sum, map_sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  rw [homogeneousComponent_of_mem (embR_isHomogeneous P Q R h k (homogeneousComponent_isHomogeneous m G))]
  split_ifs
  · exact LinearMap.mem_range_self _ _
  · exact Submodule.zero_mem _

end GlobalTheory.CharPair.GradR
end

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_component_in_range_embedding : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (G : Mdl P Q) (n : ℕ), homogeneousComponent n (embR P Q R h k G) ∈ LinearMap.range (embR P Q R h k) := by
  atlas_forward_decl GlobalTheory.CharPair.GradR.homogeneousComponent_embR_mem
end

section
section
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

noncomputable section

namespace GlobalTheory.CharPair

def leftInvVal (P Q R : ℕ) : Ix P Q × Ix R 0 → Mdl P Q
  | (Sum.inl a, Sum.inl c) => if (c : ℕ) = (a : ℕ) then 1 else 0
  | (Sum.inr b, Sum.inl c) => if hc : (c : ℕ) < P then X (⟨c, hc⟩, b) else 0
  | (_, Sum.inr _) => 0

theorem leftInv_mR (P Q R : ℕ) (h : P ≤ R) (a : Fin P) (b : Fin Q) :
    aeval (leftInvVal P Q R) (mR P Q R a b) = (X (a, b) : Mdl P Q) := by
  rw [mR, map_sum, Finset.sum_eq_single (Fin.castLE h a)]
  · simp [leftInvVal]
  · intro c _ hc
    have : (c : ℕ) ≠ (a : ℕ) := fun e => hc (Fin.ext e)
    simp [leftInvVal, this]
  · simp

theorem leftInv_detR (P Q R : ℕ) (h : P ≤ R) :
    aeval (leftInvVal P Q R) (detR P Q R h) = (1 : Mdl P Q) := by
  rw [detR, AlgHom.map_det, ← Matrix.det_one (n := Fin P)]
  congr 1
  ext1 a c
  simp [leftInvVal, Matrix.one_apply, Fin.val_inj, eq_comm]

theorem leftInv_embR (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (G : Mdl P Q) :
    aeval (leftInvVal P Q R) (embR P Q R h k G) = G := by
  have e : (aeval (leftInvVal P Q R) : Pol P Q R 0 →ₐ[ℂ] Mdl P Q).comp
      (aeval fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) = AlgHom.id ℂ (Mdl P Q) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, b⟩
    rw [AlgHom.comp_apply, aeval_X, AlgHom.id_apply]
    exact leftInv_mR P Q R h a b
  have e2 := AlgHom.congr_fun e G
  simp only [AlgHom.comp_apply, AlgHom.id_apply] at e2
  simp only [embR, LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply, map_mul, map_pow,
    leftInv_detR, one_pow, mul_one, e2]

theorem embR_injective : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ), Function.Injective (embR P Q R h k) :=
  fun P Q R h k => Function.LeftInverse.injective (g := aeval (leftInvVal P Q R)) (leftInv_embR P Q R h k)

end GlobalTheory.CharPair

end
end

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_rank_embedding : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ), Function.Injective (embR P Q R h k) := by
  atlas_forward_decl GlobalTheory.CharPair.embR_injective
end

section
section
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair

theorem fockAct1_Eab_inl_inr_embR : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q),
    fockAct1 P Q R 0 (Eab (Sum.inl a) (Sum.inr b)) (embR P Q R h k G) =
      embR P Q R h k (opR P Q R k (Sum.inl a) (Sum.inr b) G) := by
  intro P Q R h k a b G
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  have hterm : ∀ c : Fin R, omE ((Sum.inl a : Ix P Q), (Sum.inl c : Ix R 0)) (Sum.inr b, Sum.inl c)
      (embR P Q R h k G) = (X (Sum.inl a, Sum.inl c) * X (Sum.inr b, Sum.inl c)) * embR P Q R h k G := by
    intro c
    simp [omE, raiB, lowB, linePos, mul_assoc]
  simp only [hterm, ← Finset.sum_mul]
  simp only [opR, mulM, embR, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
    AlgHom.toLinearMap_apply, LinearMap.mulRight_apply, map_mul, aeval_X, mR]
  ring

end GlobalTheory.CharPair
end

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_action_commutes_with_embedding : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q), fockAct1 P Q R 0 (Eab (Sum.inl a) (Sum.inr b)) (embR P Q R h k G) = embR P Q R h k (opR P Q R k (Sum.inl a) (Sum.inr b) G) := by
  atlas_forward_decl GlobalTheory.CharPair.fockAct1_Eab_inl_inr_embR
end

section
section
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

noncomputable section

namespace GlobalTheory.CharPair.Down

variable {P Q R : ℕ}

theorem pderiv_pderiv_comm {σ : Type} (i j : σ) (f : MvPolynomial σ ℂ) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  classical
  have h0 : ⁅(pderiv i : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)),
      (pderiv j : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
    simp only [Pi.single_apply]
    split_ifs <;> simp
  have := congrArg (fun D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ) => D f) h0
  simpa [Derivation.commutator_apply, sub_eq_zero] using this

theorem pderiv_s_mR (a' a : Fin P) (b : Fin Q) (c : Fin R) :
    pderiv (Sum.inl a', Sum.inl c) (mR P Q R a b) =
      if a' = a then X (Sum.inr b, Sum.inl c) else 0 := by
  classical
  simp [mR, map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply]
  rcases eq_or_ne a' a with rfl | ha
  · simp
  · simp [ha, Ne.symm ha]

theorem pderiv_w_mR (b' : Fin Q) (a : Fin P) (b : Fin Q) (c : Fin R) :
    pderiv (Sum.inr b', Sum.inl c) (mR P Q R a b) =
      if b' = b then X (Sum.inl a, Sum.inl c) else 0 := by
  classical
  simp [mR, map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply]
  rcases eq_or_ne b' b with rfl | hb
  · simp
  · simp [hb, Ne.symm hb]

theorem embR_eq (h : P ≤ R) (k : ℕ) (G : Mdl P Q) :
    embR P Q R h k G = aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) G * detR P Q R h ^ k := by
  simp [embR]

theorem derivation_det_eq_zero {σ : Type} {n : ℕ} (d : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) (hM : ∀ i j, d (M i j) = 0) : d M.det = 0 := by
  have e : M.det = aeval (fun ij : Fin n × Fin n => M ij.1 ij.2)
      (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ)) := by
    rw [← AlgHom.coe_toRingHom, RingHom.map_det]; congr 1; ext i j; simp [Matrix.mvPolynomialX]
  rw [e, ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.derivation_aeval_eq]
  simp [hM]

def blockR (h : P ≤ R) : Matrix (Fin P) (Fin P) (Pol P Q R 0) :=
  Matrix.of fun a c : Fin P => (X (Sum.inl a, Sum.inl (Fin.castLE h c)) : Pol P Q R 0)

theorem detR_eq (h : P ≤ R) : detR P Q R h = (blockR (Q := Q) h).det := rfl

theorem pderiv_w_detR (h : P ≤ R) (b : Fin Q) (c : Fin R) :
    pderiv (Sum.inr b, Sum.inl c) (detR P Q R h) = 0 := by
  classical
  rw [detR_eq]
  apply derivation_det_eq_zero
  intro i j
  simp [blockR, pderiv_X, Pi.single_apply]

theorem pderiv_s_detR (h : P ≤ R) (a : Fin P) (c : Fin R) :
    pderiv (Sum.inl a, Sum.inl c) (detR P Q R h) =
      ∑ j : Fin P, if Fin.castLE h j = c then (blockR (Q := Q) h).adjugate j a else 0 := by
  classical
  rw [detR_eq, Matrix.det_eq_sum_mul_adjugate_row _ a, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hadj : pderiv (Sum.inl a, Sum.inl c) ((blockR (Q := Q) h).adjugate j a) = 0 := by
    rw [Matrix.adjugate_apply]
    apply derivation_det_eq_zero
    intro i j'
    rw [Matrix.updateRow_apply]
    split_ifs with hi
    · simp [Pi.single_apply]; split_ifs <;> simp
    · simp [blockR, pderiv_X, Pi.single_apply, hi]
  rw [Derivation.leibniz, hadj]
  simp [blockR, pderiv_X, Pi.single_apply, eq_comm]
  done

theorem sum_s_pderiv_detR (h : P ≤ R) (a' a : Fin P) :
    ∑ c : Fin R, X (Sum.inl a', Sum.inl c) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h) =
      if a' = a then detR P Q R h else 0 := by
  classical
  have e : ∀ c : Fin R, X (Sum.inl a', Sum.inl c) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h) =
      ∑ j : Fin P, if Fin.castLE h j = c then blockR (Q := Q) h a' j * (blockR (Q := Q) h).adjugate j a
        else 0 := by
    intro c
    rw [pderiv_s_detR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hj
    · simp [blockR, hj]
    · simp
  rw [Finset.sum_congr rfl fun c _ => e c, Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← Matrix.mul_apply, Matrix.mul_adjugate, detR_eq]
  simp [Matrix.one_apply]

abbrev phiR (P Q R : ℕ) : Mdl P Q →ₐ[ℂ] Pol P Q R 0 := aeval fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2

theorem pderiv_s_phiR (a : Fin P) (c : Fin R) (H : Mdl P Q) :
    pderiv (Sum.inl a, Sum.inl c) (phiR P Q R H) =
      ∑ b' : Fin Q, phiR P Q R (pderiv (a, b') H) * X (Sum.inr b', Sum.inl c) := by
  classical
  rw [ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.derivation_aeval_eq, Fintype.sum_prod_type]
  simp only [pderiv_s_mR, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq]

theorem pderiv_w_phiR (b : Fin Q) (c : Fin R) (H : Mdl P Q) :
    pderiv (Sum.inr b, Sum.inl c) (phiR P Q R H) =
      ∑ a' : Fin P, phiR P Q R (pderiv (a', b) H) * X (Sum.inl a', Sum.inl c) := by
  classical
  rw [ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.derivation_aeval_eq, Fintype.sum_prod_type]
  simp only [pderiv_w_mR, mul_ite, mul_zero]
  simp [Finset.sum_ite_eq]

theorem pderiv_w_detR_pow (h : P ≤ R) (k : ℕ) (b : Fin Q) (c : Fin R) :
    pderiv (Sum.inr b, Sum.inl c) (detR P Q R h ^ k) = 0 := by
  rw [Derivation.leibniz_pow, pderiv_w_detR]; simp

theorem pderiv_w_s_detR_pow (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (c : Fin R) :
    pderiv (Sum.inr b, Sum.inl c) (pderiv (Sum.inl a, Sum.inl c) (detR P Q R h ^ k)) = 0 := by
  rw [pderiv_pderiv_comm, pderiv_w_detR_pow]; simp

theorem sum_s_pderiv_detR_pow (h : P ≤ R) (k : ℕ) (a' a : Fin P) :
    ∑ c : Fin R, X (Sum.inl a', Sum.inl c) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h ^ k) =
      if a' = a then (k : Pol P Q R 0) * detR P Q R h ^ k else 0 := by
  classical
  simp only [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]
  have e : ∀ c : Fin R, X (Sum.inl a', Sum.inl c) *
      ((k : Pol P Q R 0) * (detR P Q R h ^ (k - 1) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h))) =
      (k : Pol P Q R 0) * detR P Q R h ^ (k - 1) *
        (X (Sum.inl a', Sum.inl c) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h)) := fun c => by ring
  rw [Finset.sum_congr rfl fun c _ => e c, ← Finset.mul_sum, sum_s_pderiv_detR]
  split_ifs
  · rcases k with _ | k
    · simp
    · simp [pow_succ]; ring
  · simp

theorem omE_down (a : Fin P) (b : Fin Q) (c : Fin R) (f : Pol P Q R 0) :
    omE ((Sum.inr b, Sum.inl c) : Ln P Q R 0) (Sum.inl a, Sum.inl c) f =
      -(pderiv (Sum.inr b, Sum.inl c) (pderiv (Sum.inl a, Sum.inl c) f)) := by
  simp [omE, raiB, lowB, linePos]

theorem partial_derivative_weight_space_formula (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (c : Fin R) (G : Mdl P Q) :
    pderiv (Sum.inr b, Sum.inl c) (pderiv (Sum.inl a, Sum.inl c) (phiR P Q R G * detR P Q R h ^ k)) =
      (∑ b' : Fin Q, (∑ a' : Fin P, phiR P Q R (pderiv (a', b) (pderiv (a, b') G)) *
          X (Sum.inl a', Sum.inl c)) * X (Sum.inr b', Sum.inl c)) * detR P Q R h ^ k
        + phiR P Q R (pderiv (a, b) G) * detR P Q R h ^ k
        + ∑ a' : Fin P, phiR P Q R (pderiv (a', b) G) *
          (X (Sum.inl a', Sum.inl c) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h ^ k)) := by
  classical
  have hw : pderiv (Sum.inr b, Sum.inl c) (∑ b' : Fin Q, phiR P Q R (pderiv (a, b') G) *
      X (Sum.inr b', Sum.inl c)) = (∑ b' : Fin Q, (∑ a' : Fin P, phiR P Q R (pderiv (a', b) (pderiv (a, b') G)) *
          X (Sum.inl a', Sum.inl c)) * X (Sum.inr b', Sum.inl c)) + phiR P Q R (pderiv (a, b) G) := by
    simp only [map_sum, Derivation.leibniz, pderiv_w_phiR, pderiv_X, smul_eq_mul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun b' _ => by ring
    · simp only [Pi.single_apply, Prod.mk.injEq, Sum.inr.injEq, and_true, mul_ite, mul_one, mul_zero]
      simp
  rw [Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, Derivation.leibniz, Derivation.leibniz,
    pderiv_s_phiR, hw, pderiv_w_phiR, pderiv_w_s_detR_pow, pderiv_w_detR_pow]
  simp only [smul_eq_mul, mul_zero, add_zero]
  rw [Finset.mul_sum, Finset.sum_congr rfl fun a' _ => (by ring :
    pderiv (Sum.inl a, Sum.inl c) (detR P Q R h ^ k) * (phiR P Q R (pderiv (a', b) G) * X (Sum.inl a', Sum.inl c)) =
      phiR P Q R (pderiv (a', b) G) * (X (Sum.inl a', Sum.inl c) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h ^ k)))]
  ring

theorem opR_down (k : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) :
    opR P Q R k (Sum.inr b) (Sum.inl a) G =
      -(∑ a' : Fin P, ∑ b' : Fin Q, X (a', b') * pderiv (a', b) (pderiv (a, b') G)
        + ((R + k : ℕ) : ℂ) • pderiv (a, b) G) := by
  simp [opR, LinearMap.sum_apply, Module.End.mul_apply]

theorem sum_A (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) :
    ∑ c : Fin R, (∑ b' : Fin Q, (∑ a' : Fin P, phiR P Q R (pderiv (a', b) (pderiv (a, b') G)) *
          X (Sum.inl a', Sum.inl c)) * X (Sum.inr b', Sum.inl c)) * detR P Q R h ^ k =
      (∑ a' : Fin P, ∑ b' : Fin Q, mR P Q R a' b' * phiR P Q R (pderiv (a', b) (pderiv (a, b') G))) *
        detR P Q R h ^ k := by
  rw [← Finset.sum_mul]
  congr 1
  simp only [mR, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext b'; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem sum_C (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) :
    ∑ c : Fin R, ∑ a' : Fin P, phiR P Q R (pderiv (a', b) G) *
        (X (Sum.inl a', Sum.inl c) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h ^ k)) =
      phiR P Q R (pderiv (a, b) G) * ((k : Pol P Q R 0) * detR P Q R h ^ k) := by
  classical
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_s_pderiv_detR_pow, mul_ite, mul_zero]
  simp

theorem embR_eq' (h : P ≤ R) (k : ℕ) (G : Mdl P Q) :
    embR P Q R h k G = phiR P Q R G * detR P Q R h ^ k := embR_eq h k G

end GlobalTheory.CharPair.Down

namespace GlobalTheory.CharPair

open GlobalTheory.CharPair.Down in

theorem fockAct1_embR_inr_inl (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) :
    fockAct1 P Q R 0 (Eab (Sum.inr b) (Sum.inl a)) (embR P Q R h k G) =
      embR P Q R h k (opR P Q R k (Sum.inr b) (Sum.inl a) G) := by
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  rw [embR_eq', embR_eq', opR_down]
  simp only [omE_down, partial_derivative_weight_space_formula, Finset.sum_neg_distrib, Finset.sum_add_distrib, sum_A, sum_C,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [map_neg, map_add, map_sum, map_mul, map_smul, phiR, aeval_X]
  rw [nsmul_eq_mul, Algebra.smul_def, map_natCast]
  push_cast
  ring

end GlobalTheory.CharPair
end
end

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_action_lower_left_commutes_embedding : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q), fockAct1 P Q R 0 (Eab (Sum.inr b) (Sum.inl a)) (embR P Q R h k G) = embR P Q R h k (opR P Q R k (Sum.inr b) (Sum.inl a) G) := by
  atlas_forward_decl GlobalTheory.CharPair.fockAct1_embR_inr_inl
end

section
section
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair.FirstBlock

section General

variable {K A : Type} [CommRing K] [CommRing A] [Algebra K A]

theorem der_aeval {σ : Type} [Fintype σ] [DecidableEq σ] (d : Derivation K A A) (z : σ → A)
    (G : MvPolynomial σ K) : d (aeval z G) = ∑ i, aeval z (pderiv i G) * d (z i) := by
  induction G using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p n hp =>
    have e : ∀ i, aeval z (pderiv i (p * X n)) * d (z i) =
        (if n = i then aeval z p * d (z i) else 0) + z n * (aeval z (pderiv i p) * d (z i)) := by
      intro i
      by_cases hi : n = i
      · subst hi
        simp [Derivation.leibniz]; ring
      · simp [Derivation.leibniz, hi, pderiv_X, Pi.single_apply]; ring
    simp only [e, Finset.sum_add_distrib]
    simp [hp, Finset.mul_sum]

theorem der_prod {ι : Type} [DecidableEq ι] (d : Derivation K A A) (s : Finset ι) (f : ι → A) :
    d (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * d (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Derivation.leibniz, ih, Finset.erase_insert ha,
      smul_eq_mul, smul_eq_mul, add_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne : a ≠ i := fun e => ha (e ▸ hi)
    rw [Finset.erase_insert_of_ne hne, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h)),
      mul_assoc]

theorem der_det {n : Type} [Fintype n] [DecidableEq n] (d : Derivation K A A) (M : Matrix n n A) :
    d M.det = ∑ i, (M.updateRow i fun j => d (M i j)).det := by
  simp only [Matrix.det_apply, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.smul_sum, Units.smul_def, Units.smul_def, map_zsmul, der_prod,
    ← Equiv.sum_comp σ (fun i => ∏ x, (M.updateRow i fun j => d (M i j)) (σ x) x)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Matrix.updateRow_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Matrix.updateRow_ne (fun e => (Finset.mem_erase.1 hj).1 (σ.injective e))]

end General

variable {P Q R : ℕ}

noncomputable def rowDer (Q R : ℕ) (a a' : Fin P) : Derivation ℂ (Pol P Q R 0) (Pol P Q R 0) :=
  ∑ c : Fin R, (X (Sum.inl a, Sum.inl c) : Pol P Q R 0) • pderiv (Sum.inl a', Sum.inl c)

theorem rowDer_apply (a a' : Fin P) (F : Pol P Q R 0) :
    rowDer Q R a a' F = ∑ c : Fin R, X (Sum.inl a, Sum.inl c) * pderiv (Sum.inl a', Sum.inl c) F := by
  have := map_sum (Derivation.coeFnAddMonoidHom (R := ℂ) (A := Pol P Q R 0) (M := Pol P Q R 0))
    (fun c : Fin R => (X (Sum.inl a, Sum.inl c) : Pol P Q R 0) • pderiv (Sum.inl a', Sum.inl c)) Finset.univ
  have h2 := congrFun this F
  rw [Finset.sum_apply] at h2
  exact h2

theorem rowDer_X_inl_inl (a a' i : Fin P) (c : Fin R) :
    rowDer Q R a a' (X (Sum.inl i, Sum.inl c)) = if i = a' then X (Sum.inl a, Sum.inl c) else 0 := by
  rw [rowDer_apply]
  by_cases h : i = a' <;> simp [pderiv_X, Pi.single_apply, h]

theorem rowDer_w (a a' : Fin P) (b : Fin Q) (c : Fin R) :
    rowDer Q R a a' (X (Sum.inr b, Sum.inl c)) = 0 := by
  rw [rowDer_apply]
  simp [pderiv_X, Pi.single_apply]

theorem rowDer_mR (a a' i : Fin P) (b : Fin Q) :
    rowDer Q R a a' (mR P Q R i b) = if i = a' then mR P Q R a b else 0 := by
  simp only [mR, map_sum, Derivation.leibniz, rowDer_X_inl_inl, rowDer_w, smul_eq_mul]
  split_ifs <;> simp [mul_comm]

theorem rowDer_detR (h : P ≤ R) (a a' : Fin P) :
    rowDer Q R a a' (detR P Q R h) = if a = a' then detR P Q R h else 0 := by
  rw [detR, der_det, Finset.sum_eq_single a']
  · simp only [Matrix.of_apply, rowDer_X_inl_inl, if_true]
    split_ifs with e
    · subst e
      congr 1
      exact Matrix.updateRow_eq_self _ _
    · exact Matrix.det_updateRow_eq_zero (M := Matrix.of fun a c : Fin P =>
        (X (Sum.inl a, Sum.inl (Fin.castLE h c)) : Pol P Q R 0)) e
  · intro i _ hi
    simp only [Matrix.of_apply, rowDer_X_inl_inl, if_neg hi]
    exact Matrix.det_eq_zero_of_row_eq_zero i (by simp)
  · simp

theorem act_eq (a a' : Fin P) (F : Pol P Q R 0) :
    fockAct1 P Q R 0 (Eab (Sum.inl a) (Sum.inl a')) F =
      rowDer Q R a a' F + (if a = a' then (R : ℂ) / 2 else 0) • F := by
  have hpp : ∀ c : Fin R, omE (p := P) (q := Q) (r := R) (s := 0) (Sum.inl a, Sum.inl c) (Sum.inl a', Sum.inl c) F =
      X (Sum.inl a, Sum.inl c) * pderiv (Sum.inl a', Sum.inl c) F + (if a = a' then (1 / 2 : ℂ) else 0) • F := by
    intro c
    simp only [omE, raiB, lowB, linePos]
    by_cases e : a = a' <;> simp [e]
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type, rowDer_apply]
  simp only [hpp, Finset.sum_add_distrib, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  split_ifs
  · congr 2; ring
  · simp

theorem act_first_block : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (a a' : Fin P) (G : Mdl P Q), fockAct1 P Q R 0 (Eab (Sum.inl a) (Sum.inl a')) (embR P Q R h k G) = embR P Q R h k (opR P Q R k (Sum.inl a) (Sum.inl a') G) := by
  intro P Q R h k a a' G
  have hk : rowDer Q R a a' (detR P Q R h ^ k) = (if a = a' then (k : ℂ) else 0) • detR P Q R h ^ k := by
    rw [Derivation.leibniz_pow, rowDer_detR]
    split_ifs
    · rcases k with _ | k
      · simp
      · rw [Nat.cast_smul_eq_nsmul, Nat.add_sub_cancel, smul_eq_mul, ← pow_succ]
    · simp
  have hG : rowDer Q R a a' (aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) G) =
      ∑ b, mR P Q R a b * aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) (pderiv (a', b) G) := by
    rw [der_aeval, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [rowDer_mR, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [mul_comm]
  have he : ∀ H, embR P Q R h k H =
      aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) H * detR P Q R h ^ k := fun H => rfl
  have ho : opR P Q R k (Sum.inl a) (Sum.inl a') G =
      ∑ b, X (a, b) * pderiv (a', b) G + (if a = a' then (k : ℂ) + (R : ℂ) / 2 else 0) • G := by
    by_cases e : a = a' <;> simp [opR, LinearMap.sum_apply, e]
  rw [act_eq, he, he, ho, Derivation.leibniz, hk, hG, map_add, map_sum, map_smul]
  simp only [map_mul, aeval_X, smul_eq_mul, add_mul, mul_smul_comm, smul_mul_assoc]
  rw [mul_comm (detR P Q R h ^ k)]
  split_ifs
  · module
  · simp

end GlobalTheory.CharPair.FirstBlock
end

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_action_upper_left_commutes_embedding : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (a a' : Fin P) (G : Mdl P Q), fockAct1 P Q R 0 (Eab (Sum.inl a) (Sum.inl a')) (embR P Q R h k G) = embR P Q R h k (opR P Q R k (Sum.inl a) (Sum.inl a') G) := by
  atlas_forward_decl GlobalTheory.CharPair.FirstBlock.act_first_block
end

section
section
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

noncomputable section

namespace GlobalTheory.CharPair

variable {P Q R : ℕ}

theorem pderiv_detR_wLetter (h : P ≤ R) (b : Fin Q) (c : Fin R) :
    pderiv (Sum.inr b, Sum.inl c) (detR P Q R h) = 0 := by
  let g : Fin P × Fin P → Ix P Q × Ix R 0 := fun ac => (Sum.inl ac.1, Sum.inl (Fin.castLE h ac.2))
  have : detR P Q R h = rename g (Matrix.det (Matrix.mvPolynomialX (Fin P) (Fin P) ℂ)) := by
    rw [detR, ← AlgHom.coe_toRingHom, RingHom.map_det]; congr 1; ext a c; simp [g, Matrix.mvPolynomialX]
  rw [this]
  apply pderiv_eq_zero_of_notMem_vars
  intro hv
  obtain ⟨x, -, hx⟩ := Finset.mem_image.1 (vars_rename g _ hv)
  simp [g] at hx

theorem wPolarize_aeval_mR (b b' : Fin Q) (G : Mdl P Q) :
    ∑ c : Fin R, X (Sum.inr b', Sum.inl c) * pderiv (Sum.inr b, Sum.inl c)
        (aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) G) =
      aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) (∑ a, X (a, b') * pderiv (a, b) G) := by
  induction G using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, mul_add, Finset.sum_add_distrib, hp, hq]
  | mul_X p n hp =>
    have key : ∑ c : Fin R, X (Sum.inr b', Sum.inl c) * pderiv (Sum.inr b, Sum.inl c) (mR P Q R n.1 n.2)
        = aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2)
            (∑ a, X (a, b') * pderiv (a, b) (X n : Mdl P Q)) := by
      obtain ⟨a, b''⟩ := n
      by_cases hb : b'' = b
      · subst hb
        simp [mR, pderiv_X, Pi.single_apply, mul_comm]
      · simp [mR, pderiv_X, Pi.single_apply, hb]
    have e1 : ∀ (A B : Pol P Q R 0), ∑ c : Fin R, X (Sum.inr b', Sum.inl c) * pderiv (Sum.inr b, Sum.inl c) (A * B) =
        (∑ c : Fin R, X (Sum.inr b', Sum.inl c) * pderiv (Sum.inr b, Sum.inl c) A) * B +
          A * ∑ c : Fin R, X (Sum.inr b', Sum.inl c) * pderiv (Sum.inr b, Sum.inl c) B := by
      intro A B
      simp only [pderiv_mul, mul_add, Finset.sum_add_distrib]
      rw [Finset.sum_mul, Finset.mul_sum]
      exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm)
        (Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _)
    have e2 : ∀ (A B : Mdl P Q), ∑ a, X (a, b') * pderiv (a, b) (A * B) =
        (∑ a, X (a, b') * pderiv (a, b) A) * B + A * ∑ a, X (a, b') * pderiv (a, b) B := by
      intro A B
      simp only [pderiv_mul, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
      congr 1 <;> refine Finset.sum_congr rfl fun _ _ => by ring
    rw [map_mul, aeval_X, e1, hp, key, e2, map_add, map_mul, map_mul, aeval_X]

theorem fockAct1_inr_inr_embR : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (b b' : Fin Q) (G : Mdl P Q),
    fockAct1 P Q R 0 (Eab (Sum.inr b) (Sum.inr b')) (embR P Q R h k G) =
      embR P Q R h k (opR P Q R k (Sum.inr b) (Sum.inr b') G) := by
  intro P Q R h k b b' G
  have hD : ∀ c : Fin R, pderiv (Sum.inr b, Sum.inl c) (detR P Q R h ^ k) = 0 := fun c => by
    simp [Derivation.leibniz_pow, pderiv_detR_wLetter]
  have hw := wPolarize_aeval_mR (R := R) b b' G
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    GlobalTheory.CompactHarm.omE_nn (Sum.inr b, Sum.inl _) (Sum.inr b', Sum.inl _) rfl rfl]
  simp only [embR, opR, LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply, pderiv_mul, hD,
    mul_zero, add_zero, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.sum_apply, Module.End.mul_apply,
    LinearMap.smul_apply, Module.End.one_apply, map_sub, map_neg, map_smul, Prod.mk.injEq, Sum.inr.injEq, and_true]
  have e : ∀ x : Fin P, (mulM x b') ((derM x b) G) = X (x, b') * pderiv (x, b) G := fun _ => rfl
  simp only [e, ← hw, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Finset.sum_mul, mul_assoc]
  rw [sub_right_inj]
  split_ifs
  · rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    ring
  · simp

end GlobalTheory.CharPair
end
end

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_action_lower_right_commutes_embedding : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (b b' : Fin Q) (G : Mdl P Q), fockAct1 P Q R 0 (Eab (Sum.inr b) (Sum.inr b')) (embR P Q R h k G) = embR P Q R h k (opR P Q R k (Sum.inr b) (Sum.inr b') G) := by
  atlas_forward_decl GlobalTheory.CharPair.fockAct1_inr_inr_embR
end

section
section
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair

open GlobalTheory.DefLift.BilFischer in
private theorem pair_symm' {σ : Type} [Fintype σ] (A B : MvPolynomial σ ℂ) : pair A B = pair B A := by
  classical
  induction A using MvPolynomial.induction_on' with
  | add A A' h h' => simp only [map_add, LinearMap.add_apply, h, h']
  | monomial α c =>
    induction B using MvPolynomial.induction_on' with
    | add B B' h h' => simp only [map_add, LinearMap.add_apply, h, h']
    | monomial β d =>
      rw [pair_monomial, pair_monomial, coeff_monomial, coeff_monomial]
      by_cases e : α = β
      · subst e; simp only [if_true]; ring
      · simp [e, Ne.symm e]

open GlobalTheory.DefLift.BilFischer in
private theorem pair_pderiv' {σ : Type} [Fintype σ] (A B : MvPolynomial σ ℂ) (v : σ) :
    pair (pderiv v A) B = pair A (B * X v) := by
  rw [pair_symm', ← pair_mul_X, pair_symm']

theorem pair_fockAct1_embS_up : ∀ (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) (f : Pol P Q 0 S), GlobalTheory.DefLift.BilFischer.pair (fockAct1 P Q 0 S (Eab (Sum.inl a) (Sum.inr b)) f) (embS P Q S h k' G) = GlobalTheory.DefLift.BilFischer.pair f (embS P Q S h k' (opS P Q S k' (Sum.inl a) (Sum.inr b) G)) := by
  intro P Q S h k' a b G f
  have hom : ∀ c : Fin S, omE ((Sum.inl a, Sum.inr c) : Ln P Q 0 S) (Sum.inr b, Sum.inr c) f =
      -(pderiv (Sum.inl a, Sum.inr c) (pderiv (Sum.inr b, Sum.inr c) f)) := by
    intro c
    have h1 : linePos ((Sum.inl a, Sum.inr c) : Ln P Q 0 S) = false := rfl
    have h2 : linePos ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) = true := rfl
    simp [omE, raiB, lowB, h1, h2]
  have hE : embS P Q S h k' (opS P Q S k' (Sum.inl a) (Sum.inr b) G) =
      -(embS P Q S h k' G * mS P Q S a b) := by
    simp only [opS, embS, LinearMap.neg_apply, map_neg, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, AlgHom.toLinearMap_apply, map_mul, aeval_X]
    ring
  rw [hE, fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add, hom, map_sum, map_neg,
    LinearMap.sum_apply, LinearMap.neg_apply, pair_pderiv', mS, Finset.mul_sum,
    Finset.sum_neg_distrib, mul_assoc]

end GlobalTheory.CharPair
end

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fischer_pairing_adjoint_mixed_upper : ∀ (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) (f : Pol P Q 0 S), GlobalTheory.DefLift.BilFischer.pair (fockAct1 P Q 0 S (Eab (Sum.inl a) (Sum.inr b)) f) (embS P Q S h k' G) = GlobalTheory.DefLift.BilFischer.pair f (embS P Q S h k' (opS P Q S k' (Sum.inl a) (Sum.inr b) G)) := by
  atlas_forward_decl GlobalTheory.CharPair.pair_fockAct1_embS_up
end

section
section
noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair.ActSFirstBlock

open GlobalTheory.DefLift.BilFischer

theorem pair_comm {σ : Type} [Fintype σ] (A B : MvPolynomial σ ℂ) : pair A B = pair B A := by
  classical
  induction A using MvPolynomial.induction_on' with
  | add A A' h h' => simp only [map_add, LinearMap.add_apply, h, h']
  | monomial α c =>
    induction B using MvPolynomial.induction_on' with
    | add B B' h h' => simp only [map_add, LinearMap.add_apply, h, h']
    | monomial β d =>
      rw [pair_monomial, pair_monomial, coeff_monomial, coeff_monomial]
      by_cases e : α = β
      · subst e; simp; ring
      · simp [e, Ne.symm e]

theorem pair_pderiv {σ : Type} [Fintype σ] (A B : MvPolynomial σ ℂ) (v : σ) :
    pair (pderiv v A) B = pair A (X v * B) := by
  rw [pair_comm, ← pair_mul_X, pair_comm, mul_comm]

theorem pair_X_mul {σ : Type} [Fintype σ] (A B : MvPolynomial σ ℂ) (v : σ) :
    pair (X v * A) B = pair A (pderiv v B) := by
  rw [mul_comm, pair_mul_X]

theorem omE_neg {p q r s : ℕ} (u v : Ln p q r s) (hu : linePos u = false) (hv : linePos v = false)
    (F : Pol p q r s) :
    omE u v F = -(X v * pderiv u F) - (if u = v then (1 / 2 : ℂ) else 0) • F := by
  have : omE u v F = -(pderiv u (X v * F)) + (if u = v then (1 / 2 : ℂ) else 0) • F := by
    simp only [omE, raiB, lowB, hu, hv, Bool.false_eq_true, if_false]
    split_ifs <;> simp
  rw [this, Derivation.leibniz, pderiv_X, Pi.single_apply]
  by_cases e : u = v
  · subst e
    simp only [if_true, smul_eq_mul, mul_one]
    module
  · simp [e, Ne.symm e]

theorem pderiv_aeval {σ τ : Type} [Fintype σ] (m : σ → MvPolynomial τ ℂ) (v : τ) (G : MvPolynomial σ ℂ) :
    pderiv v (aeval m G) = ∑ i, aeval m (pderiv i G) * pderiv v (m i) := by
  classical
  induction G using MvPolynomial.induction_on with
  | C c => simp
  | add A B h h' => simp only [map_add, h, h', add_mul, Finset.sum_add_distrib]
  | mul_X A u h =>
    simp only [map_mul, aeval_X, Derivation.leibniz, h, smul_eq_mul, map_add, add_mul,
      Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    congr 1
    rw [Finset.sum_eq_single u]
    · simp
    · intro w _ hw
      simp [pderiv_X, Pi.single_apply, hw, Ne.symm hw]
    · simp

theorem pderiv_detS (P Q S : ℕ) (h : Q ≤ S) (a : Fin P) (c : Ix 0 S) :
    pderiv (Sum.inl a, c) (detS P Q S h) = 0 := by
  classical
  let g : Fin Q × Fin Q → Ix P Q × Ix 0 S := fun bc => (Sum.inr bc.1, Sum.inr (Fin.castLE h bc.2))
  have : detS P Q S h = aeval (fun i => X (g i)) (Matrix.det (Matrix.mvPolynomialX (Fin Q) (Fin Q) ℂ)) := by
    rw [detS, ← AlgHom.coe_toRingHom, RingHom.map_det]; congr 1; ext b c; simp [g, Matrix.mvPolynomialX]
  rw [this, pderiv_aeval]
  simp [g, pderiv_X, Pi.single_apply]

theorem pderiv_mS (P Q S : ℕ) (a a' : Fin P) (c : Fin S) (b : Fin Q) :
    pderiv (Sum.inl a', Sum.inr c) (mS P Q S a b) =
      if a = a' then X (Sum.inr b, Sum.inr c) else 0 := by
  classical
  simp only [mS, map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply, smul_eq_mul, Prod.mk.injEq,
    Sum.inl.injEq, Sum.inr.injEq]
  split_ifs with e
  · simp [e]
  · simp [e]

theorem euler_embS (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (a a' : Fin P) (G : Mdl P Q) :
    ∑ c : Fin S, X (Sum.inl a, Sum.inr c) * pderiv (Sum.inl a', Sum.inr c) (embS P Q S h k' G) =
      embS P Q S h k' (∑ b, X (a, b) * pderiv (a', b) G) := by
  classical
  simp only [embS, LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply,
    Derivation.leibniz, Derivation.leibniz_pow, pderiv_detS, smul_zero, zero_add, smul_eq_mul,
    pderiv_aeval, pderiv_mS, map_sum, map_mul, aeval_X, Fintype.sum_prod_type, mul_zero, mul_ite,
    Finset.sum_mul, Finset.mul_sum]
  simp only [Finset.sum_comm (s := (Finset.univ : Finset (Fin P))), Finset.sum_ite_eq', Finset.mem_univ, if_true, mS, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem pair_act_first_block : ∀ (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (a a' : Fin P) (G : Mdl P Q) (f : Pol P Q 0 S), GlobalTheory.DefLift.BilFischer.pair (fockAct1 P Q 0 S (Eab (Sum.inl a) (Sum.inl a')) f) (embS P Q S h k' G) = GlobalTheory.DefLift.BilFischer.pair f (embS P Q S h k' (opS P Q S k' (Sum.inl a) (Sum.inl a') G)) := by
  intro P Q S h k' a a' G f
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type]
  simp only [omE_neg (Sum.inl _, Sum.inr _) (Sum.inl _, Sum.inr _) rfl rfl, Finset.univ_eq_empty,
    Finset.sum_empty, zero_add, map_sum, map_sub, map_neg, map_smul, LinearMap.sum_apply,
    LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.smul_apply, pair_X_mul, pair_pderiv,
    opS, Module.End.mul_apply, LinearMap.mulLeft_apply, Module.End.one_apply]
  have key := congrArg (pair f) (euler_embS P Q S h k' a a' G)
  simp only [map_sum] at key
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, key]
  by_cases e : a = a'
  · simp [e]
    ring
  · simp [e]

end GlobalTheory.CharPair.ActSFirstBlock

end
end

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fischer_pairing_adjoint_upper_block : ∀ (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (a a' : Fin P) (G : Mdl P Q) (f : Pol P Q 0 S), GlobalTheory.DefLift.BilFischer.pair (fockAct1 P Q 0 S (Eab (Sum.inl a) (Sum.inl a')) f) (embS P Q S h k' G) = GlobalTheory.DefLift.BilFischer.pair f (embS P Q S h k' (opS P Q S k' (Sum.inl a) (Sum.inl a') G)) := by
  atlas_forward_decl GlobalTheory.CharPair.ActSFirstBlock.pair_act_first_block
end

section
section
noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair GlobalTheory.DefLift.BilFischer

namespace GlobalTheory.CharPair.SecondBlockS

theorem pair_symm' {σ : Type} [Fintype σ] (f g : MvPolynomial σ ℂ) : pair f g = pair g f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial α c =>
    induction g using MvPolynomial.induction_on' with
    | monomial β d =>
      rw [pair_monomial, pair_monomial, coeff_monomial, coeff_monomial]
      by_cases h : α = β
      · subst h; simp; ring
      · simp [h, Ne.symm h]
    | add g g' h h' => simp only [map_add, LinearMap.add_apply, h, h']
  | add f f' h h' => simp only [map_add, LinearMap.add_apply, h, h']

theorem pair_X_pderiv {σ : Type} [Fintype σ] (f g : MvPolynomial σ ℂ) (u v : σ) :
    pair (X u * pderiv v f) g = pair f (X v * pderiv u g) := by
  rw [mul_comm, pair_mul_X, pair_symm', ← pair_mul_X, pair_symm', mul_comm]

variable {P Q S : ℕ}

def rowD (b b' : Fin Q) : Derivation ℂ (Pol P Q 0 S) (Pol P Q 0 S) :=
  ∑ c : Fin S, (X (Sum.inr b', Sum.inr c) : Pol P Q 0 S) • pderiv (Sum.inr b, Sum.inr c)

theorem rowD_apply (b b' : Fin Q) (g : Pol P Q 0 S) :
    rowD b b' g = ∑ c : Fin S, X (Sum.inr b', Sum.inr c) * pderiv (Sum.inr b, Sum.inr c) g := by
  rw [rowD, PI.RL.W.derivation_sum_apply]
  simp [Derivation.smul_apply, smul_eq_mul]

theorem rowD_X_inr_inr (b b' i : Fin Q) (c : Fin S) :
    rowD b b' (X (Sum.inr i, Sum.inr c) : Pol P Q 0 S) =
      if i = b then X (Sum.inr b', Sum.inr c) else 0 := by
  rw [rowD_apply]
  simp only [pderiv_X, Pi.single_apply, Prod.mk.injEq, mul_ite, mul_one, mul_zero, Sum.inr.injEq]
  by_cases h : i = b
  · subst h
    simp
  · simp [h]

theorem rowD_u (b b' : Fin Q) (a : Fin P) (c : Fin S) :
    rowD b b' (X (Sum.inl a, Sum.inr c) : Pol P Q 0 S) = 0 := by
  rw [rowD_apply]
  simp [pderiv_X, Pi.single_apply]

theorem rowD_mS (b b' i : Fin Q) (a : Fin P) :
    rowD b b' (mS P Q S a i) = if i = b then mS P Q S a b' else 0 := by
  simp only [mS, map_sum, Derivation.leibniz, rowD_X_inr_inr, rowD_u, smul_zero, add_zero, smul_eq_mul]
  split_ifs <;> simp

theorem rowD_detS (h : Q ≤ S) (b b' : Fin Q) :
    rowD b b' (detS P Q S h) = if b = b' then detS P Q S h else 0 := by
  rw [detS, PI.RL.W.derivation_det, Finset.sum_eq_single b]
  · simp only [Matrix.of_apply, rowD_X_inr_inr, if_true]
    split_ifs with hb
    · subst hb
      congr 1
      exact Matrix.updateRow_eq_self _ b
    · exact Matrix.det_updateRow_eq_zero (M := Matrix.of fun b c : Fin Q =>
        (X (Sum.inr b, Sum.inr (Fin.castLE h c)) : Pol P Q 0 S)) (Ne.symm hb)
  · intro i _ hi
    simp only [Matrix.of_apply, rowD_X_inr_inr, if_neg hi]
    exact Matrix.det_eq_zero_of_row_eq_zero i (by simp)
  · simp

theorem rowD_aeval (b b' : Fin Q) (G : Mdl P Q) :
    rowD b b' (aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) G) =
      aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) (∑ a, X (a, b') * pderiv (a, b) G) := by
  induction G using MvPolynomial.induction_on with
  | C c => simp
  | add G G' h h' => simp only [map_add, h, h', mul_add, Finset.sum_add_distrib]
  | mul_X G v h =>
    obtain ⟨a, i⟩ := v
    rw [map_mul, Derivation.leibniz, h, aeval_X, rowD_mS]
    simp only [Derivation.leibniz, smul_eq_mul, mul_add, Finset.sum_add_distrib, map_add, map_sum,
      map_mul, aeval_X, pderiv_X, Pi.single_apply, Prod.mk.injEq, Finset.mul_sum]
    refine congrArg₂ (· + ·) ?_ ?_
    · by_cases hi : i = b
      · subst hi
        rw [Finset.sum_eq_single a]
        · simp [mul_comm]
        · intro x _ hx
          simp [Ne.symm hx]
        · simp
      · simp [hi]
    · exact Finset.sum_congr rfl fun _ _ => by ring

theorem rowD_embS (h : Q ≤ S) (k' : ℕ) (b b' : Fin Q) (G : Mdl P Q) :
    rowD b b' (embS P Q S h k' G) = embS P Q S h k' (∑ a, X (a, b') * pderiv (a, b) G) +
      (if b = b' then (k' : ℂ) else 0) • embS P Q S h k' G := by
  simp only [embS, LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply]
  rw [Derivation.leibniz, rowD_aeval, Derivation.leibniz_pow, rowD_detS, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, add_comm, mul_comm]
  congr 1
  split_ifs
  · rcases k' with _ | k
    · simp
    · rw [Nat.cast_smul_eq_nsmul, mul_smul_comm, Nat.add_sub_cancel, ← pow_succ]
  · simp

theorem pair_fockAct1_inr_inr_embS (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (b b' : Fin Q) (G : Mdl P Q)
    (f : Pol P Q 0 S) :
    pair (fockAct1 P Q 0 S (Eab (Sum.inr b) (Sum.inr b')) f) (embS P Q S h k' G) =
      pair f (embS P Q S h k' (opS P Q S k' (Sum.inr b) (Sum.inr b') G)) := by
  have e : embS P Q S h k' (opS P Q S k' (Sum.inr b) (Sum.inr b') G) =
      rowD b b' (embS P Q S h k' G) + (if b = b' then (S : ℂ) / 2 else 0) • embS P Q S h k' G := by
    rw [rowD_embS, opS]
    simp only [LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_add, map_smul, LinearMap.mulLeft_apply, Derivation.coeFn_coe]
    split_ifs
    · rw [add_smul, add_assoc]
    · simp
  rw [e, fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type, rowD_apply]
  simp only [GlobalTheory.CompactHarm.omE_pp (Sum.inr _, Sum.inr _) (Sum.inr _, Sum.inr _) rfl rfl,
    Finset.univ_eq_empty, Finset.sum_empty, zero_add, map_sum, map_add, map_smul, LinearMap.sum_apply,
    LinearMap.add_apply, LinearMap.smul_apply, pair_X_pderiv, Finset.sum_add_distrib,
    Prod.mk.injEq, Sum.inr.injEq, and_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_mul]
  refine congrArg₂ (· + ·) rfl ?_
  split_ifs
  · ring
  · simp

end GlobalTheory.CharPair.SecondBlockS

end
end

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fischer_pairing_adjoint_lower_block : ∀ (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (b b' : Fin Q) (G : Mdl P Q) (f : Pol P Q 0 S), GlobalTheory.DefLift.BilFischer.pair (fockAct1 P Q 0 S (Eab (Sum.inr b) (Sum.inr b')) f) (embS P Q S h k' G) = GlobalTheory.DefLift.BilFischer.pair f (embS P Q S h k' (opS P Q S k' (Sum.inr b) (Sum.inr b') G)) := by
  atlas_forward_decl GlobalTheory.CharPair.SecondBlockS.pair_fockAct1_inr_inr_embS
end

section
noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
open scoped TensorProduct

namespace GlobalTheory.FockSplit

def jR (P Q R S : ℕ) : Ln P Q R 0 → Ln P Q R S := fun v => (v.1, Sum.elim Sum.inl (fun e => e.elim0) v.2)

def jS (P Q R S : ℕ) : Ln P Q 0 S → Ln P Q R S := fun v => (v.1, Sum.elim (fun e => e.elim0) Sum.inr v.2)

variable {P Q R S : ℕ}

theorem jR_injective : Function.Injective (jR P Q R S) := by
  rintro ⟨a, c | c⟩ ⟨a', c' | c'⟩ h
  · simp only [jR, Sum.elim_inl, Prod.mk.injEq, Sum.inl.injEq] at h; rw [h.1, h.2]
  · exact c'.elim0
  · exact c.elim0
  · exact c.elim0

theorem jS_injective : Function.Injective (jS P Q R S) := by
  rintro ⟨a, c | c⟩ ⟨a', c' | c'⟩ h
  · exact c.elim0
  · exact c.elim0
  · exact c'.elim0
  · simp only [jS, Sum.elim_inr, Prod.mk.injEq, Sum.inr.injEq] at h; rw [h.1, h.2]

theorem linePos_jR (l : Ln P Q R 0) : linePos (jR P Q R S l) = linePos l := by
  rcases l with ⟨a | a, c | c⟩ <;> first | exact c.elim0 | rfl

theorem linePos_jS (l : Ln P Q 0 S) : linePos (jS P Q R S l) = linePos l := by
  rcases l with ⟨a | a, c | c⟩ <;> first | exact c.elim0 | rfl

theorem jR_ne_jS (k : Ln P Q R 0) (m : Ln P Q 0 S) : jR P Q R S k ≠ jS P Q R S m := by
  rcases k with ⟨a, c | c⟩ <;> rcases m with ⟨a', e | e⟩
  · exact e.elim0
  · simp [jR, jS]
  · exact c.elim0
  · exact c.elim0

section General

variable {R' S' : ℕ} (j : Ln P Q R' S' → Ln P Q R S)

theorem pderiv_rename_eq_zero {σ τ : Type*} (i : σ → τ) (v : τ) (hv : ∀ m, i m ≠ v) (g : MvPolynomial σ ℂ) :
    pderiv v (rename i g) = 0 := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p m hp => simp [hp, pderiv_X, Pi.single_apply, hv m]

theorem pderiv_rename_mul (hj : Function.Injective j) (k : Ln P Q R' S') (f : Pol P Q R' S') (G : Pol P Q R S)
    (hG : pderiv (j k) G = 0) : pderiv (j k) (rename j f * G) = rename j (pderiv k f) * G := by
  rw [Derivation.leibniz, hG, smul_zero, zero_add, pderiv_rename hj, smul_eq_mul, mul_comm]

theorem raiB_rename_mul (hj : Function.Injective j) (hpos : ∀ l, linePos (j l) = linePos l) (l : Ln P Q R' S')
    (f : Pol P Q R' S') (G : Pol P Q R S) (hG : ∀ k, pderiv (j k) G = 0) :
    raiB (j l) (rename j f * G) = rename j (raiB l f) * G := by
  unfold raiB; rw [hpos l]
  split_ifs
  · simp [mul_assoc]
  · simp [pderiv_rename_mul j hj l f G (hG l)]

theorem lowB_rename_mul (hj : Function.Injective j) (hpos : ∀ l, linePos (j l) = linePos l) (l : Ln P Q R' S')
    (f : Pol P Q R' S') (G : Pol P Q R S) (hG : ∀ k, pderiv (j k) G = 0) :
    lowB (j l) (rename j f * G) = rename j (lowB l f) * G := by
  unfold lowB; rw [hpos l]
  split_ifs
  · simp [pderiv_rename_mul j hj l f G (hG l)]
  · simp [mul_assoc]

theorem omE_rename_mul (hj : Function.Injective j) (hpos : ∀ l, linePos (j l) = linePos l) (l l' : Ln P Q R' S')
    (f : Pol P Q R' S') (G : Pol P Q R S) (hG : ∀ k, pderiv (j k) G = 0) :
    omE (j l) (j l') (rename j f * G) = rename j (omE l l' f) * G := by
  simp only [omE, LinearMap.add_apply, Module.End.mul_apply, lowB_rename_mul j hj hpos l' f G hG,
    raiB_rename_mul j hj hpos l _ G hG, hj.eq_iff]
  split_ifs <;> simp [add_mul, smul_mul_assoc]

end General

theorem fockAct1_Eab_mul (a b : Ix P Q) (f : Pol P Q R 0) (g : Pol P Q 0 S) :
    fockAct1 P Q R S (Eab a b) (rename (jR P Q R S) f * rename (jS P Q R S) g) =
      rename (jR P Q R S) (fockAct1 P Q R 0 (Eab a b) f) * rename (jS P Q R S) g +
        rename (jR P Q R S) f * rename (jS P Q R S) (fockAct1 P Q 0 S (Eab a b) g) := by
  rw [fockAct1_Eab, fockAct1_Eab, fockAct1_Eab]
  simp only [LinearMap.sum_apply, LinearMap.add_apply, Fintype.sum_sum_type, Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_add,
    map_sum, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun c _ => ?_
    exact omE_rename_mul (jR P Q R S) jR_injective linePos_jR (a, .inl c) (b, .inl c) f _
      (fun k => pderiv_rename_eq_zero _ _ (fun m => (jR_ne_jS k m).symm) g)
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm, mul_comm (rename _ f)]
    exact omE_rename_mul (jS P Q R S) jS_injective linePos_jS (a, .inr c) (b, .inr c) g _
      (fun k => pderiv_rename_eq_zero _ _ (fun m => jR_ne_jS m k) f)

end GlobalTheory.FockSplit

namespace GlobalTheory.FockSplit

variable {P Q R S : ℕ}

theorem fockAct1_rename_mul (Z : Mat P Q) (f : Pol P Q R 0) (g : Pol P Q 0 S) :
    fockAct1 P Q R S Z (rename (jR P Q R S) f * rename (jS P Q R S) g) =
      rename (jR P Q R S) (fockAct1 P Q R 0 Z f) * rename (jS P Q R S) g +
        rename (jR P Q R S) f * rename (jS P Q R S) (fockAct1 P Q 0 S Z g) := by
  have hZ : Z = ∑ a, ∑ b, Z a b • Eab a b := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
    simp only [Eab, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hZ]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, fockAct1_Eab_mul, smul_add,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]

def toTens (P Q R S : ℕ) (v : Ln P Q R S) : Pol P Q R 0 ⊗[ℂ] Pol P Q 0 S :=
  Sum.elim (fun c => X (v.1, Sum.inl c) ⊗ₜ 1) (fun e => 1 ⊗ₜ X (v.1, Sum.inr e)) v.2

theorem hasForm_of_pairing : ∀ (P Q R S : ℕ) (x : ℚ) (b : Pol P Q R 0 →ₗ[ℂ] Pol P Q 0 S →ₗ[ℂ] ℂ), b ≠ 0 →
    (∀ Z f g, b (fockAct1 P Q R 0 Z f) g + b f (fockAct1 P Q 0 S Z g) = (x : ℂ) * Z.trace * b f g) →
    GlobalTheory.RealLift.HasForm P Q R S x := by
  intro P Q R S x b hb hinv
  let φ : Pol P Q R S →ₐ[ℂ] Pol P Q R 0 ⊗[ℂ] Pol P Q 0 S := aeval (toTens P Q R S)
  let μ : Pol P Q R 0 ⊗[ℂ] Pol P Q 0 S →ₐ[ℂ] Pol P Q R S :=
    Algebra.TensorProduct.productMap (rename (jR P Q R S)) (rename (jS P Q R S))
  have hμ : ∀ f g, μ (f ⊗ₜ g) = rename (jR P Q R S) f * rename (jS P Q R S) g := fun f g =>
    Algebra.TensorProduct.productMap_apply_tmul _ _ _ _
  have hφR : ∀ f, φ (rename (jR P Q R S) f) = f ⊗ₜ 1 := by
    intro f
    have : φ.comp (rename (jR P Q R S)) = Algebra.TensorProduct.includeLeft := by
      apply MvPolynomial.algHom_ext
      rintro ⟨a, c | c⟩
      · simp [φ, toTens, jR]
      · exact c.elim0
    simpa using congrArg (fun h => h f) this
  have hφS : ∀ g, φ (rename (jS P Q R S) g) = 1 ⊗ₜ g := by
    intro g
    have : φ.comp (rename (jS P Q R S)) = Algebra.TensorProduct.includeRight := by
      apply MvPolynomial.algHom_ext
      rintro ⟨a, c | c⟩
      · exact c.elim0
      · simp [φ, toTens, jS]
    simpa using congrArg (fun h => h g) this
  have hφ : ∀ f g, φ (rename (jR P Q R S) f * rename (jS P Q R S) g) = f ⊗ₜ g := by
    intro f g; rw [map_mul, hφR, hφS, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hμφ : μ.comp φ = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, c | c⟩
    · simp [φ, μ, toTens, jR]
    · simp [φ, μ, toTens, jS]
  let l : Pol P Q R S →ₗ[ℂ] ℂ := TensorProduct.lift b ∘ₗ φ.toLinearMap
  have hl : ∀ f g, l (rename (jR P Q R S) f * rename (jS P Q R S) g) = b f g := by
    intro f g; simp [l, hφ]
  refine ⟨l, ?_, ?_⟩
  · intro h0
    apply hb
    refine LinearMap.ext fun f => LinearMap.ext fun g => ?_
    have := congrArg (fun m => m (rename (jR P Q R S) f * rename (jS P Q R S) g)) h0
    simpa [hl] using this
  · intro Z F
    have key : ∀ t, l (fockAct1 P Q R S Z (μ t)) = (x : ℂ) * Z.trace * l (μ t) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul f g => rw [hμ, fockAct1_rename_mul, map_add, hl, hl, hl, hinv]
      | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂, mul_add]
    have hF : μ (φ F) = F := by simpa using congrArg (fun h => h F) hμφ
    simpa [hF] using key (φ F)

end GlobalTheory.FockSplit
end
end

section
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzero_equivariant_pairing_has_form : ∀ (P Q R S : ℕ) (x : ℚ) (b : Pol P Q R 0 →ₗ[ℂ] Pol P Q 0 S →ₗ[ℂ] ℂ), b ≠ 0 → (∀ Z f g, b (fockAct1 P Q R 0 Z f) g + b f (fockAct1 P Q 0 S Z g) = (x : ℂ) * Z.trace * b f g) → GlobalTheory.RealLift.HasForm P Q R S x := by
  first | exact @GlobalTheory.FockSplit.hasForm_of_pairing | exact GlobalTheory.FockSplit.hasForm_of_pairing | (intros; apply GlobalTheory.FockSplit.hasForm_of_pairing <;> assumption)
end

section
noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair

theorem L_proj (p q r s : ℕ) (W : Submodule ℂ (Pol p q r s))
    (hW : ∀ Z, ∀ f ∈ W, fockAct1 p q r s Z f ∈ W) (hg : ∀ f ∈ W, ∀ n, homogeneousComponent n f ∈ W) :
    ∃ π : Pol p q r s →ₗ[ℂ] Pol p q r s, (∀ f, π f ∈ W) ∧ (∀ f ∈ W, π f = f) ∧
      ∀ Z f, π (fockAct1 p q r s Z f) = fockAct1 p q r s Z (π f) := GlobalTheory.T.fock_invariant_subspace_equivariant_projection p q r s W hW hg

theorem L_grad (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (G : Mdl P Q) (n : ℕ) :
    homogeneousComponent n (embR P Q R h k G) ∈ LinearMap.range (embR P Q R h k) := GlobalTheory.T.homogeneous_component_in_range_embedding P Q R h k G n

theorem L_inj (P Q R : ℕ) (h : P ≤ R) (k : ℕ) : Function.Injective (embR P Q R h k) := GlobalTheory.T.injective_rank_embedding P Q R h k

theorem L_actR (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (i j : Ix P Q) (G : Mdl P Q) :
    fockAct1 P Q R 0 (Eab i j) (embR P Q R h k G) = embR P Q R h k (opR P Q R k i j G) := by
  rcases i with a | b <;> rcases j with a' | b'
  · exact GlobalTheory.T.fock_action_upper_left_commutes_embedding P Q R h k a a' G
  · exact GlobalTheory.T.fock_action_commutes_with_embedding P Q R h k a b' G
  · exact GlobalTheory.T.fock_action_lower_left_commutes_embedding P Q R h k a' b G
  · exact GlobalTheory.T.fock_action_lower_right_commutes_embedding P Q R h k b b' G

theorem L_actS (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (i j : Ix P Q) (G : Mdl P Q) (f : Pol P Q 0 S) :
    GlobalTheory.DefLift.BilFischer.pair (fockAct1 P Q 0 S (Eab i j) f) (embS P Q S h k' G) =
      GlobalTheory.DefLift.BilFischer.pair f (embS P Q S h k' (opS P Q S k' i j G)) := by
  rcases i with a | b <;> rcases j with a' | b'
  · exact GlobalTheory.T.fischer_pairing_adjoint_upper_block P Q S h k' a a' G f
  · exact GlobalTheory.T.fischer_pairing_adjoint_mixed_upper P Q S h k' a b' G f
  · exact GlobalTheory.T.fischer_pairing_adjoint_mixed_lower P Q S h k' a' b G f
  · exact GlobalTheory.T.fischer_pairing_adjoint_lower_block P Q S h k' b b' G f

theorem L_tensor (P Q R S : ℕ) (x : ℚ) (b : Pol P Q R 0 →ₗ[ℂ] Pol P Q 0 S →ₗ[ℂ] ℂ) (hb : b ≠ 0)
    (hinv : ∀ Z f g, b (fockAct1 P Q R 0 Z f) g + b f (fockAct1 P Q 0 S Z g) = (x : ℂ) * Z.trace * b f g) :
    GlobalTheory.RealLift.HasForm P Q R S x := GlobalTheory.T.nonzero_equivariant_pairing_has_form P Q R S x b hb hinv

theorem L_detS (P Q S : ℕ) (h : Q ≤ S) : detS P Q S h ≠ 0 := detS_ne_zero P Q S h

theorem op_sum' (P Q R S k k' : ℕ) (x : ℂ) (hk : S + k' = R + k) (hx : x = k + (R : ℂ) / 2 - (S : ℂ) / 2)
    (i j : Ix P Q) :
    opR P Q R k i j + opS P Q S k' i j = (if i = j then x else 0) • (1 : Module.End ℂ (Mdl P Q)) := by
  have hk' : ((S + k' : ℕ) : ℂ) = ((R + k : ℕ) : ℂ) := by rw [hk]
  have hk2 : (k' : ℂ) = R + k - S := by
    have := congrArg (fun n : ℕ => (n : ℂ)) hk; push_cast at this; linear_combination this
  rcases i with a | b <;> rcases j with a' | b'
  · simp only [opR, opS, Sum.inl.injEq]
    split_ifs with hh
    · rw [hx]; module
    · simp
  · simp [opR, opS]
  · simp only [opR, opS, hk', reduceCtorEq, if_false, zero_smul]
    abel
  · simp only [opR, opS, Sum.inr.injEq]
    split_ifs with hh
    · rw [hx, hk2]; module
    · simp

theorem act_sum (P Q R S k k' : ℕ) (x : ℂ) (hk : S + k' = R + k) (hx : x = k + (R : ℂ) / 2 - (S : ℂ) / 2)
    (Z : Mat P Q) (G : Mdl P Q) :
    actR P Q R k Z G + actS P Q S k' Z G = (x * Z.trace) • G := by
  have h : actR P Q R k Z + actS P Q S k' Z = (x * Z.trace) • (1 : Module.End ℂ (Mdl P Q)) := by
    rw [actR_apply, actS_apply, ← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib, ← smul_add, op_sum' P Q R S k k' x hk hx, smul_smul, mul_ite, mul_zero,
      ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, ← Finset.sum_smul]
    congr 1
    simp [Matrix.trace, Finset.mul_sum, mul_comm, mul_add]
  rw [← LinearMap.add_apply, h]; simp

theorem mat_eq_sum {P Q : ℕ} (Z : Mat P Q) : Z = ∑ i, ∑ j, Z i j • Eab i j := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
  simp [Eab, Matrix.smul_single]

theorem actR_full (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (Z : Mat P Q) (G : Mdl P Q) :
    fockAct1 P Q R 0 Z (embR P Q R h k G) = embR P Q R h k (actR P Q R k Z G) := by
  conv_lhs => rw [mat_eq_sum Z]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, L_actR, actR_apply]

theorem actS_full (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (Z : Mat P Q) (G : Mdl P Q) (f : Pol P Q 0 S) :
    GlobalTheory.DefLift.BilFischer.pair (fockAct1 P Q 0 S Z f) (embS P Q S h k' G) =
      GlobalTheory.DefLift.BilFischer.pair f (embS P Q S h k' (actS P Q S k' Z G)) := by
  conv_lhs => rw [mat_eq_sum Z]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, L_actS, actS_apply, smul_eq_mul]

theorem formEx : GlobalTheory.RealLift.FormEx := by
  intro P Q R S x k k' hP hQ _ _ hk hk'
  have hkk : S + k' = R + k := by
    have h1 : ((S + k' : ℕ) : ℚ) = ((R + k : ℕ) : ℚ) := by
      push_cast; rw [← hk, ← hk']; unfold cPair; ring
    exact_mod_cast h1
  have hx : (x : ℂ) = k + (R : ℂ) / 2 - (S : ℂ) / 2 := by
    have : x = k + (R : ℚ) / 2 - (S : ℚ) / 2 := by rw [← hk]; unfold cPair; ring
    rw [this]; push_cast; ring
  set e := embR P Q R hP k
  have hinj := L_inj P Q R hP k
  obtain ⟨π, hπW, hπid, hπeq⟩ := L_proj P Q R 0 (LinearMap.range e)
    (by rintro Z _ ⟨G, rfl⟩; exact ⟨_, (actR_full P Q R hP k Z G).symm⟩)
    (by rintro _ ⟨G, rfl⟩ n; exact L_grad P Q R hP k G n)
  let eq := LinearEquiv.ofInjective e hinj
  let κ : Pol P Q R 0 →ₗ[ℂ] Mdl P Q := eq.symm.toLinearMap ∘ₗ LinearMap.codRestrict _ π hπW
  have hκ : ∀ f, e (κ f) = π f := by
    intro f
    have := eq.apply_symm_apply ⟨π f, hπW f⟩
    simpa [eq, κ] using congrArg Subtype.val this
  have hκeq : ∀ Z f, κ (fockAct1 P Q R 0 Z f) = actR P Q R k Z (κ f) := by
    intro Z f; apply hinj
    rw [hκ, hπeq, ← hκ, actR_full]
  have hκ1 : κ (e 1) = 1 := by
    apply hinj; rw [hκ, hπid _ ⟨1, rfl⟩]
  let b : Pol P Q R 0 →ₗ[ℂ] Pol P Q 0 S →ₗ[ℂ] ℂ :=
    GlobalTheory.DefLift.BilFischer.pair.flip ∘ₗ (embS P Q S hQ k') ∘ₗ κ
  have hb : ∀ f g, b f g = GlobalTheory.DefLift.BilFischer.pair g (embS P Q S hQ k' (κ f)) := fun _ _ => rfl
  apply L_tensor P Q R S x b
  · intro h0
    have hne : embS P Q S hQ k' 1 ≠ 0 := by
      simp only [embS, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_one, LinearMap.mulRight_apply, one_mul]
      exact pow_ne_zero _ (L_detS P Q S hQ)
    apply hne
    apply GlobalTheory.DefLift.BilFischer.pair_nondeg
    intro g
    have := congrArg (fun t => t (e 1) g) h0
    simpa [hb, hκ1] using this
  · intro Z f g
    rw [hb, hb, hb, hκeq, actS_full, ← map_add, ← map_add, act_sum P Q R S k k' x hkk hx, map_smul, map_smul,
      smul_eq_mul]

end GlobalTheory.CharPair

end
end

section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.FormExists : GlobalTheory.RealLift.FormEx := by
  first | exact @GlobalTheory.CharPair.formEx | exact GlobalTheory.CharPair.formEx | (intros; apply GlobalTheory.CharPair.formEx <;> assumption)
end
