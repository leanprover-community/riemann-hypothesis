import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointRowWeightAntitoneOfMaxPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericRowCoefMemCoefAlgebraOfDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeLeOfColW
import Formalism.PieriBlockIdeals.PieriColumnMinors.RealLocalDeltaNabla
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixCoefficientPolySimpleSubquotient

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

set_option autoImplicit false

noncomputable section

open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory.HighWt

theorem rowWeight_le_colSum (N : ℕ) (d : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    (Finsupp.weight (rowW N N) d) a ≤ ∑ s, (Finsupp.weight (colW N N) d) s := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  rw [← Finset.mul_sum]
  simp only [rowW, colW, Finset.sum_pi_single', Finset.mem_univ, if_true]
  apply Nat.mul_le_mul_left
  rw [Pi.single_apply]
  split_ifs <;> omega

variable (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ)

def wtBox (τ : ι) : Finset (Fin N → ℕ) :=
  Fintype.piFinset fun _ => Finset.range (∑ s : Fin N, res N (lam τ) s + 1)

theorem sum_box (τ : ι) (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ dualWeyl O N N (res N (lam τ))) :
    ∑ w ∈ wtBox N lam τ, weightedHomogeneousComponent (rowW N N) w f = f := by
  classical
  have hc : IsWeightedHomogeneous (colW N N) f (res N (lam τ)) := by
    have := (Submodule.mem_inf.mp hf).1
    simpa [mem_weightedHomogeneousSubmodule] using this
  ext d
  rw [coeff_sum]
  simp only [coeff_weightedHomogeneousComponent]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    apply h
    have hd := hc (Ne.symm hne)
    simp only [wtBox, Fintype.mem_piFinset, Finset.mem_range]
    intro a
    have := rowWeight_le_colSum N d a
    rw [hd] at this
    omega

section Ops

variable {O N lam}

theorem isProj_idem {τ : ι} {w : Fin N → ℕ} {a : Module.End O (NablaT O N lam)} (h : IsProj O N lam τ w a) :
    a * a = a := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, Module.End.mul_apply]
  let y : dualWeyl O N N (res N (lam τ)) := rowProj O N (res N (lam τ)) w (x τ)
  have hy : (y : MvPolynomial (Fin N × Fin N) O) = weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial _ O) := rfl
  rw [h x y hy]
  have hy' : (y : MvPolynomial (Fin N × Fin N) O) =
      weightedHomogeneousComponent (rowW N N) w ((Function.update x τ y) τ : MvPolynomial _ O) := by
    rw [Function.update_self, hy, weightedHomogeneousComponent_eq_self
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _)]
  rw [h _ y hy', Function.update_idem]

theorem isProj_comm {τ τ' : ι} (hne : τ ≠ τ') {w w' : Fin N → ℕ} {a b : Module.End O (NablaT O N lam)}
    (ha : IsProj O N lam τ w a) (hb : IsProj O N lam τ' w' b) : a * b = b * a := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, Module.End.mul_apply]
  let y : dualWeyl O N N (res N (lam τ)) := rowProj O N (res N (lam τ)) w (x τ)
  let y' : dualWeyl O N N (res N (lam τ')) := rowProj O N (res N (lam τ')) w' (x τ')
  have hy : (y : MvPolynomial (Fin N × Fin N) O) = weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial _ O) := rfl
  have hy' : (y' : MvPolynomial (Fin N × Fin N) O) = weightedHomogeneousComponent (rowW N N) w' (x τ' : MvPolynomial _ O) := rfl
  rw [hb x y' hy', ha x y hy]
  have h1 : (y : MvPolynomial (Fin N × Fin N) O) =
      weightedHomogeneousComponent (rowW N N) w ((Function.update x τ' y') τ : MvPolynomial _ O) := by
    rw [Function.update_of_ne hne]; exact hy
  have h2 : (y' : MvPolynomial (Fin N × Fin N) O) =
      weightedHomogeneousComponent (rowW N N) w' ((Function.update x τ y) τ' : MvPolynomial _ O) := by
    rw [Function.update_of_ne hne.symm]; exact hy'
  rw [ha _ y h1, hb _ y' h2, Function.update_comm hne]

theorem isProj_sum (τ : ι) (e : (Fin N → ℕ) → Module.End O (NablaT O N lam)) (he : ∀ w, IsProj O N lam τ w (e w)) :
    ∑ w ∈ wtBox N lam τ, e w = 1 := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply, LinearMap.sum_apply, Module.End.one_apply]
  have key : ∀ w, e w (PiTensorProduct.tprod O x) =
      (PiTensorProduct.tprod O).toLinearMap x τ (rowProj O N (res N (lam τ)) w (x τ)) := by
    intro w
    rw [MultilinearMap.toLinearMap_apply]
    exact he w x _ rfl
  rw [Finset.sum_congr rfl (fun w _ => key w)]
  rw [← map_sum, MultilinearMap.toLinearMap_apply]
  have : ∑ w ∈ wtBox N lam τ, rowProj O N (res N (lam τ)) w (x τ) = x τ := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact sum_box O N lam τ _ (x τ).2
  rw [this, Function.update_eq_self]

end Ops

section Main

variable {O N lam}

def projA [Fintype ι] (τ : ι) (w : Fin N → ℕ) : alg O N lam :=
  ⟨(exists_unique_isProj O N ι lam τ w).choose,
    Algebra.subset_adjoin (Or.inr ⟨τ, w, (exists_unique_isProj O N ι lam τ w).choose_spec.1⟩)⟩

variable [Fintype ι]

theorem projA_isProj (τ : ι) (w : Fin N → ℕ) : IsProj O N lam τ w (projA (O := O) (lam := lam) τ w : Module.End O (NablaT O N lam)) :=
  (exists_unique_isProj O N ι lam τ w).choose_spec.1

theorem projA_eq {τ : ι} {w : Fin N → ℕ} {a : alg O N lam} (h : IsProj O N lam τ w a) : a = projA τ w :=
  Subtype.ext ((exists_unique_isProj O N ι lam τ w).choose_spec.2 _ h)

theorem projA_idem (τ : ι) (w : Fin N → ℕ) : projA (O := O) (lam := lam) τ w * projA τ w = projA τ w :=
  Subtype.ext (isProj_idem (projA_isProj τ w))

theorem projA_comm {τ τ' : ι} (hne : τ ≠ τ') (w w' : Fin N → ℕ) :
    projA (O := O) (lam := lam) τ w * projA τ' w' = projA τ' w' * projA τ w :=
  Subtype.ext (isProj_comm hne (projA_isProj τ w) (projA_isProj τ' w'))

theorem projA_sum (τ : ι) : ∑ w ∈ wtBox N lam τ, projA (O := O) (lam := lam) τ w = 1 := by
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finset_sum, OneMemClass.coe_one]
  exact isProj_sum τ _ (projA_isProj τ)

end Main

theorem exists_jointWt : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] (lam : ι → ℕ → ℕ) (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], Nontrivial Gm →
    ∃ w : ι → Fin N → ℕ, GlobalTheory.HighWt.JointWt O N lam Gm w := by
  intro O _ _ _ _ N ι _ _ lam Gm _ _ _
  have step : ∀ s : Finset ι, ∃ z : Gm, z ≠ 0 ∧ ∃ w : ι → Fin N → ℕ,
      ∀ τ ∈ s, projA (O := O) (lam := lam) τ (w τ) • z = z := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨z, hz⟩ := exists_ne (0 : Gm)
      exact ⟨z, hz, 0, by simp⟩
    | insert τ s hτ ih =>
      obtain ⟨z, hz, w, hw⟩ := ih
      have hsum : ∑ v ∈ wtBox N lam τ, projA (O := O) (lam := lam) τ v • z = z := by
        rw [← Finset.sum_smul, projA_sum, one_smul]
      obtain ⟨v, -, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum.symm ▸ hz)
      refine ⟨projA τ v • z, hv, Function.update w τ v, ?_⟩
      intro σ hσ
      rcases Finset.mem_insert.mp hσ with rfl | hσ
      · rw [Function.update_self, smul_smul, projA_idem]
      · have hne : σ ≠ τ := fun h => hτ (h ▸ hσ)
        rw [Function.update_of_ne hne, smul_smul, projA_comm hne, mul_smul, hw σ hσ]
  obtain ⟨z, hz, w, hw⟩ := step Finset.univ
  exact ⟨w, z, hz, fun τ a ha => by rw [projA_eq ha]; exact hw τ (Finset.mem_univ _)⟩

end GlobalTheory.HighWt
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_jointRowWeight_dualWeylModule : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], Nontrivial Gm → ∃ w : ι → Fin N → ℕ, GlobalTheory.HighWt.JointWt O N lam Gm w := by
  atlas_forward_decl GlobalTheory.HighWt.exists_jointWt
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

set_option autoImplicit false

open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory.HighWt

theorem dualWeyl_rowDeg_dominance (O : Type) [CommRing O] [IsDomain O] (N : ℕ) (ν : Fin N → ℕ)
    (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ dualWeyl O N N ν) : ∀ m ∈ f.support,
      (∀ k : ℕ, (∑ a : Fin N with a.val < k, rowDeg m a) ≤ ∑ t : Fin N with t.val < k, ν t) ∧
      ∑ a : Fin N, rowDeg m a = ∑ t : Fin N, ν t := by
  classical
  rw [standardMonomialSpanDomain O N N ν] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hx
    intro m hm
    have h := bideterminantDominance O N N K sz hsz I m hm
    rw [hshape] at h
    exact h
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.mp (support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx =>
    intro m hm
    exact hx m (support_smul hm)

theorem rename_rowPerm_mem (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (σ : Equiv.Perm (Fin N))
    (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ dualWeyl O N N ν) :
    rename (fun v : Fin N × Fin N => (σ v.1, v.2)) f ∈ dualWeyl O N N ν := by
  classical
  have h : (rename (fun v : Fin N × Fin N => (σ v.1, v.2)) : MvPolynomial (Fin N × Fin N) O →ₐ[O] _) =
      rowAct O (Matrix.of fun a b : Fin N => if σ a = b then (1 : O) else 0) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [rowAct]
  rw [h]
  exact dualWeylRowStable O N N ν _ f hf

theorem weight_rowW_eq_rowDeg {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    Finsupp.weight (rowW N N) m a = rowDeg m a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp [rowW, rowDeg]
  · intro b _ hb
    simp [rowW, Ne.symm hb]
  · simp

end GlobalTheory.HighWt

namespace GlobalTheory.HighWt

open MvPolynomial Formalism.GradedWeylDivisibility

theorem sum_fin_lt_one {N : ℕ} (h : 0 < N) (g : Fin N → ℕ) : ∑ b : Fin N with b.val < 1, g b = g ⟨0, h⟩ := by
  rw [Finset.sum_eq_single_of_mem (⟨0, h⟩ : Fin N) (by simp)]
  intro b hb hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  exact absurd (Fin.ext (by simp; omega)) hne

theorem sum_fin_split_last {N : ℕ} (h : 0 < N) (g : Fin N → ℕ) :
    ∑ b : Fin N, g b = ∑ b : Fin N with b.val < N - 1, g b + g ⟨N - 1, by omega⟩ := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun b : Fin N => b.val < N - 1)]
  congr 1
  rw [Finset.sum_eq_single_of_mem (⟨N - 1, by omega⟩ : Fin N) (by simp; omega)]
  intro b hb hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hb
  exact absurd (Fin.ext (by simp; omega)) hne

theorem jointWt_bounds : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] (lam : ι → ℕ → ℕ), (∀ τ, Antitone (res N (lam τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm]
    (w : ι → Fin N → ℕ), GlobalTheory.HighWt.JointWt O N lam Gm w → ∀ τ, ∑ a : Fin N, w τ a = ∑ a : Fin N, lam τ a ∧
      ∀ a : Fin N, lam τ (N - 1) ≤ w τ a ∧ w τ a ≤ lam τ 0 := by
  intro O _ _ _ _ N ι _ _ lam _ Gm _ _ w hw τ
  classical
  obtain ⟨z, hz0, hz⟩ := hw
  obtain ⟨a0, ha0, -⟩ := GlobalTheory.ExpFrame.exists_unique_isProj O N ι lam τ (w τ)
  have hmem : a0 ∈ alg O N lam := Algebra.subset_adjoin (Or.inr ⟨τ, w τ, ha0⟩)
  have hex : ∃ x : ∀ τ, dualWeyl O N N (res N (lam τ)),
      weightedHomogeneousComponent (rowW N N) (w τ) (x τ : MvPolynomial (Fin N × Fin N) O) ≠ 0 := by
    by_contra hne
    push_neg at hne
    have ha0z : a0 = 0 := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro x
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.zero_apply]
      rw [ha0 x 0 (by simp [hne x])]
      exact MultilinearMap.map_coord_zero _ τ (by simp)
    have h1 := hz τ ⟨a0, hmem⟩ ha0
    have h0 : (⟨a0, hmem⟩ : alg O N lam) = 0 := Subtype.ext ha0z
    rw [h0, zero_smul] at h1
    exact hz0 h1.symm
  obtain ⟨x, hx⟩ := hex
  set f := weightedHomogeneousComponent (rowW N N) (w τ) (x τ : MvPolynomial (Fin N × Fin N) O) with hfdef
  have hfmem : f ∈ dualWeyl O N N (res N (lam τ)) := dualWeylRowGraded O N N _ _ _ (x τ).2
  have hfhom : IsWeightedHomogeneous (rowW N N) f (w τ) := weightedHomogeneousComponent_isWeightedHomogeneous _ _
  obtain ⟨m, hm⟩ := support_nonempty.2 hx
  have hrd : ∀ a, rowDeg m a = w τ a := fun a => by
    rw [← weight_rowW_eq_rowDeg, hfhom (mem_support_iff.1 hm)]
  have key : ∀ σ : Equiv.Perm (Fin N),
      (∀ k : ℕ, (∑ b : Fin N with b.val < k, w τ (σ.symm b)) ≤ ∑ t : Fin N with t.val < k, res N (lam τ) t) ∧
      ∑ b : Fin N, w τ (σ.symm b) = ∑ t : Fin N, res N (lam τ) t := by
    intro σ
    let e : Fin N × Fin N → Fin N × Fin N := fun v => (σ v.1, v.2)
    have he : Function.Injective e := by
      intro u v huv
      simp only [e, Prod.mk.injEq] at huv
      exact Prod.ext (σ.injective huv.1) huv.2
    have hm' : m.mapDomain e ∈ (rename e f).support := by
      rw [mem_support_iff, coeff_rename_mapDomain e he]
      exact mem_support_iff.1 hm
    have hrd' : ∀ b, rowDeg (m.mapDomain e) b = w τ (σ.symm b) := by
      intro b
      rw [← hrd]
      unfold rowDeg
      refine Finset.sum_congr rfl fun s _ => ?_
      have : (b, s) = e (σ.symm b, s) := by simp [e]
      rw [this, Finsupp.mapDomain_apply he]
    have hd := dualWeyl_rowDeg_dominance O N _ _ (rename_rowPerm_mem O N _ σ f hfmem) _ hm'
    simp only [hrd'] at hd
    exact hd
  have hres : ∀ t : Fin N, res N (lam τ) t = lam τ t := fun t => rfl
  refine ⟨?_, fun a => ⟨?_, ?_⟩⟩
  · have h := (key (Equiv.refl _)).2
    simpa [hres] using h
  · have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) a.isLt
    obtain ⟨h1, h2⟩ := key (Equiv.swap ⟨N - 1, by omega⟩ a)
    have h3 := h1 (N - 1)
    rw [sum_fin_split_last hN, sum_fin_split_last hN] at h2
    have h4 : w τ ((Equiv.swap ⟨N - 1, by omega⟩ a).symm ⟨N - 1, by omega⟩) = w τ a := by simp
    rw [h4] at h2
    have h5 : res N (lam τ) ⟨N - 1, by omega⟩ = lam τ (N - 1) := rfl
    rw [h5] at h2
    omega
  · have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) a.isLt
    have h1 := (key (Equiv.swap ⟨0, hN⟩ a)).1 1
    rw [sum_fin_lt_one hN, sum_fin_lt_one hN] at h1
    have h2 : w τ a ≤ res N (lam τ) ⟨0, hN⟩ := by simpa using h1
    exact h2

end GlobalTheory.HighWt
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jointRowWeight_bounds_dualWeylModule : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ), (∀ τ, Antitone (res N (lam τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm] (w : ι → Fin N → ℕ), GlobalTheory.HighWt.JointWt O N lam Gm w → ∀ τ, ∑ a : Fin N, w τ a = ∑ a : Fin N, lam τ a ∧ ∀ a : Fin N, lam τ (N - 1) ≤ w τ a ∧ w τ a ≤ lam τ 0 := by
  atlas_forward_decl GlobalTheory.HighWt.jointWt_bounds
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jointRowWeight_antitone_of_maxPotential : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm] (w : ι → Fin N → ℕ), GlobalTheory.HighWt.JointWt O N lam Gm w → (∀ w' : ι → Fin N → ℕ, GlobalTheory.HighWt.JointWt O N lam Gm w' → GlobalTheory.HighWt.pot N w' ≤ GlobalTheory.HighWt.pot N w) → ∀ τ, Antitone (w τ) := by
  first | exact @GlobalTheory.HighWt.antitone_of_pot_max | exact GlobalTheory.HighWt.antitone_of_pot_max | (intros; apply GlobalTheory.HighWt.antitone_of_pot_max <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open MvPolynomial
open Formalism.GradedWeylDivisibility

namespace GlobalTheory.HighWt

theorem map_bidet {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    MvPolynomial.map φ (bideterminant R sz hsz I) = bideterminant S sz hsz I := by
  unfold bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp [RingHom.mapMatrix_apply]

theorem baseChange_holds : BaseChange := by
  intro O _ _ _ ϖ hϖ N ν _
  have hmax : (Ideal.span {ϖ}).IsMaximal := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
    exact IsLocalRing.maximalIdeal.isMaximal O
  letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  have hdom : IsDomain (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.isDomain _
  constructor
  · intro f hf
    rw [standardMonomialSpanDomain (O ⧸ Ideal.span {ϖ}) N N ν] at hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨K, sz, hsz, I, hsh, rfl⟩ := hx
      refine ⟨bideterminant O sz hsz I, ?_, map_bidet _ sz hsz I⟩
      rw [← hsh]
      exact bidetMem O N N K sz hsz I
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a + b, Submodule.add_mem _ ha hb, by simp⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
      refine ⟨c' • a, Submodule.smul_mem _ c' ha, ?_⟩
      rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]
  · intro g hg h0
    have hk : g ∈ RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ}))) := h0
    rw [MvPolynomial.ker_map, Ideal.mk_ker, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton'] at hk
    obtain ⟨h, hh⟩ := hk
    have hgh : g = ϖ • h := by rw [smul_eq_C_mul, ← hh, mul_comm]
    refine ⟨h, ?_, hgh⟩
    exact dualWeylSat O N N ν ϖ h hϖ.ne_zero (hgh ▸ hg)

end GlobalTheory.HighWt

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_weight_base_change : GlobalTheory.HighWt.BaseChange := by
  atlas_forward_decl GlobalTheory.HighWt.baseChange_holds
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HighWtEmb

theorem exists_basis_reduction_linearIndependent : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → GlobalTheory.HighWt.BaseChange →
    ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ∃ (n : ℕ) (b : Module.Basis (Fin n) O (dualWeyl O N N ν)),
      LinearIndependent (O ⧸ Ideal.span {ϖ})
        (fun i => MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (b i : MvPolynomial (Fin N × Fin N) O)) := by
  intro O _ _ _ ϖ hϖ hBC N ν hν
  haveI := GlobalTheory.NablaFin.dualWeyl_finite O N ν
  haveI : Module.Free O (dualWeyl O N N ν) := Module.free_of_finite_type_torsion_free'
  let b := (Module.Free.chooseBasis O (dualWeyl O N N ν)).reindex (Fintype.equivFin _)
  refine ⟨_, b, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  choose c hc using fun j => Ideal.Quotient.mk_surjective (I := Ideal.span {ϖ}) (a j)
  let g : dualWeyl O N N ν := ∑ j, c j • b j
  have hg : MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (g : MvPolynomial (Fin N × Fin N) O) = 0 := by
    rw [← ha]
    simp only [g, Submodule.coe_sum, Submodule.coe_smul, map_sum, MvPolynomial.smul_eq_C_mul, map_mul, map_C, hc]
  obtain ⟨h, hh, hgh⟩ := (hBC O ϖ hϖ N ν hν).2 g g.2 hg
  have hgh' : g = ϖ • (⟨h, hh⟩ : dualWeyl O N N ν) := Subtype.ext (by simpa using hgh)
  have hci : c i = ϖ * b.repr ⟨h, hh⟩ i := by
    have h2 := congrArg (fun x => b.repr x i) hgh'
    simp only [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul] at h2
    rw [← h2]
    simp [g, map_sum, Finsupp.single_apply]
  rw [← hc i, hci, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ϖ), zero_mul]

theorem exists_dual_family (k : Type) [Field k] (σ : Type) (κ : Type) [DecidableEq κ] (v : κ → MvPolynomial σ k)
    (hv : LinearIndependent k v) : ∃ ψ : κ → (MvPolynomial σ k →ₗ[k] k), ∀ i l, ψ l (v i) = if i = l then 1 else 0 := by
  let B := Module.Basis.span hv
  refine ⟨fun l => (LinearMap.exists_extend (B.coord l)).choose, fun i l => ?_⟩
  have h := (LinearMap.exists_extend (B.coord l)).choose_spec
  have hvi : v i ∈ Submodule.span k (Set.range v) := Submodule.subset_span ⟨i, rfl⟩
  have h1 := LinearMap.congr_fun h ⟨v i, hvi⟩
  have hBi : B i = ⟨v i, hvi⟩ := Module.Basis.span_apply hv i
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h1
  rw [h1, ← hBi, B.coord_apply, B.repr_self, Finsupp.single_apply]

theorem curry_sum_mapDomain {ι σ : Type} [Fintype ι] [DecidableEq ι] (F : ι → σ →₀ ℕ) (τ : ι) :
    (∑ ρ, Finsupp.mapDomain (fun s : σ => ((ρ, s) : ι × σ)) (F ρ)).curry τ = F τ := by
  classical
  ext s
  rw [Finsupp.curry_apply, Finsupp.coe_finset_sum, Finset.sum_apply, Finset.sum_eq_single τ]
  · exact Finsupp.mapDomain_apply (fun _ _ h => congrArg Prod.snd h) _ _
  · intro ρ _ hρ
    apply Finsupp.mapDomain_notin_range
    rintro ⟨t, ht⟩
    exact hρ (congrArg Prod.fst ht)
  · simp

theorem exists_prod_functional : ∀ (k : Type) [CommRing k] (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type)
    (φ : ι → (MvPolynomial σ k →ₗ[k] k)), ∃ Φ : MvPolynomial (ι × σ) k →ₗ[k] k,
      ∀ f : ι → MvPolynomial σ k, Φ (∏ τ, rename (fun s : σ => ((τ, s) : ι × σ)) (f τ)) = ∏ τ, φ τ (f τ) := by
  intro k _ ι _ _ σ φ
  classical
  let w : ((ι × σ) →₀ ℕ) → k := fun M => ∏ τ, φ τ (monomial (M.curry τ) 1)
  let Φ := (MvPolynomial.basisMonomials (ι × σ) k).constr k w
  have hmono : ∀ M c, Φ (monomial M c) = c * w M := by
    intro M c
    have : (monomial M c : MvPolynomial (ι × σ) k) = c • (MvPolynomial.basisMonomials (ι × σ) k M) := by
      rw [MvPolynomial.coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
    rw [this, map_smul, Module.Basis.constr_basis, smul_eq_mul]
  have hφ : ∀ τ m c, φ τ (monomial m c) = c * φ τ (monomial m 1) := by
    intro τ m c
    rw [← smul_eq_mul, ← map_smul, smul_monomial, smul_eq_mul, mul_one]
  refine ⟨Φ, fun f => ?_⟩
  have h1 : ∀ τ, rename (fun s : σ => ((τ, s) : ι × σ)) (f τ) =
      ∑ m ∈ (f τ).support, monomial (Finsupp.mapDomain (fun s : σ => ((τ, s) : ι × σ)) m) (coeff m (f τ)) := by
    intro τ
    conv_lhs => rw [as_sum (f τ)]
    simp only [map_sum, rename_monomial]
  have h2 : ∀ τ, φ τ (f τ) = ∑ m ∈ (f τ).support, coeff m (f τ) * φ τ (monomial m 1) := by
    intro τ
    conv_lhs => rw [as_sum (f τ)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => hφ τ m _
  rw [Finset.prod_congr rfl (fun τ _ => h1 τ), Finset.prod_congr rfl (fun τ _ => h2 τ), Finset.prod_univ_sum,
    Finset.prod_univ_sum, map_sum]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [← monomial_sum_prod, hmono]
  simp only [w, curry_sum_mapDomain, Finset.prod_mul_distrib]

theorem linearIndependent_prod_rename : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) (κ : ι → Type) [∀ τ, Fintype (κ τ)]
    (v : ∀ τ, κ τ → MvPolynomial σ k), (∀ τ, LinearIndependent k (v τ)) →
    LinearIndependent k (fun p : (∀ τ, κ τ) => ∏ τ, rename (fun s : σ => ((τ, s) : ι × σ)) (v τ (p τ))) := by
  intro k _ ι _ _ σ κ _ v hv
  classical
  choose ψ hψ using fun τ => exists_dual_family k σ (κ τ) (v τ) (hv τ)
  rw [Fintype.linearIndependent_iff]
  intro a ha l
  obtain ⟨Φ, hΦ⟩ := exists_prod_functional k ι σ (fun τ => ψ τ (l τ))
  have h := congrArg Φ ha
  rw [map_sum, map_zero] at h
  simp only [map_smul, hΦ, hψ, smul_eq_mul] at h
  rw [Finset.sum_eq_single l] at h
  · simpa using h
  · intro p _ hp
    obtain ⟨τ, hτ⟩ : ∃ τ, p τ ≠ l τ := by
      by_contra hc
      push_neg at hc
      exact hp (funext hc)
    rw [Finset.prod_eq_zero (Finset.mem_univ τ) (if_neg hτ), mul_zero]
  · simp

theorem blockRed_eq (O : Type) [CommRing O] (N : ℕ) {ι : Type} (ϖ : O) (τ : ι) (g : MvPolynomial (Fin N × Fin N) O) :
    blockRed O N ϖ τ g = rename (fun s : Fin N × Fin N => ((τ, s) : BVar N ι)) (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [blockRed, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp [hp, hq]
  | mul_X p s hp => simp [hp, blockRed] at *

theorem mem_smul_top_of_redT_eq_zero : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (mu : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (mu τ))) → GlobalTheory.HighWt.BaseChange →
    ∀ y : NablaT O N mu, redT O N mu ϖ y = 0 → y ∈ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N mu)) := by
  intro O _ _ _ N ι _ _ mu ϖ hϖ hanti hBC y hy
  haveI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  have hb := fun τ => exists_basis_reduction_linearIndependent O ϖ hϖ hBC N (res N (mu τ)) (hanti τ)
  choose n b hli using hb
  let B := Basis.piTensorProduct b
  have hred : ∀ p, redT O N mu ϖ (B p) = ∏ τ, rename (fun s : Fin N × Fin N => ((τ, s) : BVar N ι))
      (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (b τ (p τ) : MvPolynomial (Fin N × Fin N) O)) := by
    intro p
    simp only [B, Basis.piTensorProduct_apply, redT, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, AlgHom.toLinearMap_apply]
    exact Finset.prod_congr rfl fun τ _ => blockRed_eq O N ϖ τ _
  have hL := linearIndependent_prod_rename (O ⧸ Ideal.span {ϖ}) ι (Fin N × Fin N) (fun τ => Fin (n τ))
    (fun τ i => MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (b τ i : MvPolynomial (Fin N × Fin N) O)) hli
  rw [Fintype.linearIndependent_iff] at hL
  have hy' : ∑ p, Ideal.Quotient.mk (Ideal.span {ϖ}) (B.repr y p) • ∏ τ, rename (fun s : Fin N × Fin N => ((τ, s) : BVar N ι))
      (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (b τ (p τ) : MvPolynomial (Fin N × Fin N) O)) = 0 := by
    rw [← hy]
    conv_rhs => rw [← B.sum_repr y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [LinearMap.map_smul, hred]
    exact algebraMap_smul (O ⧸ Ideal.span {ϖ}) (B.repr y p) _
  have hc := hL _ hy'
  rw [← B.sum_repr y]
  refine Submodule.sum_mem _ fun p _ => ?_
  have hp : B.repr y p ∈ Ideal.span {ϖ} := Ideal.Quotient.eq_zero_iff_mem.mp (hc p)
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hp
  rw [← hd, mul_comm, mul_smul]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ϖ) Submodule.mem_top

end GlobalTheory.HighWtEmb

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_smul_top_of_dualWeylTensorReduction_eq_zero : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (mu τ))) → GlobalTheory.HighWt.BaseChange → ∀ y : NablaT O N mu, redT O N mu ϖ y = 0 → y ∈ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N mu)) := by
  atlas_forward_decl GlobalTheory.HighWtEmb.mem_smul_top_of_redT_eq_zero
end

section
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

namespace GlobalTheory.HighWtEmb

theorem blockRed_eq_rename (O : Type) [CommRing O] (N : ℕ) {ι : Type} (ϖ : O) (τ : ι)
    (g : MvPolynomial (Fin N × Fin N) O) :
    blockRed O N ϖ τ g = rename (fun v : Fin N × Fin N => ((τ, v) : BVar N ι))
      (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [blockRed, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp => simp only [map_mul, hp, blockRed, aeval_X, map_X, rename_X] at hp ⊢

theorem redT_tprod (O : Type) [CommRing O] (N : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O)
    (x : ∀ τ, dualWeyl O N N (res N (mu τ))) :
    redT O N mu ϖ (PiTensorProduct.tprod O x) =
      ∏ τ, rename (fun v : Fin N × Fin N => ((τ, v) : BVar N ι))
        (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (x τ : MvPolynomial (Fin N × Fin N) O)) := by
  unfold redT
  rw [PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply]
  exact blockRed_eq_rename O N ϖ τ _

end GlobalTheory.HighWtEmb

namespace GlobalTheory.HighWtEmb

theorem nabK_lift : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (mu : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (mu τ))) → GlobalTheory.HighWt.BaseChange →
    ∀ P ∈ nabK (O ⧸ Ideal.span {ϖ}) N (fun τ => res N (mu τ)), ∃ y : NablaT O N mu, redT O N mu ϖ y = P := by
  intro O _ _ _ N ι _ _ mu ϖ hϖ hanti hBC P hP
  unfold nabK at hP
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨f, hf, rfl⟩ := hP
    have hl : ∀ τ, ∃ g ∈ dualWeyl O N N (res N (mu τ)),
        MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) g = f τ :=
      fun τ => (hBC O ϖ hϖ N (res N (mu τ)) (hanti τ)).1 (f τ) (hf τ)
    choose g hg hgf using hl
    refine ⟨PiTensorProduct.tprod O (fun τ => (⟨g τ, hg τ⟩ : dualWeyl O N N (res N (mu τ)))), ?_⟩
    rw [redT_tprod]
    exact Finset.prod_congr rfl fun τ _ => by rw [hgf τ]
  | zero => exact ⟨0, map_zero _⟩
  | add P Q _ _ hP hQ =>
    obtain ⟨y, rfl⟩ := hP
    obtain ⟨z, rfl⟩ := hQ
    exact ⟨y + z, map_add _ _ _⟩
  | smul c P _ hP =>
    obtain ⟨y, rfl⟩ := hP
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨c • y, ?_⟩
    rw [LinearMap.map_smul, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]

end GlobalTheory.HighWtEmb
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_dualWeylTensorReduction : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (mu τ))) → GlobalTheory.HighWt.BaseChange → ∀ P ∈ nabK (O ⧸ Ideal.span {ϖ}) N (fun τ => res N (mu τ)), ∃ y : NablaT O N mu, redT O N mu ϖ y = P := by
  atlas_forward_decl GlobalTheory.HighWtEmb.nabK_lift
end

section
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

namespace GlobalTheory.HighWtEmb

theorem blockRed_rowAct (O : Type) [CommRing O] (N : ℕ) {ι : Type} (ϖ : O) (τ : ι)
    (A : ι → Matrix (Fin N) (Fin N) (O ⧸ Ideal.span {ϖ})) (M : Matrix (Fin N) (Fin N) O)
    (hA : A τ = M.map (Ideal.Quotient.mk (Ideal.span {ϖ}))) (f : MvPolynomial (Fin N × Fin N) O) :
    blockRed O N ϖ τ (rowAct O M f) = blockSub (O ⧸ Ideal.span {ϖ}) N A (blockRed O N ϖ τ f) := by
  have h : (blockRed O N ϖ τ).comp (rowAct O M) =
      ((blockSub (O ⧸ Ideal.span {ϖ}) N A).restrictScalars O).comp (blockRed O N ϖ τ) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, rowAct, blockRed, blockSub, aeval_X, map_sum, map_mul,
      hA, Matrix.map_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    rw [aeval_C]
    rfl
  exact congrArg (fun φ => φ f) h

end GlobalTheory.HighWtEmb

theorem GlobalTheory.HighWtEmb.redT_grp : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O) (g : ι → GL (Fin N) O) (y : NablaT O N mu), redT O N mu ϖ (grp O N mu g y) = blockSub (O ⧸ Ideal.span {ϖ}) N (fun τ => (((g τ)⁻¹ : GL (Fin N) O) : Matrix (Fin N) (Fin N) O).map (Ideal.Quotient.mk (Ideal.span {ϖ}))) (redT O N mu ϖ y) := by
  intro O _ N ι _ _ mu ϖ g y
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul]
    have h1 := (Formalism.CohomologicalDescent.RealLocalDeltaNabla.nabla_rep_tensor_product O ι (fun _ => N) (fun _ => N) (fun τ => res N (mu τ)) g m)
    simp only [GlobalTheory.ExpFrame.grp]
    rw [h1.1]
    simp only [redT, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
      LinearMap.comp_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply]
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_prod, IsScalarTower.algebraMap_apply O (O ⧸ Ideal.span {ϖ}), AlgHom.commutes]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [h1.2 τ]
    exact blockRed_rowAct O N ϖ τ _ _ rfl _
  | add a b ha hb => simp only [map_add, ha, hb]

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylTensorReduction_intertwines_group_action : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O) (g : ι → GL (Fin N) O) (y : NablaT O N mu), redT O N mu ϖ (grp O N mu g y) = blockSub (O ⧸ Ideal.span {ϖ}) N (fun τ => (((g τ)⁻¹ : GL (Fin N) O) : Matrix (Fin N) (Fin N) O).map (Ideal.Quotient.mk (Ideal.span {ϖ}))) (redT O N mu ϖ y) := by
  atlas_forward_decl GlobalTheory.HighWtEmb.redT_grp
end

section
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

namespace GlobalTheory.HighWtEmb

theorem wComp_monomial_eq_ite {σ R M : Type} [CommSemiring R] [AddCommMonoid M] [DecidableEq M] (w : σ → M) (n : M) (d : σ →₀ ℕ) (c : R) :
    weightedHomogeneousComponent w n (monomial d c) = if Finsupp.weight w d = n then monomial d c else 0 := by
  classical
  ext m
  rw [coeff_weightedHomogeneousComponent, coeff_monomial]
  by_cases h : Finsupp.weight w d = n <;> by_cases hd : d = m
  · subst hd; simp [h]
  · simp [h, hd, coeff_monomial]
  · subst hd; simp [h]
  · simp [h, hd]

theorem wComp_mul_of_weight_zero {σ R M : Type} [CommSemiring R] [AddCommMonoid M] (w : σ → M) (n : M) (P Q : MvPolynomial σ R)
    (hQ : IsWeightedHomogeneous w Q 0) :
    weightedHomogeneousComponent w n (P * Q) = weightedHomogeneousComponent w n P * Q := by
  classical
  ext m
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  split_ifs with h
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases hq : coeff x.2 Q = 0
    · simp [hq]
    · have h2 := hQ hq
      have hm : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      have e : Finsupp.weight w x.1 = n := by rw [← h, ← hm, map_add, h2, add_zero]
      rw [if_pos e]
  · symm
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases hq : coeff x.2 Q = 0
    · simp [hq]
    · have h2 := hQ hq
      have hm : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      have e : Finsupp.weight w x.1 ≠ n := by rw [← hm, map_add, h2, add_zero] at h; exact h
      rw [if_neg e, zero_mul]

theorem blockRed_eq_rename_map (O : Type) [CommRing O] (N : ℕ) {ι : Type} (ϖ : O) (τ : ι) (f : MvPolynomial (Fin N × Fin N) O) :
    blockRed O N ϖ τ f = rename (fun v => ((τ, v) : BVar N ι)) (map (Ideal.Quotient.mk (Ideal.span {ϖ})) f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [blockRed, MvPolynomial.algebraMap_eq]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p v hp => rw [map_mul, hp]; simp [blockRed]

theorem weight_blockW_mapDomain_self (N : ℕ) {ι : Type} [DecidableEq ι] (τ : ι) (d : Fin N × Fin N →₀ ℕ) :
    Finsupp.weight (blockW N τ) (Finsupp.mapDomain (fun v => ((τ, v) : BVar N ι)) d) = Finsupp.weight (rowW N N) d := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i c => c • blockW N τ i) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  simp [blockW, rowW]

theorem weight_blockW_mapDomain_of_ne (N : ℕ) {ι : Type} [DecidableEq ι] {τ σ : ι} (h : σ ≠ τ) (d : Fin N × Fin N →₀ ℕ) :
    Finsupp.weight (blockW N τ) (Finsupp.mapDomain (fun v => ((σ, v) : BVar N ι)) d) = 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i c => c • blockW N τ i) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  simp [blockW, h]

end GlobalTheory.HighWtEmb

namespace GlobalTheory.HighWtEmb

theorem blockRed_wComp_rowW (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (ϖ : O) (τ : ι) (v : Fin N → ℕ)
    (f : MvPolynomial (Fin N × Fin N) O) :
    blockRed O N ϖ τ (weightedHomogeneousComponent (rowW N N) v f) =
      weightedHomogeneousComponent (blockW N τ) v (blockRed O N ϖ τ f) := by
  classical
  conv_rhs => rw [f.as_sum]
  rw [weightedHomogeneousComponent_apply, map_sum, map_sum, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [blockRed_eq_rename_map, map_monomial, rename_monomial]
  rw [wComp_monomial_eq_ite, weight_blockW_mapDomain_self]

theorem blockRed_isWeightedHomogeneous_zero (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (ϖ : O) {τ σ : ι} (h : σ ≠ τ)
    (f : MvPolynomial (Fin N × Fin N) O) : IsWeightedHomogeneous (blockW N τ) (blockRed O N ϖ σ f) 0 := by
  rw [blockRed_eq_rename_map, f.as_sum, map_sum, map_sum, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun d _ => ?_
  rw [mem_weightedHomogeneousSubmodule, map_monomial, rename_monomial]
  exact isWeightedHomogeneous_monomial _ _ _ (weight_blockW_mapDomain_of_ne N h d)

theorem redT_tprod_prod_blockRed (O : Type) [CommRing O] (N : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O)
    (x : ∀ τ, dualWeyl O N N (res N (mu τ))) :
    redT O N mu ϖ (PiTensorProduct.tprod O x) = ∏ σ, blockRed O N ϖ σ (x σ) := by
  simp [redT]

theorem redT_isProj : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O) (τ : ι) (v : Fin N → ℕ) (a : Module.End O (NablaT O N mu)), IsProj O N mu τ v a → ∀ y : NablaT O N mu, redT O N mu ϖ (a y) = weightedHomogeneousComponent (blockW N τ) v (redT O N mu ϖ y) := by
  intro O _ N ι _ _ mu ϖ τ v a ha y
  have key : (redT O N mu ϖ).comp a =
      ((weightedHomogeneousComponent (blockW N τ) v).restrictScalars O).comp (redT O N mu ϖ) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
    let yy : dualWeyl O N N (res N (mu τ)) := rowProj O N (res N (mu τ)) v (x τ)
    have hQ : IsWeightedHomogeneous (blockW N τ) (∏ σ ∈ ({τ}ᶜ : Finset ι), blockRed O N ϖ σ (x σ)) 0 := by
      have := IsWeightedHomogeneous.prod ({τ}ᶜ : Finset ι) (fun σ => blockRed O N ϖ σ (x σ)) (fun _ => (0 : Fin N → ℕ))
        (fun σ hσ => blockRed_isWeightedHomogeneous_zero O N ϖ (by simpa using hσ) (x σ))
      simpa using this
    rw [ha x yy rfl, redT_tprod_prod_blockRed, redT_tprod_prod_blockRed, Fintype.prod_eq_mul_prod_compl τ, Fintype.prod_eq_mul_prod_compl τ,
      Function.update_self, wComp_mul_of_weight_zero _ _ _ _ hQ]
    congr 1
    · show blockRed O N ϖ τ (weightedHomogeneousComponent (rowW N N) v (x τ : MvPolynomial (Fin N × Fin N) O)) = _
      exact blockRed_wComp_rowW O N ϖ τ v _
    · refine Finset.prod_congr rfl fun σ hσ => ?_
      rw [Function.update_of_ne (by simpa using hσ)]
  exact LinearMap.congr_fun key y

end GlobalTheory.HighWtEmb
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylTensorReduction_weightProjector : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O) (τ : ι) (v : Fin N → ℕ) (a : Module.End O (NablaT O N mu)), IsProj O N mu τ v a → ∀ y : NablaT O N mu, redT O N mu ϖ (a y) = weightedHomogeneousComponent (blockW N τ) v (redT O N mu ϖ y) := by
  atlas_forward_decl GlobalTheory.HighWtEmb.redT_isProj
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HighWtEmb.NabInter

variable {k : Type} [Field k]

def mr {σ A B : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (L : A →ₗ[k] B)
    (F : MvPolynomial σ A) : MvPolynomial σ B :=
  ∑ m ∈ F.support, monomial m (L (coeff m F))

section
variable {σ A B : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (L : A →ₗ[k] B)

theorem coeff_mr (F : MvPolynomial σ A) (m : σ →₀ ℕ) : coeff m (mr L F) = L (coeff m F) := by
  classical
  simp only [mr, coeff_sum, coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h, map_zero]

theorem mr_add (F G : MvPolynomial σ A) : mr L (F + G) = mr L F + mr L G := by
  ext m; simp [coeff_mr]

theorem mr_smul (c : k) (F : MvPolynomial σ A) : mr L (c • F) = c • mr L F := by
  ext m; simp [coeff_mr, coeff_smul]

theorem mr_monomial (m : σ →₀ ℕ) (a : A) : mr L (monomial m a) = monomial m (L a) := by
  classical
  ext n; simp only [coeff_mr, coeff_monomial]; split_ifs <;> simp

theorem mr_C (a : A) : mr L (C a : MvPolynomial σ A) = C (L a) := mr_monomial L 0 a

theorem mr_map_mul (q : MvPolynomial σ k) (F : MvPolynomial σ A) :
    mr L (map (algebraMap k A) q * F) = map (algebraMap k B) q * mr L F := by
  classical
  ext n
  simp only [coeff_mr, coeff_mul, coeff_map, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Algebra.smul_def (coeff x.1 q) (coeff x.2 F), LinearMap.map_smul, Algebra.smul_def]
end

theorem mr_C_mul_map {σ A : Type} [CommRing A] [Algebra k A] (L : A →ₗ[k] k) (c : A) (h : MvPolynomial σ k) :
    mr L (C c * map (algebraMap k A) h) = L c • h := by
  ext n
  simp only [coeff_mr, coeff_C_mul, coeff_map, coeff_smul, smul_eq_mul]
  rw [← Algebra.commutes, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul, mul_comm]

theorem commAlgEquiv_monomial_one {S₁ S₂ : Type} (m' : S₁ →₀ ℕ) :
    commAlgEquiv k S₁ S₂ (monomial m' 1) = C (monomial m' 1) := by
  rw [monomial_eq, monomial_eq, C_1, C_1, one_mul, one_mul]
  simp only [Finsupp.prod, map_prod, map_pow, commAlgEquiv_X]

theorem coeff_coeff_commAlgEquiv {S₁ S₂ : Type} (F : MvPolynomial S₁ (MvPolynomial S₂ k)) (β : S₂ →₀ ℕ) (m : S₁ →₀ ℕ) :
    coeff m (coeff β (commAlgEquiv k S₁ S₂ F)) = coeff β (coeff m F) := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial m' a =>
    have : (monomial m' a : MvPolynomial S₁ (MvPolynomial S₂ k)) = C a * monomial m' 1 := by
      rw [C_mul_monomial, mul_one]
    rw [this, map_mul, commAlgEquiv_C, commAlgEquiv_monomial_one, mul_comm, coeff_C_mul, coeff_map,
      ← this, coeff_monomial]
    rw [mul_comm, C_mul_monomial, mul_one, coeff_monomial]
    split_ifs <;> simp
  | add p q hp hq => simp [hp, hq]

end GlobalTheory.HighWtEmb.NabInter

namespace GlobalTheory.HighWtEmb.NabInter
variable {k : Type} [Field k]

theorem mr_aeval {σ τ' A : Type} [CommRing A] [Algebra k A] (L : A →ₗ[k] k) (g : σ → MvPolynomial τ' k)
    (F : MvPolynomial σ A) :
    mr L (aeval (fun v => map (algebraMap k A) (g v)) F) = aeval g (mr L F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial u a =>
    have h1 : aeval (fun v => map (algebraMap k A) (g v)) (monomial u (1 : A)) =
        map (algebraMap k A) (aeval g (monomial u (1 : k))) := by
      simp only [aeval_monomial, Finsupp.prod, map_prod, map_pow, map_one, one_mul, map_mul, map_X]
    have h2 : (monomial u a : MvPolynomial σ A) = C a * monomial u 1 := by rw [C_mul_monomial, mul_one]
    rw [h2, map_mul, aeval_C, h1, algebraMap_eq, mr_C_mul_map, ← h2, mr_monomial,
      show (monomial u (L a) : MvPolynomial σ k) = L a • monomial u 1 by rw [smul_monomial, smul_eq_mul, mul_one],
      map_smul]
  | add p q hp hq => rw [map_add, mr_add, hp, hq, mr_add, map_add]

theorem colAddGen_eq_aeval (A : Type) [CommRing A] [Algebra k A] {r n : ℕ} (l j : Fin n) :
    colAddGen A (r := r) l j = aeval (fun v => map (algebraMap k A)
      ((if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v) :
        MvPolynomial (Option (Fin r × Fin n)) k))) := by
  unfold colAddGen
  congr 1
  funext v
  split_ifs <;> simp

theorem rename_some_eq_aeval (A : Type) [CommRing A] [Algebra k A] {r n : ℕ} :
    (rename (R := A) (some : Fin r × Fin n → Option (Fin r × Fin n))) =
      aeval (fun v => map (algebraMap k A) (X (some v) : MvPolynomial (Option (Fin r × Fin n)) k)) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp

theorem dualWeyl_mr {A : Type} [CommRing A] [Algebra k A] (L : A →ₗ[k] k) (r n : ℕ) (ν : Fin n → ℕ)
    (F : MvPolynomial (Fin r × Fin n) A) (hF : F ∈ dualWeyl A r n ν) : mr L F ∈ dualWeyl k r n ν := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hF ⊢
  obtain ⟨h1, h2⟩ := hF
  refine ⟨?_, fun l j hlj => ?_⟩
  · intro d hd
    apply h1
    intro h0
    apply hd
    rw [coeff_mr, h0, map_zero]
  · have := congrArg (mr L) (h2 l j hlj)
    rw [colAddGen_eq_aeval (k := k), rename_some_eq_aeval (k := k), mr_aeval, mr_aeval] at this
    rw [colAddGen_eq_aeval (k := k), rename_some_eq_aeval (k := k)]
    simpa [Algebra.algebraMap_self, map_id] using this

end GlobalTheory.HighWtEmb.NabInter

namespace GlobalTheory.HighWtEmb.NabInter
variable {k : Type} [Field k]

theorem exists_proj {M : Type} [AddCommGroup M] [Module k M] (D : Submodule k M) :
    ∃ π : M →ₗ[k] M, (∀ f, π f ∈ D) ∧ ∀ f ∈ D, π f = f := by
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl D
  refine ⟨D.subtype ∘ₗ Submodule.projectionOnto D q hq, fun f => by simp, fun f hf => ?_⟩
  have := Submodule.projectionOnto_apply_left hq ⟨f, hf⟩
  simpa using congrArg Subtype.val this

def mrL {σ A B : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (L : A →ₗ[k] B) :
    MvPolynomial σ A →ₗ[k] MvPolynomial σ B where
  toFun := mr L
  map_add' := mr_add L
  map_smul' c F := by rw [mr_smul, RingHom.id_apply]

section
variable (N : ℕ) {ι : Type} [DecidableEq ι]

def splitEquiv (τ : ι) : BVar N ι ≃ OVar N τ ⊕ (Fin N × Fin N) where
  toFun p := if h : p.1 = τ then Sum.inr p.2 else Sum.inl ⟨p, h⟩
  invFun := Sum.elim Subtype.val (fun v => (τ, v))
  left_inv p := by
    obtain ⟨a, v⟩ := p
    by_cases h : a = τ
    · subst h; simp
    · simp [h]
  right_inv x := by
    rcases x with ⟨p, hp⟩ | v
    · simp [hp]
    · simp

def Ψ (τ : ι) :
    MvPolynomial (BVar N ι) k ≃ₐ[k] MvPolynomial (OVar N τ) (MvPolynomial (Fin N × Fin N) k) :=
  (renameEquiv k (splitEquiv N τ)).trans (sumAlgEquiv k _ _)

theorem Ψ_X_self (τ : ι) (v : Fin N × Fin N) : Ψ (k := k) N τ (X (τ, v)) = C (X v) := by
  simp [Ψ, splitEquiv]

theorem Ψ_X_ne (τ : ι) (p : BVar N ι) (h : p.1 ≠ τ) : Ψ (k := k) N τ (X p) = X ⟨p, h⟩ := by
  simp [Ψ, splitEquiv, h]

theorem Ψ_rename_self (τ : ι) (f : MvPolynomial (Fin N × Fin N) k) :
    Ψ N τ (rename (fun v : Fin N × Fin N => ((τ, v) : BVar N ι)) f) = C f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have := (Ψ (k := k) N τ).commutes a
    simpa [MvPolynomial.algebraMap_apply] using this
  | add p q hp hq => simp [hp, hq]
  | mul_X p v ih => simp [ih, Ψ_X_self]

theorem Ψ_rename_ne (τ σ : ι) (h : σ ≠ τ) (f : MvPolynomial (Fin N × Fin N) k) :
    Ψ N τ (rename (fun v : Fin N × Fin N => ((σ, v) : BVar N ι)) f) =
      map (algebraMap k (MvPolynomial (Fin N × Fin N) k))
        (rename (fun v : Fin N × Fin N => (⟨(σ, v), h⟩ : OVar N τ)) f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have := (Ψ (k := k) N τ).commutes a
    simpa [MvPolynomial.algebraMap_apply] using this
  | add p q hp hq => simp [hp, hq]
  | mul_X p v ih => simp [ih, Ψ_X_ne N τ (σ, v) h]

theorem Ψ_eq_toBlock (τ : ι) (P : MvPolynomial (BVar N ι) k) :
    Ψ N τ P = commAlgEquiv k (Fin N × Fin N) (OVar N τ) (toBlock k N τ P) := by
  have : (Ψ (k := k) N τ).toAlgHom = (commAlgEquiv k (Fin N × Fin N) (OVar N τ)).toAlgHom.comp (toBlock k N τ) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, v⟩
    by_cases h : a = τ
    · subst h; simp [toBlock, Ψ_X_self]
    · simp [toBlock, h, Ψ_X_ne N τ (a, v) h]
  exact congrArg (fun φ : MvPolynomial (BVar N ι) k →ₐ[k] _ => φ P) this

end

end GlobalTheory.HighWtEmb.NabInter

namespace GlobalTheory.HighWtEmb.NabInter
variable {k : Type} [Field k]

section
variable (N : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]

def E (τ : ι) (π : MvPolynomial (Fin N × Fin N) k →ₗ[k] MvPolynomial (Fin N × Fin N) k) :
    MvPolynomial (BVar N ι) k →ₗ[k] MvPolynomial (BVar N ι) k :=
  (Ψ N τ).symm.toLinearMap ∘ₗ mrL π ∘ₗ (Ψ N τ).toLinearMap

def gen (D : ι → Submodule k (MvPolynomial (Fin N × Fin N) k)) (T : Finset ι) :
    Set (MvPolynomial (BVar N ι) k) :=
  {Q | ∃ f : ι → MvPolynomial (Fin N × Fin N) k, (∀ σ ∈ T, f σ ∈ D σ) ∧
    Q = ∏ σ, rename (fun v : Fin N × Fin N => ((σ, v) : BVar N ι)) (f σ)}

theorem E_gen (D : ι → Submodule k (MvPolynomial (Fin N × Fin N) k)) (T : Finset ι) (τ : ι)
    (π : MvPolynomial (Fin N × Fin N) k →ₗ[k] MvPolynomial (Fin N × Fin N) k) (hπ : ∀ f, π f ∈ D τ)
    (Q : MvPolynomial (BVar N ι) k) (hQ : Q ∈ gen N D T) : E N τ π Q ∈ gen N D (insert τ T) := by
  obtain ⟨f, hf, rfl⟩ := hQ
  set A := ∏ σ ∈ Finset.univ.erase τ, rename (fun v : Fin N × Fin N => ((σ, v) : BVar N ι)) (f σ) with hAdef
  have hsplit : ∏ σ, rename (fun v : Fin N × Fin N => ((σ, v) : BVar N ι)) (f σ) =
      A * rename (fun v : Fin N × Fin N => ((τ, v) : BVar N ι)) (f τ) :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ τ)).symm
  have hA : ∃ q, Ψ N τ A = map (algebraMap k (MvPolynomial (Fin N × Fin N) k)) q := by
    refine Finset.prod_induction _ (fun x => ∃ q, Ψ N τ x = map (algebraMap k (MvPolynomial (Fin N × Fin N) k)) q)
      (fun a b ⟨qa, ha⟩ ⟨qb, hb⟩ => ⟨qa * qb, by rw [map_mul, ha, hb, map_mul]⟩) ⟨1, by simp⟩ ?_
    intro σ hσ
    exact ⟨_, Ψ_rename_ne N τ σ (Finset.ne_of_mem_erase hσ) (f σ)⟩
  obtain ⟨q, hq⟩ := hA
  refine ⟨Function.update f τ (π (f τ)), ?_, ?_⟩
  · intro σ hσ
    by_cases h : σ = τ
    · subst h; simp [hπ]
    · rw [Function.update_of_ne h]
      exact hf σ (by simpa [h] using hσ)
  · have hA' : ∏ σ ∈ Finset.univ.erase τ,
        rename (fun v : Fin N × Fin N => ((σ, v) : BVar N ι)) (Function.update f τ (π (f τ)) σ) = A := by
      refine Finset.prod_congr rfl fun σ hσ => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hσ)]
    have hR : ∏ σ, rename (fun v : Fin N × Fin N => ((σ, v) : BVar N ι)) (Function.update f τ (π (f τ)) σ) =
        A * rename (fun v : Fin N × Fin N => ((τ, v) : BVar N ι)) (π (f τ)) := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ τ), Function.update_self, hA']
    rw [hR, hsplit]
    show (Ψ N τ).symm (mr π (Ψ N τ (A * rename (fun v : Fin N × Fin N => ((τ, v) : BVar N ι)) (f τ)))) =
      A * rename (fun v : Fin N × Fin N => ((τ, v) : BVar N ι)) (π (f τ))
    rw [map_mul, hq, Ψ_rename_self, mr_map_mul, mr_C, ← Ψ_rename_self N τ, ← hq, ← map_mul,
      AlgEquiv.symm_apply_apply]

theorem span_gen_empty (D : ι → Submodule k (MvPolynomial (Fin N × Fin N) k)) (P : MvPolynomial (BVar N ι) k) :
    P ∈ Submodule.span k (gen N D ∅) := by
  have hmulX : ∀ v : BVar N ι, ∀ Q ∈ Submodule.span k (gen N D ∅), Q * X v ∈ Submodule.span k (gen N D ∅) := by
    intro v Q hQ
    induction hQ using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨f, -, rfl⟩ := hQ
      refine Submodule.subset_span ⟨fun σ => f σ * (if σ = v.1 then X v.2 else 1), by simp, ?_⟩
      simp only [map_mul, Finset.prod_mul_distrib]
      congr 1
      simp only [apply_ite, rename_X, map_one]
      rw [Finset.prod_ite_eq']
      simp
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h1 : (1 : MvPolynomial (BVar N ι) k) ∈ gen N D ∅ := ⟨fun _ => 1, by simp, by simp⟩
    rw [show (C a : MvPolynomial (BVar N ι) k) = a • 1 by rw [smul_eq_C_mul, mul_one]]
    exact Submodule.smul_mem _ a (Submodule.subset_span h1)
  | add p q hp hq => exact add_mem hp hq
  | mul_X p v ih => exact hmulX v p ih

theorem mem_span_gen_univ (D : ι → Submodule k (MvPolynomial (Fin N × Fin N) k)) (P : MvPolynomial (BVar N ι) k)
    (h : ∀ τ β, coeff β (Ψ N τ P) ∈ D τ) : P ∈ Submodule.span k (gen N D Finset.univ) := by
  choose π hπ1 hπ2 using fun τ => exists_proj (D τ)
  have key : ∀ T : Finset ι, P ∈ Submodule.span k (gen N D T) := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact span_gen_empty N D P
    | insert τ T hτ ih =>
      have hfix : E N τ (π τ) P = P := by
        show (Ψ N τ).symm (mr (π τ) (Ψ N τ P)) = P
        have : mr (π τ) (Ψ N τ P) = Ψ N τ P := by
          ext β
          rw [coeff_mr, hπ2 τ _ (h τ β)]
        rw [this, AlgEquiv.symm_apply_apply]
      rw [← hfix]
      have hle : Submodule.span k (gen N D T) ≤ (Submodule.span k (gen N D (insert τ T))).comap (E N τ (π τ)) :=
        Submodule.span_le.mpr fun Q hQ => Submodule.subset_span (E_gen N D T τ (π τ) (hπ1 τ) Q hQ)
      exact hle ih
  exact key Finset.univ

end

end GlobalTheory.HighWtEmb.NabInter

namespace GlobalTheory.HighWtEmb

open NabInter in

theorem mem_nabK_of_toBlock : ∀ (k : Type) [Field k] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ν : ι → Fin N → ℕ) (P : MvPolynomial (BVar N ι) k),
    (∀ τ, toBlock k N τ P ∈ dualWeyl (MvPolynomial (OVar N τ) k) N N (ν τ)) → P ∈ nabK k N ν := by
  intro k _ N ι _ _ ν P hP
  have h : ∀ τ β, coeff β (Ψ N τ P) ∈ dualWeyl k N N (ν τ) := by
    intro τ β
    have := dualWeyl_mr (lcoeff k β) N N (ν τ) _ (hP τ)
    convert this using 1
    ext m
    rw [Ψ_eq_toBlock, coeff_mr, lcoeff_apply, coeff_coeff_commAlgEquiv]
  have := mem_span_gen_univ N (fun τ => dualWeyl k N N (ν τ)) P h
  refine Submodule.span_mono ?_ this
  rintro Q ⟨f, hf, rfl⟩
  exact ⟨f, fun τ => hf τ (Finset.mem_univ τ), rfl⟩

end GlobalTheory.HighWtEmb

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_dualWeylProductSpan_of_factorwise_dualWeyl : ∀ (k : Type) [Field k] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (ν : ι → Fin N → ℕ) (P : MvPolynomial (BVar N ι) k), (∀ τ, toBlock k N τ P ∈ dualWeyl (MvPolynomial (OVar N τ) k) N N (ν τ)) → P ∈ nabK k N ν := by
  atlas_forward_decl GlobalTheory.HighWtEmb.mem_nabK_of_toBlock
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HighWtEmb

theorem exists_prodProj (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ)
    (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm] (w : ι → Fin N → ℕ) (z₀ : Gm)
    (hz : ∀ τ (a : alg O N lam), IsProj O N lam τ (w τ) a → a • z₀ = z₀) (s : Finset ι) :
    ∃ e : alg O N lam, e • z₀ = z₀ ∧ ∀ x : ∀ τ, dualWeyl O N N (res N (lam τ)),
      (e : Module.End O (NablaT O N lam)) (PiTensorProduct.tprod O x) =
        PiTensorProduct.tprod O (fun σ => if σ ∈ s then rowProj O N (res N (lam σ)) (w σ) (x σ) else x σ) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_smul _ _, fun x => by simp⟩
  | insert τ s hτ ih =>
    obtain ⟨e, he, hex⟩ := ih
    obtain ⟨p, hp, -⟩ := exists_unique_isProj O N ι lam τ (w τ)
    let pA : alg O N lam := ⟨p, Algebra.subset_adjoin (Or.inr ⟨τ, w τ, hp⟩)⟩
    refine ⟨pA * e, by rw [mul_smul, he]; exact hz τ pA hp, fun x => ?_⟩
    show p ((e : Module.End O (NablaT O N lam)) _) = _
    rw [hex]
    rw [hp _ (rowProj O N (res N (lam τ)) (w τ) (x τ)) (by simp [hτ, rowProj])]
    congr 1
    funext σ
    by_cases h : σ = τ
    · subst h; simp
    · simp [Function.update_of_ne h, h]

theorem prodProj_mul_eq_zero (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ)
    (w : ι → Fin N → ℕ) (e : Module.End O (NablaT O N lam))
    (he : ∀ x : ∀ τ, dualWeyl O N N (res N (lam τ)),
      e (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (fun σ => rowProj O N (res N (lam σ)) (w σ) (x σ)))
    (τ : ι) (v : Fin N → ℕ) (a : Module.End O (NablaT O N lam)) (ha : IsProj O N lam τ v a) (hv : v ≠ w τ) : e * a = 0 := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, Module.End.mul_apply, LinearMap.zero_apply]
  rw [ha x (rowProj O N (res N (lam τ)) v (x τ)) (by simp [rowProj]), he]
  refine (PiTensorProduct.tprod O).map_coord_zero τ ?_
  simp only [Function.update_self]
  apply Subtype.ext
  simp only [rowProj, LinearMap.restrict_apply, ZeroMemClass.coe_zero]
  rw [weightedHomogeneousComponent_of_mem (weightedHomogeneousComponent_isWeightedHomogeneous _ _), if_neg hv.symm]

set_option synthInstance.maxHeartbeats 400000 in

theorem exists_weightForm : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], SubQ O N lam ϖ Gm → ∀ (w : ι → Fin N → ℕ) (z₀ : Gm), z₀ ≠ 0 → (∀ τ (a : alg O N lam), IsProj O N lam τ (w τ) a → a • z₀ = z₀) → ∃ φ : Gm →+ O ⧸ Ideal.span {ϖ}, φ z₀ ≠ 0 ∧ (∀ (c : O) (z : Gm), φ (algebraMap O (alg O N lam) c • z) = Ideal.Quotient.mk (Ideal.span {ϖ}) c * φ z) ∧ ∀ τ (v : Fin N → ℕ) (a : alg O N lam), IsProj O N lam τ v a → v ≠ w τ → ∀ z, φ (a • z) = 0 := by
  intro O _ _ _ N ι _ _ lam ϖ hϖ Gm _ _ hSQ w z₀ hz0 hfix

  have hkill : ∀ z : Gm, algebraMap O (alg O N lam) ϖ • z = 0 := by
    obtain ⟨U, π, hπ, h0⟩ := hSQ
    intro z
    obtain ⟨x, rfl⟩ := hπ z
    rw [← map_smul]
    exact h0 _ x rfl
  letI iO : Module O Gm := Module.compHom Gm (algebraMap O (alg O N lam))
  have hT : Module.IsTorsionBySet O Gm (Ideal.span {ϖ} : Ideal O) :=
    (Module.isTorsionBySet_span_singleton_iff ϖ).2 fun z => hkill z
  haveI hmax : (Ideal.span {ϖ} : Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  letI kF : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  letI iK : Module (O ⧸ Ideal.span {ϖ}) Gm := hT.module
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (O ⧸ Ideal.span {ϖ}) hz0
  obtain ⟨e, he, hex⟩ := exists_prodProj O N ι lam Gm w z₀ hfix Finset.univ
  let φ : Gm →+ O ⧸ Ideal.span {ϖ} :=
    { toFun := fun z => f (e • z)
      map_zero' := by simp
      map_add' := fun y z => by simp [smul_add] }
  refine ⟨φ, ?_, fun c z => ?_, fun τ v a ha hv z => ?_⟩
  · show f (e • z₀) ≠ 0
    rw [he]; exact hf
  · show f (e • (algebraMap O (alg O N lam) c • z)) = _ * f (e • z)
    rw [← mul_smul, ← Algebra.commutes, mul_smul]
    have : algebraMap O (alg O N lam) c • (e • z) = (Ideal.Quotient.mk (Ideal.span {ϖ}) c) • (e • z) := rfl
    rw [this, map_smul, smul_eq_mul]
  · show f (e • (a • z)) = 0
    have h0 : e * a = 0 := by
      apply Subtype.ext
      exact prodProj_mul_eq_zero O N ι lam w (e : Module.End O (NablaT O N lam))
        (fun x => by rw [hex]; simp) τ v a ha hv
    rw [← mul_smul, h0, zero_smul, map_zero]

end GlobalTheory.HighWtEmb
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weightForm_on_simple_subquotient : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], SubQ O N lam ϖ Gm → ∀ (w : ι → Fin N → ℕ) (z₀ : Gm), z₀ ≠ 0 → (∀ τ (a : alg O N lam), IsProj O N lam τ (w τ) a → a • z₀ = z₀) → ∃ φ : Gm →+ O ⧸ Ideal.span {ϖ}, φ z₀ ≠ 0 ∧ (∀ (c : O) (z : Gm), φ (algebraMap O (alg O N lam) c • z) = Ideal.Quotient.mk (Ideal.span {ϖ}) c * φ z) ∧ ∀ τ (v : Fin N → ℕ) (a : alg O N lam), IsProj O N lam τ v a → v ≠ w τ → ∀ z, φ (a • z) = 0 := by
  atlas_forward_decl GlobalTheory.HighWtEmb.exists_weightForm
end

section
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

namespace GlobalTheory.HighWtEmb

set_option maxHeartbeats 1000000 in

theorem embeds_of_maxWeight : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (lam τ))) → GlobalTheory.HighWt.BaseChange → GlobalTheory.HighWt.CoefIn O N lam → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], IsSimpleModule (alg O N lam) Gm → SubQ O N lam ϖ Gm → ∀ w : ι → Fin N → ℕ, (∀ τ, Antitone (w τ)) → GlobalTheory.HighWt.JointWt O N lam Gm w → (∀ w' : ι → Fin N → ℕ, GlobalTheory.HighWt.JointWt O N lam Gm w' → GlobalTheory.HighWt.pot N w' ≤ GlobalTheory.HighWt.pot N w) → Embeds O N lam (GlobalTheory.HighWt.extW N w) ϖ Gm := by
  intro O _ _ _ _ N ι _ _ lam ϖ hϖ hlam hBC hC Gm _ _ hS hSQ w hw hJ hmax
  obtain ⟨z₀, hz₀, hfix⟩ := hJ
  obtain ⟨φ, hφ0, hφc, hφp⟩ := GlobalTheory.T.exists_weightForm_on_simple_subquotient O N ι lam ϖ hϖ Gm hSQ w z₀ hz₀ hfix
  obtain ⟨Pz, hPc, hPg, hPp, hPn, hPz0⟩ :=
    GlobalTheory.T.exists_matrixCoefficientPoly_simpleSubquotient O N ι lam ϖ hϖ hlam hC Gm hSQ w hmax φ z₀ hφ0 hfix hφc hφp
  have hmuA : ∀ τ, Antitone (res N (GlobalTheory.HighWt.extW N w τ)) := fun τ => by
    rw [GlobalTheory.HighWt.res_extW]; exact hw τ
  have hle : (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N (GlobalTheory.HighWt.extW N w))) ≤
      LinearMap.ker (redT O N (GlobalTheory.HighWt.extW N w) ϖ) := by
    refine Submodule.smul_le.2 fun r hr n _ => ?_
    rw [LinearMap.mem_ker, map_smul]
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [Algebra.smul_def, MvPolynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq, map_mul,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self ϖ), mul_zero, map_zero, zero_mul]
  set L := (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N (GlobalTheory.HighWt.extW N w))).liftQ
    (redT O N (GlobalTheory.HighWt.extW N w) ϖ) hle with hL
  have hLmk : ∀ y, L (Submodule.Quotient.mk y) = redT O N (GlobalTheory.HighWt.extW N w) ϖ y := fun y => rfl
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, hL, Submodule.ker_liftQ_eq_bot]
    intro y hy
    exact GlobalTheory.T.mem_smul_top_of_dualWeylTensorReduction_eq_zero O N ι (GlobalTheory.HighWt.extW N w) ϖ hϖ hmuA hBC y hy
  have hsurj : ∀ z, ∃ q, L q = Pz z := by
    intro z
    have h1 : Pz z ∈ nabK (O ⧸ Ideal.span {ϖ}) N (fun τ => res N (GlobalTheory.HighWt.extW N w τ)) := by
      have e : (fun τ => res N (GlobalTheory.HighWt.extW N w τ)) = w := funext fun τ => GlobalTheory.HighWt.res_extW N w τ
      rw [e]
      haveI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
      letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
      exact GlobalTheory.T.mem_dualWeylProductSpan_of_factorwise_dualWeyl (O ⧸ Ideal.span {ϖ}) N ι w (Pz z) (hPn z)
    obtain ⟨y, hy⟩ := GlobalTheory.T.exists_lift_dualWeylTensorReduction O N ι (GlobalTheory.HighWt.extW N w) ϖ hϖ hmuA hBC _ h1
    exact ⟨Submodule.Quotient.mk y, hy⟩
  choose q hq using hsurj
  have hsm : ∀ (a : alg O N lam) (z : Gm), Pz z = 0 → Pz (a • z) = 0 := by
    rintro ⟨a, ha⟩
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      intro z hz
      rcases hx with ⟨g, rfl⟩ | ⟨τ, v, hp⟩
      · have e : (⟨grp O N lam g, Algebra.subset_adjoin (Or.inl ⟨g, rfl⟩)⟩ : alg O N lam) = grpA O N lam g := rfl
        rw [e, hPg, hz, map_zero]
      · rw [hPp τ v _ hp, hz, map_zero]
    | algebraMap c =>
      intro z hz
      have e : (⟨algebraMap O _ c, Subalgebra.algebraMap_mem _ c⟩ : alg O N lam) = algebraMap O (alg O N lam) c := rfl
      rw [e, hPc, hz, mul_zero]
    | add x y hx hy ihx ihy =>
      intro z hz
      have e : (⟨x + y, Subalgebra.add_mem _ hx hy⟩ : alg O N lam) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [e, add_smul, map_add, ihx z hz, ihy z hz, add_zero]
    | mul x y hx hy ihx ihy =>
      intro z hz
      have e : (⟨x * y, Subalgebra.mul_mem _ hx hy⟩ : alg O N lam) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [e, mul_smul]
      exact ihx _ (ihy z hz)
  let K : Submodule (alg O N lam) Gm :=
    { carrier := {z | Pz z = 0}
      add_mem' := fun {a b} ha hb => by simp only [Set.mem_setOf_eq, map_add] at *; rw [ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun a z hz => hsm a z hz }
  have hK : K = ⊥ := by
    haveI : IsSimpleOrder (Submodule (alg O N lam) Gm) := (isSimpleModule_iff _ _).1 hS
    rcases IsSimpleOrder.eq_bot_or_eq_top K with h | h
    · exact h
    · exfalso
      have : z₀ ∈ K := h ▸ Submodule.mem_top
      exact hPz0 this
  let ψ : Gm →+ NablaT O N (GlobalTheory.HighWt.extW N w) ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N (GlobalTheory.HighWt.extW N w))) :=
    { toFun := q
      map_zero' := hLinj (by rw [hq, map_zero, map_zero])
      map_add' := fun a b => hLinj (by rw [hq, map_add, map_add, hq, hq]) }
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have h1 : Pz (a - b) = 0 := by
      rw [map_sub, ← hq a, ← hq b]
      exact sub_eq_zero.2 (congrArg L hab)
    have h2 : a - b ∈ K := h1
    rw [hK, Submodule.mem_bot] at h2
    exact sub_eq_zero.1 h2
  · intro c z
    apply hLinj
    change L (q _) = L (c • q z)
    rw [hq, hPc, LinearMap.map_smul, hq, Algebra.smul_def, MvPolynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq]
  · intro g z y hzy
    apply hLinj
    change L (q _) = _
    have hzy' : q z = Submodule.Quotient.mk y := hzy
    rw [hq, hLmk, GlobalTheory.T.dualWeylTensorReduction_intertwines_group_action, hPg, ← hq z, hzy', hLmk]
  · intro τ v a a' ha ha' z y hzy
    apply hLinj
    change L (q _) = _
    have hzy' : q z = Submodule.Quotient.mk y := hzy
    rw [hq, hLmk, GlobalTheory.T.dualWeylTensorReduction_weightProjector O N ι _ ϖ τ v a' ha', hPp τ v a ha, ← hq z, hzy', hLmk]

end GlobalTheory.HighWtEmb

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simple_subquotient_embeds_dualWeyl_reduction_maxWeight : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (lam τ))) → GlobalTheory.HighWt.BaseChange → GlobalTheory.HighWt.CoefIn O N lam → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], IsSimpleModule (alg O N lam) Gm → SubQ O N lam ϖ Gm → ∀ w : ι → Fin N → ℕ, (∀ τ, Antitone (w τ)) → GlobalTheory.HighWt.JointWt O N lam Gm w → (∀ w' : ι → Fin N → ℕ, GlobalTheory.HighWt.JointWt O N lam Gm w' → GlobalTheory.HighWt.pot N w' ≤ GlobalTheory.HighWt.pot N w) → Embeds O N lam (GlobalTheory.HighWt.extW N w) ϖ Gm := by
  atlas_forward_decl GlobalTheory.HighWtEmb.embeds_of_maxWeight
end

section
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem GlobalTheory.HighWt.simpleSubquot_embeds : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (lam τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], IsSimpleModule (alg O N lam) Gm → SubQ O N lam ϖ Gm → ∃ mu : ι → ℕ → ℕ, (∀ τ, Antitone (res N (mu τ)) ∧ ∑ a : Fin N, mu τ a = ∑ a : Fin N, lam τ a ∧ (∀ a : Fin N, lam τ (N - 1) ≤ mu τ a ∧ mu τ a ≤ lam τ 0) ∧ ∃ (e : alg O N lam) (z : Gm), IsProj O N lam τ (res N (mu τ)) e ∧ e • z ≠ 0) ∧ Embeds O N lam mu ϖ Gm := by
  intro O _ _ _ _ N ι _ _ lam ϖ hϖ hlam Gm _ _ hs hsub
  classical
  haveI : Nontrivial Gm := IsSimpleModule.nontrivial (alg O N lam) Gm
  obtain ⟨w0, hw0⟩ := GlobalTheory.T.exists_jointRowWeight_dualWeylModule O N ι lam Gm inferInstance
  have hB := GlobalTheory.T.jointRowWeight_bounds_dualWeylModule O N ι lam hlam Gm
  let S : Set (ι → Fin N → ℕ) := {w | GlobalTheory.HighWt.JointWt O N lam Gm w}
  have hfin : S.Finite := by
    refine Set.Finite.subset (Set.Finite.pi (t := fun τ => Set.pi Set.univ fun _ : Fin N => Set.Iic (lam τ 0))
      fun τ => Set.Finite.pi fun _ => Set.finite_Iic _) ?_
    intro w hw
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Iic, true_implies]
    intro τ a
    exact ((hB w hw τ).2 a).2
  obtain ⟨w, hwS, hmax⟩ := hfin.toFinset.exists_max_image (GlobalTheory.HighWt.pot N) ⟨w0, hfin.mem_toFinset.2 hw0⟩
  rw [Set.Finite.mem_toFinset] at hwS
  have hmax' : ∀ w', GlobalTheory.HighWt.JointWt O N lam Gm w' → GlobalTheory.HighWt.pot N w' ≤ GlobalTheory.HighWt.pot N w :=
    fun w' h' => hmax w' (hfin.mem_toFinset.2 h')
  have hanti := GlobalTheory.T.jointRowWeight_antitone_of_maxPotential O N ι lam Gm w hwS hmax'
  refine ⟨GlobalTheory.HighWt.extW N w, fun τ => ?_, GlobalTheory.T.simple_subquotient_embeds_dualWeyl_reduction_maxWeight O N ι lam ϖ hϖ hlam GlobalTheory.T.highest_weight_base_change (GlobalTheory.T.genericRowCoef_mem_coefAlgebra_of_domain O N ι lam) Gm hs hsub w hanti hwS hmax'⟩
  rw [GlobalTheory.HighWt.res_extW]
  refine ⟨hanti τ, ?_, ?_, ?_⟩
  · have := (hB w hwS τ).1
    simpa [GlobalTheory.HighWt.extW, Fin.is_lt] using this
  · intro a
    simpa [GlobalTheory.HighWt.extW, Fin.is_lt] using (hB w hwS τ).2 a
  · obtain ⟨a, ha, -⟩ := GlobalTheory.T.existsUnique_dualWeylWeightProjector O N ι lam τ (w τ)
    obtain ⟨z, hz, hfix⟩ := hwS
    let e : alg O N lam := ⟨a, Algebra.subset_adjoin (Or.inr ⟨τ, w τ, ha⟩)⟩
    refine ⟨e, z, ha, ?_⟩
    rw [hfix τ e ha]
    exact hz

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simpleSubquotient_dualWeyl_embeds_highestWeight : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (lam τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], IsSimpleModule (alg O N lam) Gm → SubQ O N lam ϖ Gm → ∃ mu : ι → ℕ → ℕ, (∀ τ, Antitone (res N (mu τ)) ∧ ∑ a : Fin N, mu τ a = ∑ a : Fin N, lam τ a ∧ (∀ a : Fin N, lam τ (N - 1) ≤ mu τ a ∧ mu τ a ≤ lam τ 0) ∧ ∃ (e : alg O N lam) (z : Gm), IsProj O N lam τ (res N (mu τ)) e ∧ e • z ≠ 0) ∧ Embeds O N lam mu ϖ Gm := by
  atlas_forward_decl GlobalTheory.HighWt.simpleSubquot_embeds
end
