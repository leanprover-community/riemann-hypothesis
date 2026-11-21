import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.SmoothColumnLifts.SmoothCol
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.SmoothColumnLifts.KerOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedAbsDetMulIntegralCompMulVecFinitePlace
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorOpenCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexAnnihilatorsDuality
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeAnnihilatorWithinNhds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenCompactLatticeContaining
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaussianDualMeasure.DualMeasure
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaussianDualMeasure.SecondCountableTopologyAndT2Space
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalContinuousSectionVecMulOrbit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyHaarDetEqOneNearOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureSubgroupRelIndexMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGLLastBasisVecMulEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteImageCompactOpenQuotient
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.SmoothColumnLifts.ULiftOfAbs

section
noncomputable section

open Matrix
open scoped Topology

namespace PositivityTheory.RgUd.Form.U.Lift2.AvA

section Grp

variable {G : Type*} [AddCommGroup G]

theorem sum_transl {M : Type*} [AddCommMonoid M] (A H : AddSubgroup G) (_hHA : H ≤ A) (T : Finset G)
    (hT : ∀ t ∈ T, t ∈ A) (hu : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H)
    (f : G → M) (hf : ∀ x, ∀ h ∈ H, f (x + h) = f x) (a : G) (ha : a ∈ A) :
    ∑ t ∈ T, f (t + a) = ∑ t ∈ T, f t := by
  classical
  have hex : ∀ x ∈ A, ∃ t, t ∈ T ∧ x - t ∈ H := fun x hx => (hu x hx).exists
  let r : G → G := fun x => if hx : x ∈ A then (hex x hx).choose else x
  have hr : ∀ x ∈ A, r x ∈ T ∧ x - r x ∈ H := by
    intro x hx
    simp only [r, dif_pos hx]
    exact (hex x hx).choose_spec
  have huniq : ∀ x ∈ A, ∀ t ∈ T, x - t ∈ H → r x = t := fun x hx t ht hxt =>
    (hu x hx).unique (hr x hx) ⟨ht, hxt⟩
  have hfr : ∀ x ∈ A, f x = f (r x) := by
    intro x hx
    have := hf (r x) (x - r x) (hr x hx).2
    rw [add_sub_cancel] at this
    exact this
  refine Finset.sum_nbij' (fun t => r (t + a)) (fun t => r (t - a)) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    exact (hr _ (A.add_mem (hT t ht) ha)).1
  · intro t ht
    exact (hr _ (A.sub_mem (hT t ht) ha)).1
  · intro t ht
    have h1 := hr (t + a) (A.add_mem (hT t ht) ha)
    apply huniq _ (A.sub_mem (hT _ h1.1) ha) t ht
    have : r (t + a) - a - t = -((t + a) - r (t + a)) := by abel
    rw [this]
    exact H.neg_mem h1.2
  · intro t ht
    have h1 := hr (t - a) (A.sub_mem (hT t ht) ha)
    apply huniq _ (A.add_mem (hT _ h1.1) ha) t ht
    have : r (t - a) + a - t = -((t - a) - r (t - a)) := by abel
    rw [this]
    exact H.neg_mem h1.2
  · intro t ht
    exact hfr _ (A.add_mem (hT t ht) ha)

theorem card_ne_zero (A H : AddSubgroup G) (T : Finset G) (hu : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H) :
    (T.card : ℂ) ≠ 0 := by
  obtain ⟨t, ⟨ht, -⟩, -⟩ := hu 0 A.zero_mem
  exact Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨t, ht⟩)

theorem sum_char_eq_zero (A H : AddSubgroup G) (hHA : H ≤ A) (T : Finset G)
    (hT : ∀ t ∈ T, t ∈ A) (hu : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H)
    (χ : G → ℂ) (hχ : ∀ x y, χ (x + y) = χ x * χ y) (hH : ∀ h ∈ H, χ h = 1)
    (a : G) (ha : a ∈ A) (hne : χ a ≠ 1) : ∑ t ∈ T, χ t = 0 := by
  have h := sum_transl A H hHA T hT hu χ (fun x h hh => by rw [hχ, hH h hh, mul_one]) a ha
  simp_rw [hχ] at h
  rw [← Finset.sum_mul] at h
  have : (∑ t ∈ T, χ t) * (χ a - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
  rcases mul_eq_zero.1 this with h1 | h1
  · exact h1
  · exact absurd (sub_eq_zero.1 h1) hne

theorem avg_indep {M : Type*} [AddCommGroup M] [Module ℂ M] (A H K : AddSubgroup G) (hHA : H ≤ A)
    (hKA : K ≤ A) (S R : Finset G)
    (hS : ∀ t ∈ S, t ∈ A) (huS : ∀ a ∈ A, ∃! t, t ∈ S ∧ a - t ∈ H)
    (hR : ∀ t ∈ R, t ∈ A) (huR : ∀ a ∈ A, ∃! t, t ∈ R ∧ a - t ∈ K)
    (f : G → M) (hfH : ∀ x, ∀ h ∈ H, f (x + h) = f x) (hfK : ∀ x, ∀ h ∈ K, f (x + h) = f x) :
    ((S.card : ℂ)⁻¹) • ∑ t ∈ S, f t = ((R.card : ℂ)⁻¹) • ∑ t ∈ R, f t := by
  have e1 : ∑ r ∈ R, ∑ t ∈ S, f (t + r) = (R.card : ℂ) • ∑ t ∈ S, f t := by
    rw [Finset.sum_congr rfl (fun r hr => sum_transl A H hHA S hS huS f hfH r (hR r hr))]
    rw [Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have e2 : ∑ t ∈ S, ∑ r ∈ R, f (r + t) = (S.card : ℂ) • ∑ t ∈ R, f t := by
    rw [Finset.sum_congr rfl (fun t ht => sum_transl A K hKA R hR huR f hfK t (hS t ht))]
    rw [Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have key : (R.card : ℂ) • ∑ t ∈ S, f t = (S.card : ℂ) • ∑ t ∈ R, f t := by
    rw [← e1, ← e2, Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [add_comm]
  have hSp := card_ne_zero A H S huS
  have hRp := card_ne_zero A K R huR
  have hX : (∑ t ∈ S, f t) = (R.card : ℂ)⁻¹ • ((S.card : ℂ) • ∑ t ∈ R, f t) := by
    rw [← key, smul_smul, inv_mul_cancel₀ hRp, one_smul]
  rw [hX, smul_smul, smul_smul, mul_comm ((S.card : ℂ)⁻¹) ((R.card : ℂ)⁻¹), mul_assoc,
    inv_mul_cancel₀ hSp, mul_one]

theorem sum_circ_eq_zero (A H : AddSubgroup G) (hHA : H ≤ A) (T : Finset G)
    (hT : ∀ t ∈ T, t ∈ A) (hu : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H)
    (χ : G → Circle) (hχ : ∀ x y, χ (x + y) = χ x * χ y) (hH : ∀ h ∈ H, χ h = 1)
    (a : G) (ha : a ∈ A) (hne : χ a ≠ 1) : ∑ t ∈ T, ((χ t : Circle) : ℂ) = 0 :=
  sum_char_eq_zero A H hHA T hT hu (fun x => (χ x : ℂ)) (fun x y => by rw [hχ, Circle.coe_mul])
    (fun h hh => by rw [hH h hh, Circle.coe_one]) a ha (fun h => hne (Circle.coe_eq_one.1 h))

theorem exists_tr [TopologicalSpace G] [IsTopologicalAddGroup G] (A H : AddSubgroup G)
    (hAc : IsCompact (A : Set G)) (hH : IsOpen (H : Set G)) (hHA : H ≤ A) :
    ∃ T : Finset G, (∀ t ∈ T, t ∈ A) ∧ ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H := by
  classical
  obtain ⟨F, hF⟩ := hAc.elim_finite_subcover (fun a : A => (fun x => x - (a : G)) ⁻¹' (H : Set G))
    (fun a => hH.preimage (continuous_sub_right _))
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, by simp [H.zero_mem]⟩)
  let r : G → G := fun x => Quotient.out (QuotientAddGroup.mk x : G ⧸ H)
  have hr : ∀ x, r x - x ∈ H := fun x => by
    obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add H x
    simp only [r]
    rw [hh, add_sub_cancel_left]
    exact h.2
  have hrr : ∀ x y, x - y ∈ H → r x = r y := fun x y hxy => by
    simp only [r]
    congr 1
    refine QuotientAddGroup.eq.2 ?_
    have : -x + y = -(x - y) := by abel
    rw [this]
    exact H.neg_mem hxy
  have hrA : ∀ x ∈ A, r x ∈ A := fun x hx => by
    have : r x = x + (r x - x) := by abel
    rw [this]
    exact A.add_mem hx (hHA (hr x))
  refine ⟨F.image (fun a : A => r a), ?_, ?_⟩
  · intro t ht
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 ht
    exact hrA a a.2
  · intro a ha
    obtain ⟨i, hi, hai⟩ := Set.mem_iUnion₂.1 (hF ha)
    refine ⟨r i, ⟨Finset.mem_image.2 ⟨i, hi, rfl⟩, ?_⟩, ?_⟩
    · have : a - r i = (a - i) - (r i - i) := by abel
      rw [this]
      exact H.sub_mem hai (hr i)
    · rintro t ⟨ht, hat⟩
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ht
      have h1 : r (r j) = r j := hrr _ _ (hr j)
      have h2 : r (r i) = r i := hrr _ _ (hr i)
      have h3 : r j - r i ∈ H := by
        have : r j - r i = (a - r i) - (a - r j) := by abel
        rw [this]
        have : a - r i = (a - i) - (r i - i) := by abel
        rw [this]
        exact H.sub_mem (H.sub_mem hai (hr i)) hat
      rw [← h1, ← h2]
      exact hrr _ _ h3

end Grp

theorem isOpen_ker {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (φ : AddChar k Circle) (hφ : Continuous φ) : IsOpen {x : k | φ x = 1} :=
  PositivityTheory.RgUd.Form.U.Lift2.KerOpen.isOpen_ker φ hφ

end PositivityTheory.RgUd.Form.U.Lift2.AvA
end
end

section
noncomputable section

set_option linter.unusedSectionVars false

open Matrix
open scoped Topology

namespace PositivityTheory.RgUd.Form.U.Lift2.AvA

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}

def stab (col : (Fin n → k) → V →ₗ[ℂ] V) (hc0 : ∀ v, col 0 v = v)
    (hca : ∀ x y v, col (x + y) v = col x (col y v)) (v : V) : AddSubgroup (Fin n → k) where
  carrier := {x | col x v = v}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [hca, hy, hx]
  zero_mem' := hc0 v
  neg_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    calc col (-x) v = col (-x) (col x v) := by rw [hx]
      _ = col (-x + x) v := (hca _ _ _).symm
      _ = v := by rw [neg_add_cancel, hc0]

def kers (φ : AddChar k Circle) (s : Finset (Fin n → k)) : AddSubgroup (Fin n → k) where
  carrier := {x | ∀ ξ ∈ s, φ (ξ ⬝ᵥ x) = 1}
  add_mem' := by
    intro x y hx hy ξ hξ
    rw [dotProduct_add, AddChar.map_add_eq_mul, hx ξ hξ, hy ξ hξ, one_mul]
  zero_mem' := by
    intro ξ _
    simp
  neg_mem' := by
    intro x hx ξ hξ
    rw [dotProduct_neg, AddChar.map_neg_eq_inv, hx ξ hξ, inv_one]

theorem isOpen_kers (φ : AddChar k Circle) (hφ : Continuous φ) (s : Finset (Fin n → k)) :
    IsOpen (kers φ s : Set (Fin n → k)) := by
  have : (kers φ s : Set (Fin n → k)) = ⋂ ξ ∈ s, {x | φ (ξ ⬝ᵥ x) = 1} := by
    ext x
    simp [kers]
  rw [this]
  refine isOpen_biInter_finset fun ξ _ => ?_
  exact (isOpen_ker φ hφ).preimage (by fun_prop)

theorem exists_AD (φ : AddChar k Circle) (hφ : Continuous φ) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hc0 : ∀ v, col 0 v = v) (hca : ∀ x y v, col (x + y) v = col x (col y v))
    (hsm : ∀ v, IsOpen {x | col x v = v})
    (A : AddSubgroup (Fin n → k)) (hA : Lat A) (s : Finset (Fin n → k)) (v : V) :
    ∃ p : AddSubgroup (Fin n → k) × Finset (Fin n → k), ∀ ξ ∈ s, AD φ col ξ A v p := by
  let H := A ⊓ stab col hc0 hca v ⊓ kers φ s
  have hHo : IsOpen (H : Set (Fin n → k)) := by
    simp only [H, AddSubgroup.coe_inf]
    exact (hA.2.inter (hsm v)).inter (isOpen_kers φ hφ s)
  have hHA : H ≤ A := fun x hx => hx.1.1
  obtain ⟨T, hT, hu⟩ := exists_tr A H hA.1 hHo hHA
  exact ⟨(H, T), fun ξ hξ => ⟨hHA, hHo, fun a ha => ha.1.2, fun a ha => ha.2 ξ hξ, hT, hu⟩⟩

theorem summand_inv (φ : AddChar k Circle) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hca : ∀ x y v, col (x + y) v = col x (col y v)) (ξ : Fin n → k) (v : V) (H : AddSubgroup (Fin n → k))
    (h3 : ∀ a ∈ H, col a v = v) (h4 : ∀ a ∈ H, φ (ξ ⬝ᵥ a) = 1) :
    ∀ x, ∀ h ∈ H, (fun t => (starRingEnd ℂ ((φ (ξ ⬝ᵥ t) : Circle) : ℂ)) • col t v) (x + h) =
      (fun t => (starRingEnd ℂ ((φ (ξ ⬝ᵥ t) : Circle) : ℂ)) • col t v) x := by
  intro x h hh
  simp only [dotProduct_add, AddChar.map_add_eq_mul, h4 h hh, mul_one, hca, h3 h hh]

theorem av_eq' (φ : AddChar k Circle) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hca : ∀ x y v, col (x + y) v = col x (col y v))
    (A : AddSubgroup (Fin n → k)) (ξ : Fin n → k) (v : V) (p : AddSubgroup (Fin n → k) × Finset (Fin n → k))
    (hp : AD φ col ξ A v p) :
    av φ col ξ A v = ((p.2.card : ℂ)⁻¹) • ∑ t ∈ p.2, (starRingEnd ℂ ((φ (ξ ⬝ᵥ t) : Circle) : ℂ)) • col t v := by
  have hd : ∃ p, AD φ col ξ A v p := ⟨p, hp⟩
  unfold av
  rw [dif_pos hd]
  obtain ⟨h1, -, h3, h4, h5, h6⟩ := hd.choose_spec
  obtain ⟨g1, -, g3, g4, g5, g6⟩ := hp
  exact avg_indep A _ _ h1 g1 _ _ h5 h6 g5 g6 _ (summand_inv φ col hca ξ v _ h3 h4)
    (summand_inv φ col hca ξ v _ g3 g4)

theorem circ_char (φ ψ : AddChar k Circle) (ξ η : Fin n → k) (x y : Fin n → k) :
    (φ (ξ ⬝ᵥ (x + y)))⁻¹ * ψ (η ⬝ᵥ (x + y)) = ((φ (ξ ⬝ᵥ x))⁻¹ * ψ (η ⬝ᵥ x)) * ((φ (ξ ⬝ᵥ y))⁻¹ * ψ (η ⬝ᵥ y)) := by
  rw [dotProduct_add, dotProduct_add, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

open Classical in
theorem av_eigen' (φ : AddChar k Circle) (hφ : Continuous φ) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hc0 : ∀ v, col 0 v = v) (hca : ∀ x y v, col (x + y) v = col x (col y v)) (hsm : ∀ v, IsOpen {x | col x v = v})
    (E : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (ψ : AddChar k Circle) (η : Fin n → k)
    (hE : ∀ x u w, E (col x u) w = ((ψ (η ⬝ᵥ x) : Circle) : ℂ) * E u w)
    (A : AddSubgroup (Fin n → k)) (hA : Lat A) (ξ : Fin n → k) (v w : V) :
    E (av φ col ξ A v) w = if ∀ a ∈ A, ψ (η ⬝ᵥ a) = φ (ξ ⬝ᵥ a) then E v w else 0 := by
  obtain ⟨p, hp⟩ := exists_AD φ hφ col hc0 hca hsm A hA {ξ} v
  have hp' := hp ξ (Finset.mem_singleton_self ξ)
  rw [av_eq' φ col hca A ξ v p hp']
  obtain ⟨h1, -, h3, h4, h5, h6⟩ := hp'
  let χ : (Fin n → k) → Circle := fun t => (φ (ξ ⬝ᵥ t))⁻¹ * ψ (η ⬝ᵥ t)
  have hexp : E (((p.2.card : ℂ)⁻¹) • ∑ t ∈ p.2, (starRingEnd ℂ ((φ (ξ ⬝ᵥ t) : Circle) : ℂ)) • col t v) w
      = ((p.2.card : ℂ)⁻¹ * ∑ t ∈ p.2, ((χ t : Circle) : ℂ)) * E v w := by
    simp only [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul, hE]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    simp only [χ, Circle.coe_mul, Circle.coe_inv_eq_conj]
    ring
  rw [hexp]
  by_cases hEv : E v w = 0
  · rw [hEv, mul_zero]
    split_ifs <;> rfl
  have hψ : ∀ a ∈ p.1, ψ (η ⬝ᵥ a) = 1 := by
    intro a ha
    have h := hE a v w
    rw [h3 a ha] at h
    have h' : (((ψ (η ⬝ᵥ a) : Circle) : ℂ) - 1) * E v w = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
    exact Circle.coe_eq_one.1 (sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hEv))
  have hχH : ∀ a ∈ p.1, χ a = 1 := by
    intro a ha
    simp only [χ, h4 a ha, hψ a ha, inv_one, mul_one]
  have hN := card_ne_zero A p.1 p.2 h6
  split_ifs with hc
  · have : ∑ t ∈ p.2, ((χ t : Circle) : ℂ) = p.2.card := by
      rw [Finset.sum_congr rfl (fun t ht => by
        simp only [χ, hc t (h5 t ht), inv_mul_cancel, Circle.coe_one] : ∀ t ∈ p.2, ((χ t : Circle) : ℂ) = 1)]
      simp
    rw [this, inv_mul_cancel₀ hN, one_mul]
  · simp only [not_forall] at hc
    obtain ⟨a, ha, hne⟩ := hc
    have hχa : χ a ≠ 1 := by
      intro h
      apply hne
      have := congrArg (fun z => φ (ξ ⬝ᵥ a) * z) h
      simpa [χ] using this
    rw [sum_circ_eq_zero A p.1 h1 p.2 h5 h6 χ (circ_char φ ψ ξ η) hχH a ha hχa, mul_zero, zero_mul]

theorem mulVec_ginv (g : GL (Fin n) k) (x : Fin n → k) :
    ((g : Matrix (Fin n) (Fin n) k)) *ᵥ (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

theorem ginv_mulVec (g : GL (Fin n) k) (x : Fin n → k) :
    (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) *ᵥ ((g : Matrix (Fin n) (Fin n) k) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

theorem mem_gmap (g : GL (Fin n) k) (A : AddSubgroup (Fin n → k)) (x : Fin n → k) :
    x ∈ gmap g A ↔ (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) *ᵥ x ∈ A := by
  simp only [gmap, AddSubgroup.mem_map, LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rwa [ginv_mulVec]
  · intro h
    exact ⟨_, h, mulVec_ginv g x⟩

theorem isOpen_gmap (g : GL (Fin n) k) (A : AddSubgroup (Fin n → k)) (hA : IsOpen (A : Set (Fin n → k))) :
    IsOpen (gmap g A : Set (Fin n → k)) := by
  have : (gmap g A : Set (Fin n → k)) =
      (fun x => (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) *ᵥ x) ⁻¹' (A : Set (Fin n → k)) := by
    ext x
    exact mem_gmap g A x
  rw [this]
  exact hA.preimage (continuous_const.matrix_mulVec continuous_id)

theorem lat_gmap' (g : GL (Fin n) k) (A : AddSubgroup (Fin n → k)) (hA : Lat A) : Lat (gmap g A) := by
  refine ⟨?_, isOpen_gmap g A hA.2⟩
  have : (gmap g A : Set (Fin n → k)) = (fun x => (g : Matrix (Fin n) (Fin n) k) *ᵥ x) '' (A : Set (Fin n → k)) := by
    simp only [gmap, AddSubgroup.coe_map]
    rfl
  rw [this]
  exact hA.1.image (continuous_const.matrix_mulVec continuous_id)

theorem dot_g (g : GL (Fin n) k) (ξ x : Fin n → k) :
    (ξ ᵥ* ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) ⬝ᵥ x =
      ξ ⬝ᵥ ((((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) *ᵥ x) := by
  rw [dotProduct_mulVec]

theorem av_conj' (φ : AddChar k Circle) (hφ : Continuous φ) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hc0 : ∀ v, col 0 v = v) (hca : ∀ x y v, col (x + y) v = col x (col y v)) (hsm : ∀ v, IsOpen {x | col x v = v})
    (gl : GL (Fin n) k →* (V →ₗ[ℂ] V))
    (hconj : ∀ g x v, gl g (col x v) = col ((g : Matrix (Fin n) (Fin n) k) *ᵥ x) (gl g v))
    (g : GL (Fin n) k) (A : AddSubgroup (Fin n → k)) (hA : Lat A) (ξ : Fin n → k) (v : V) :
    gl g (av φ col ξ A v) = av φ col (ξ ᵥ* ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (gmap g A) (gl g v) := by
  classical
  obtain ⟨p, hp⟩ := exists_AD φ hφ col hc0 hca hsm A hA {ξ} v
  have hp' := hp ξ (Finset.mem_singleton_self ξ)
  rw [av_eq' φ col hca A ξ v p hp']
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp'
  have hinj : Function.Injective (fun t : Fin n → k => (g : Matrix (Fin n) (Fin n) k) *ᵥ t) := by
    intro x y hxy
    have := congrArg (fun z => (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) *ᵥ z) hxy
    simpa only [ginv_mulVec] using this
  let q : AddSubgroup (Fin n → k) × Finset (Fin n → k) :=
    (gmap g p.1, p.2.image (fun t => (g : Matrix (Fin n) (Fin n) k) *ᵥ t))
  have hsub : ∀ a t, (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) *ᵥ (a - (g : Matrix (Fin n) (Fin n) k) *ᵥ t)
      = (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) *ᵥ a - t := by
    intro a t
    rw [Matrix.mulVec_sub, ginv_mulVec]
  have hq : AD φ col (ξ ᵥ* ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (gmap g A) (gl g v) q := by
    refine ⟨AddSubgroup.map_mono h1, isOpen_gmap g p.1 h2, ?_, ?_, ?_, ?_⟩
    · intro a ha
      rw [mem_gmap] at ha
      rw [← mulVec_ginv g a, ← hconj, h3 _ ha]
    · intro a ha
      rw [mem_gmap] at ha
      rw [dot_g]
      exact h4 _ ha
    · intro t ht
      obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.1 ht
      rw [mem_gmap, ginv_mulVec]
      exact h5 t₀ ht₀
    · intro a ha
      rw [mem_gmap] at ha
      obtain ⟨t₀, ⟨ht₀, hb⟩, huq⟩ := h6 _ ha
      refine ⟨(g : Matrix (Fin n) (Fin n) k) *ᵥ t₀, ⟨Finset.mem_image.2 ⟨t₀, ht₀, rfl⟩, ?_⟩, ?_⟩
      · rw [mem_gmap, hsub]
        exact hb
      · rintro t ⟨ht, hat⟩
        obtain ⟨t₁, ht₁, rfl⟩ := Finset.mem_image.1 ht
        rw [mem_gmap, hsub] at hat
        rw [huq t₁ ⟨ht₁, hat⟩]
  rw [av_eq' φ col hca (gmap g A) _ (gl g v) q hq]
  simp only [q]
  rw [Finset.card_image_of_injective _ hinj, Finset.sum_image (fun x _ y _ h => hinj h)]
  simp only [map_smul, map_sum, hconj, dot_g, ginv_mulVec]

end PositivityTheory.RgUd.Form.U.Lift2.AvA
end
end

section
noncomputable section

set_option linter.unusedSectionVars false

open Matrix

namespace PositivityTheory.RgUd.Form.U.Lift2.AvA

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}

theorem B_u (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (c : (Fin n → k) → ℂ) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (T : Finset (Fin n → k)) (v w : V) :
    B (∑ t ∈ T, c t • col t v) w = ∑ t ∈ T, c t * B (col t v) w := by
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem gram (φ : AddChar k Circle) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hc0 : ∀ v, col 0 v = v) (hca : ∀ x y v, col (x + y) v = col x (col y v))
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hBc : ∀ x v w, B (col x v) (col x w) = B v w)
    (A H : AddSubgroup (Fin n → k)) (hHA : H ≤ A) (T : Finset (Fin n → k))
    (hT : ∀ t ∈ T, t ∈ A) (hu : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H)
    (v : V) (hv : ∀ a ∈ H, col a v = v) (ξ ζ : Fin n → k) (hξ : ∀ a ∈ H, φ (ξ ⬝ᵥ a) = 1) :
    B (∑ t ∈ T, (starRingEnd ℂ ((φ (ξ ⬝ᵥ t) : Circle) : ℂ)) • col t v)
        (∑ r ∈ T, (starRingEnd ℂ ((φ (ζ ⬝ᵥ r) : Circle) : ℂ)) • col r v)
      = (∑ r ∈ T, ((((φ (ξ ⬝ᵥ r))⁻¹ * φ (ζ ⬝ᵥ r) : Circle)) : ℂ)) *
          ∑ t ∈ T, starRingEnd ℂ ((φ (ξ ⬝ᵥ t) : Circle) : ℂ) * B (col t v) v := by
  classical
  set f : (Fin n → k) → ℂ := fun x => starRingEnd ℂ ((φ (ξ ⬝ᵥ x) : Circle) : ℂ) * B (col x v) v with hf
  have hfH : ∀ x h, h ∈ H → f (x + h) = f x := by
    intro x h hh
    simp only [hf, dotProduct_add, AddChar.map_add_eq_mul, hξ h hh, mul_one, hca, hv h hh]
  have hsh : ∀ r ∈ T, ∑ t ∈ T, f (t + -r) = ∑ t ∈ T, f t := fun r hr =>
    sum_transl A H hHA T hT hu f hfH (-r) (A.neg_mem (hT r hr))
  have key : ∀ t r, B (col t v) (col r v) = B (col (t - r) v) v := by
    intro t r
    have h1 : col t v = col r (col (t - r) v) := by rw [← hca, add_sub_cancel]
    rw [h1, hBc]
  have hsplit : ∀ t r, starRingEnd ℂ ((φ (ξ ⬝ᵥ t) : Circle) : ℂ) =
      starRingEnd ℂ ((φ (ξ ⬝ᵥ (t + -r)) : Circle) : ℂ) * starRingEnd ℂ ((φ (ξ ⬝ᵥ r) : Circle) : ℂ) := by
    intro t r
    rw [← map_mul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← dotProduct_add, neg_add_cancel_right]
  conv_lhs =>
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smul, LinearMap.smul_apply,
      LinearMap.map_smulₛₗ, smul_eq_mul, starRingEnd_self_apply, RingHom.id_apply, key, Finset.mul_sum]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [← hsh r hr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [hsplit t r]
  simp only [hf, Circle.coe_mul, Circle.coe_inv_eq_conj, sub_eq_add_neg]
  ring

theorem gram_av (φ : AddChar k Circle) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hc0 : ∀ v, col 0 v = v) (hca : ∀ x y v, col (x + y) v = col x (col y v))
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hBc : ∀ x v w, B (col x v) (col x w) = B v w)
    (A : AddSubgroup (Fin n → k)) (ξ ζ : Fin n → k) (v : V)
    (p : AddSubgroup (Fin n → k) × Finset (Fin n → k)) (hpξ : AD φ col ξ A v p) (hpζ : AD φ col ζ A v p) :
    B (av φ col ξ A v) (av φ col ζ A v) =
      ((p.2.card : ℂ)⁻¹ * ∑ r ∈ p.2, ((((φ (ξ ⬝ᵥ r))⁻¹ * φ (ζ ⬝ᵥ r) : Circle)) : ℂ)) *
        B (av φ col ξ A v) v := by
  rw [av_eq' φ col hca A ξ v p hpξ, av_eq' φ col hca A ζ v p hpζ]
  obtain ⟨h1, -, h3, h4, h5, h6⟩ := hpξ
  rw [LinearMap.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ,
    gram φ col hc0 hca B hBc A p.1 h1 p.2 h5 h6 v h3 ξ ζ h4, LinearMap.smul_apply, B_u]
  simp only [smul_eq_mul, map_inv₀, map_natCast]
  ring

theorem bessel_abs (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hB : Psd B) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (w : ι → V) (v : V)
    (hw : ∀ i ∈ s, ∀ j ∈ s, B (w i) (w j) = if i = j then B (w i) v else 0) :
    ∑ i ∈ s, (B (w i) v).re ≤ (B v v).re := by
  classical
  have hWW : B (∑ i ∈ s, w i) (∑ i ∈ s, w i) = ∑ i ∈ s, B (w i) v := by
    simp only [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_congr rfl fun d hd => hw d hd i hi]
    simp [hi]
  have hWv : B (∑ i ∈ s, w i) v = ∑ i ∈ s, B (w i) v := by
    simp only [map_sum, LinearMap.sum_apply]
  have hvW : B v (∑ i ∈ s, w i) = starRingEnd ℂ (∑ i ∈ s, B (w i) v) := by
    rw [hB.1 (∑ i ∈ s, w i) v, hWv]
  have h0 := hB.2 (v - ∑ i ∈ s, w i)
  simp only [map_sub, LinearMap.sub_apply, hWW, hWv, hvW, Complex.sub_re, Complex.conj_re] at h0
  rw [← Complex.re_sum]
  linarith

theorem av_bessel' (φ : AddChar k Circle) (hφ : Continuous φ) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hc0 : ∀ v, col 0 v = v) (hca : ∀ x y v, col (x + y) v = col x (col y v)) (hsm : ∀ v, IsOpen {x | col x v = v})
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hB : Psd B) (hBc : ∀ x v w, B (col x v) (col x w) = B v w)
    (A : AddSubgroup (Fin n → k)) (hA : Lat A) (s : Finset (Fin n → k))
    (hs : ∀ ξ ∈ s, ∀ ξ' ∈ s, ξ - ξ' ∈ perp φ A → ξ = ξ') (v : V) :
    ∑ ξ ∈ s, (B (av φ col ξ A v) v).re ≤ (B v v).re := by
  classical
  obtain ⟨p, hp⟩ := exists_AD φ hφ col hc0 hca hsm A hA s v
  refine bessel_abs B hB s (fun ξ => av φ col ξ A v) v ?_
  intro ξ hξ ξ' hξ'
  show B (av φ col ξ A v) (av φ col ξ' A v) = if ξ = ξ' then B (av φ col ξ A v) v else 0
  rw [gram_av φ col hc0 hca B hBc A ξ ξ' v p (hp ξ hξ) (hp ξ' hξ')]
  have hcard := card_ne_zero A p.1 p.2 (hp ξ hξ).2.2.2.2.2
  split_ifs with hxx
  · subst hxx
    simp only [inv_mul_cancel, Circle.coe_one, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [inv_mul_cancel₀ hcard, one_mul]
  · have hz : ∑ r ∈ p.2, ((((φ (ξ ⬝ᵥ r))⁻¹ * φ (ξ' ⬝ᵥ r) : Circle)) : ℂ) = 0 := by
      obtain ⟨h1, -, -, h4, h5, h6⟩ := hp ξ hξ
      obtain ⟨-, -, -, h4', -, -⟩ := hp ξ' hξ'
      by_contra hne
      apply hxx
      apply hs ξ hξ ξ' hξ'
      show ∀ a ∈ A, φ ((ξ - ξ') ⬝ᵥ a) = 1
      intro a ha
      by_contra hna
      apply hne
      refine sum_circ_eq_zero A p.1 h1 p.2 h5 h6 (fun r => (φ (ξ ⬝ᵥ r))⁻¹ * φ (ξ' ⬝ᵥ r))
        (fun x y => circ_char φ φ ξ ξ' x y) (fun h hh => by simp [h4 h hh, h4' h hh]) a ha ?_
      intro hχ
      apply hna
      have e : φ (ξ ⬝ᵥ a) = φ (ξ' ⬝ᵥ a) := inv_mul_eq_one.mp hχ
      rw [sub_dotProduct, AddChar.map_sub_eq_div, e, div_self']
    rw [hz, mul_zero, zero_mul]

end PositivityTheory.RgUd.Form.U.Lift2.AvA
end
end

section
noncomputable section

open Matrix GlobalTheory.SplitWeil GlobalTheory.BZMir
open scoped Topology

namespace PositivityTheory.RgUd.Form.U.Lift2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}

theorem lat_gmap (g : GL (Fin n) k) (A : AddSubgroup (Fin n → k)) (hA : Lat A) : Lat (gmap g A) :=
  AvA.lat_gmap' g A hA

theorem av_conj (φ : AddChar k Circle) (hφ : Continuous φ) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hc0 : ∀ v, col 0 v = v) (hca : ∀ x y v, col (x + y) v = col x (col y v)) (hsm : ∀ v, IsOpen {x | col x v = v})
    (gl : GL (Fin n) k →* (V →ₗ[ℂ] V))
    (hconj : ∀ g x v, gl g (col x v) = col ((g : Matrix (Fin n) (Fin n) k) *ᵥ x) (gl g v))
    (g : GL (Fin n) k) (A : AddSubgroup (Fin n → k)) (hA : Lat A) (ξ : Fin n → k) (v : V) :
    gl g (av φ col ξ A v) = av φ col (ξ ᵥ* ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (gmap g A) (gl g v) :=
  AvA.av_conj' φ hφ col hc0 hca hsm gl hconj g A hA ξ v

theorem av_bessel (φ : AddChar k Circle) (hφ : Continuous φ) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hc0 : ∀ v, col 0 v = v) (hca : ∀ x y v, col (x + y) v = col x (col y v)) (hsm : ∀ v, IsOpen {x | col x v = v})
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hB : Psd B) (hBc : ∀ x v w, B (col x v) (col x w) = B v w)
    (A : AddSubgroup (Fin n → k)) (hA : Lat A) (s : Finset (Fin n → k))
    (hs : ∀ ξ ∈ s, ∀ ξ' ∈ s, ξ - ξ' ∈ perp φ A → ξ = ξ') (v : V) :
    ∑ ξ ∈ s, (B (av φ col ξ A v) v).re ≤ (B v v).re :=
  AvA.av_bessel' φ hφ col hc0 hca hsm B hB hBc A hA s hs v

end PositivityTheory.RgUd.Form.U.Lift2
end
end

section
noncomputable section

open Matrix MeasureTheory GlobalTheory.SplitWeil GlobalTheory.BZMir Filter
open scoped Topology ENNReal NNReal

namespace PositivityTheory.RgUd.Form.U.Lift2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Lattices

variable (ψ : AddChar k Circle) {n : ℕ}

theorem perp_open (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {A : AddSubgroup (Fin n → k)} (hA : Lat A) :
    IsOpen (perp ψ A : Set (Fin n → k)) := (GlobalTheory.T.annihilator_open_compact k ψ hψ hψ1 n A hA.1 hA.2).1

theorem perp_compact (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {A : AddSubgroup (Fin n → k)} (hA : Lat A) :
    IsCompact (perp ψ A : Set (Fin n → k)) := (GlobalTheory.T.annihilator_open_compact k ψ hψ hψ1 n A hA.1 hA.2).2

theorem perp_anti {A A' : AddSubgroup (Fin n → k)} (h : A ≤ A') : perp ψ A' ≤ perp ψ A :=
  fun _ hξ a ha => hξ a (h ha)

theorem perp_relIndex (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {A₀ A : AddSubgroup (Fin n → k)} (h₀ : Lat A₀) (h : Lat A)
    (hle : A₀ ≤ A) : (perp ψ A).relIndex (perp ψ A₀) = A₀.relIndex A :=
  GlobalTheory.T.relIndex_annihilators_duality k ψ hψ hψ1 n A₀ A (perp ψ A₀) (perp ψ A) h₀.1 h₀.2 h.1 h.2 hle (fun _ => Iff.rfl) (fun _ => Iff.rfl)

theorem relIndex_ne_zero_of_lat {A₀ A : AddSubgroup (Fin n → k)} (h₀ : Lat A₀) (h : Lat A) : A₀.relIndex A ≠ 0 := by
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp h.1
  have ho : IsOpen ((A₀.addSubgroupOf A : AddSubgroup A) : Set A) := h₀.2.preimage continuous_subtype_val
  haveI := AddSubgroup.quotient_finite_of_isOpen (A₀.addSubgroupOf A) ho
  exact AddSubgroup.index_ne_zero_of_finite

theorem lat_over {K : Set (Fin n → k)} (hK : IsCompact K) : ∃ A : AddSubgroup (Fin n → k), Lat A ∧ K ⊆ A := by
  obtain ⟨A, h1, h2, h3⟩ := GlobalTheory.T.exists_open_compact_lattice_containing k n K hK
  exact ⟨A, ⟨h1, h2⟩, h3⟩

theorem lat_shrink (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {U : Set (Fin n → k)} (hU : U ∈ 𝓝 (0 : Fin n → k)) :
    ∃ A : AddSubgroup (Fin n → k), Lat A ∧ (perp ψ A : Set _) ⊆ U := by
  obtain ⟨A, h1, h2, h3⟩ := GlobalTheory.T.lattice_annihilator_within_nhds k ψ hψ hψ1 n U hU
  exact ⟨A, ⟨h1, h2⟩, h3⟩

theorem lat_sup {A A' : AddSubgroup (Fin n → k)} (h : Lat A) (h' : Lat A') : ∃ A'', Lat A'' ∧ A ≤ A'' ∧ A' ≤ A'' := by
  obtain ⟨B, hB, hB'⟩ := lat_over (h.1.union h'.1)
  exact ⟨B, hB, fun x hx => hB' (Or.inl hx), fun x hx => hB' (Or.inr hx)⟩

end Lattices

section Forms

variable {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

abbrev md (g : GL (Fin (m + 1)) k) : ℝ := nabs k (Matrix.GeneralLinearGroup.det g)

theorem md_pos (g : GL (Fin (m + 1)) k) : 0 < md g := NNReal.coe_pos.mpr distribHaarChar_pos

theorem md_mul (g h : GL (Fin (m + 1)) k) : md (g * h) = md g * md h := by
  simp [md, nabs, map_mul]

theorem md_inv (g : GL (Fin (m + 1)) k) : md g⁻¹ = (md g)⁻¹ := by
  simp [md, nabs, map_inv]

theorem md_one : md (1 : GL (Fin (m + 1)) k) = 1 := by
  simp [md, nabs]

theorem xz_eq (m : ℕ) : (xz m : Fin (m + 1) → k) = eLast k m := rfl

variable (gl : GL (Fin (m + 1)) k →* (V →ₗ[ℂ] V)) (s : ℝ) (C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)

def Ct (g : GL (Fin (m + 1)) k) : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ :=
  (((md g ^ (s + 1) : ℝ) : ℂ)) • (C.compl₂ (gl g⁻¹)).comp (gl g⁻¹)

theorem Ct_apply (g : GL (Fin (m + 1)) k) (v w : V) :
    Ct gl s C g v w = ((md g ^ (s + 1) : ℝ) : ℂ) * C (gl g⁻¹ v) (gl g⁻¹ w) := by
  simp [Ct]

open Classical in

def sect (ξ : Fin (m + 1) → k) : GL (Fin (m + 1)) k :=
  if h : ξ = 0 then 1 else (Classical.choose (GlobalTheory.T.exists_GL_last_basis_vecMul_eq k m ξ h))⁻¹

theorem sect_spec {ξ : Fin (m + 1) → k} (h : ξ ≠ 0) :
    xz m ᵥ* (((sect ξ)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ := by
  rw [sect, dif_neg h, inv_inv]
  exact Classical.choose_spec (GlobalTheory.T.exists_GL_last_basis_vecMul_eq k m ξ h)

open Classical in

def Df (ξ : Fin (m + 1) → k) : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ := if ξ = 0 then 0 else Ct gl s C (sect ξ)

theorem Df_zero : Df gl s C (0 : Fin (m + 1) → k) = 0 := by
  simp [Df]

variable {gl s C}

theorem Ct_congr (hC : ∀ p ∈ Mir k m, ∀ v w, C (gl p v) (gl p w) = ((md p ^ (s + 1) : ℝ) : ℂ) * C v w)
    {g h : GL (Fin (m + 1)) k}
    (hgh : xz m ᵥ* ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) =
      xz m ᵥ* ((h⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) :
    Ct gl s C g = Ct gl s C h := by
  set p := h⁻¹ * g with hp_def
  have hp : p⁻¹ ∈ Mir k m := by
    show vecMul (eLast k m) ((p⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = eLast k m
    rw [hp_def, _root_.mul_inv_rev, inv_inv, Units.val_mul, ← vecMul_vecMul, ← xz_eq, hgh, vecMul_vecMul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, vecMul_one]
  have hg : g = h * p := by rw [hp_def, mul_inv_cancel_left]
  have hgi : g⁻¹ = p⁻¹ * h⁻¹ := by rw [hg, _root_.mul_inv_rev]
  refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
  rw [Ct_apply, Ct_apply, hgi, map_mul, Module.End.mul_apply, Module.End.mul_apply, hC _ hp, ← mul_assoc]
  congr 1
  rw [hg, md_mul, md_inv, ← Complex.ofReal_mul, Real.mul_rpow (md_pos h).le (md_pos p).le,
    Real.inv_rpow (md_pos p).le, mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos (md_pos p) _).ne', mul_one]

theorem Df_eq (hC : ∀ p ∈ Mir k m, ∀ v w, C (gl p v) (gl p w) = ((md p ^ (s + 1) : ℝ) : ℂ) * C v w)
    {ξ : Fin (m + 1) → k} (hξ : ξ ≠ 0) {g : GL (Fin (m + 1)) k}
    (hg : xz m ᵥ* ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ) :
    Df gl s C ξ = Ct gl s C g := by
  rw [Df, if_neg hξ]
  exact Ct_congr hC ((sect_spec hξ).trans hg.symm)

theorem Df_xz (hC : ∀ p ∈ Mir k m, ∀ v w, C (gl p v) (gl p w) = ((md p ^ (s + 1) : ℝ) : ℂ) * C v w) (v w : V) :
    Df gl s C (xz m) v w = C v w := by
  have h0 : (xz m : Fin (m + 1) → k) ≠ 0 := by
    intro h
    have := congrFun h (Fin.last m)
    simp [xz] at this
  rw [Df_eq hC h0 (g := 1) (by simp), Ct_apply]
  simp [md_one]

end Forms

section Forms2

variable {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {ψ : AddChar k Circle}
  {col : (Fin (m + 1) → k) → V →ₗ[ℂ] V} {gl : GL (Fin (m + 1)) k →* (V →ₗ[ℂ] V)} {s : ℝ} {C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

theorem circ_mul_conj (z : Circle) : (z : ℂ) * starRingEnd ℂ (z : ℂ) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]
  norm_num

theorem Ct_herm (hCp : Psd C) (g : GL (Fin (m + 1)) k) (v w : V) :
    Ct gl s C g w v = starRingEnd ℂ (Ct gl s C g v w) := by
  rw [Ct_apply, Ct_apply, hCp.1, map_mul, Complex.conj_ofReal]

theorem Ct_re_nonneg (hCp : Psd C) (g : GL (Fin (m + 1)) k) (v : V) : 0 ≤ (Ct gl s C g v v).re := by
  rw [Ct_apply, Complex.re_ofReal_mul]
  exact mul_nonneg (Real.rpow_nonneg (md_pos g).le _) (hCp.2 _)

theorem Df_herm (hCp : Psd C) (ξ : Fin (m + 1) → k) (v w : V) :
    Df gl s C ξ w v = starRingEnd ℂ (Df gl s C ξ v w) := by
  by_cases h : ξ = 0
  · subst h
    simp [Df_zero]
  · simp only [Df, if_neg h]
    exact Ct_herm hCp _ _ _

theorem Df_re_nonneg (hCp : Psd C) (ξ : Fin (m + 1) → k) (v : V) : 0 ≤ (Df gl s C ξ v v).re := by
  by_cases h : ξ = 0
  · subst h
    simp [Df_zero]
  · simp only [Df, if_neg h]
    exact Ct_re_nonneg hCp _ _

theorem Ct_col (hS : Setup col gl) (hCc : ∀ x v w, C (col x v) w = ((ψ (xz m ⬝ᵥ x) : Circle) : ℂ) * C v w)
    (g : GL (Fin (m + 1)) k) (x : Fin (m + 1) → k) (v w : V) :
    Ct gl s C g (col x v) w =
      ((ψ ((xz m ᵥ* ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) ⬝ᵥ x) : Circle) : ℂ) *
        Ct gl s C g v w := by
  rw [Ct_apply, Ct_apply, hS.conj, hCc, dotProduct_mulVec]
  ring

variable (hS : Setup col gl) (hCp : Psd C)
  (hCc : ∀ x v w, C (col x v) w = ((ψ (xz m ⬝ᵥ x) : Circle) : ℂ) * C v w)
  (hC : ∀ p ∈ Mir k m, ∀ v w, C (gl p v) (gl p w) = ((md p ^ (s + 1) : ℝ) : ℂ) * C v w)
include hS hCc hC

theorem Df_col (ξ x : Fin (m + 1) → k) (v w : V) :
    Df gl s C ξ (col x v) w = ((ψ (ξ ⬝ᵥ x) : Circle) : ℂ) * Df gl s C ξ v w := by
  by_cases h : ξ = 0
  · subst h
    simp [Df_zero]
  · rw [Df_eq hC h (sect_spec h), Ct_col hS hCc, sect_spec h]

include hCp

theorem Df_col_right (ξ x : Fin (m + 1) → k) (v w : V) :
    Df gl s C ξ v (col x w) = starRingEnd ℂ ((ψ (ξ ⬝ᵥ x) : Circle) : ℂ) * Df gl s C ξ v w := by
  rw [Df_herm hCp, Df_col hS hCc hC, map_mul, ← Df_herm hCp]

theorem form_column_invariant (ξ x : Fin (m + 1) → k) (v w : V) : Df gl s C ξ (col x v) (col x w) = Df gl s C ξ v w := by
  rw [Df_col_right hS hCp hCc hC, Df_col hS hCc hC, ← mul_assoc, mul_comm (starRingEnd ℂ _), circ_mul_conj, one_mul]

omit hCp hCc in
theorem Df_gl {ξ : Fin (m + 1) → k} (hξ : ξ ≠ 0) (g : GL (Fin (m + 1)) k) (v w : V) :
    Df gl s C ξ (gl g v) (gl g w) =
      ((md g ^ (s + 1) : ℝ) : ℂ) * Df gl s C (ξ ᵥ* (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) v w := by
  have hξg : ξ ᵥ* (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ≠ 0 := by
    intro h0
    apply hξ
    have := congrArg (fun x => x ᵥ* ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) h0
    simpa [vecMul_vecMul, ← Units.val_mul] using this
  have hτ : xz m ᵥ* (((g⁻¹ * sect ξ)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) =
      ξ ᵥ* (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) := by
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← vecMul_vecMul, sect_spec hξ]
  rw [Df_eq hC hξ (sect_spec hξ), Df_eq hC hξg hτ, Ct_apply, Ct_apply, ← Module.End.mul_apply, ← Module.End.mul_apply,
    ← map_mul, _root_.mul_inv_rev (g⁻¹) (sect ξ), inv_inv, ← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  rw [md_mul, md_inv, Real.mul_rpow (inv_nonneg.mpr (md_pos g).le) (md_pos (sect ξ)).le, Real.inv_rpow (md_pos g).le,
    ← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos (md_pos g) _).ne', one_mul]

omit hS hCc in
theorem Df_ker (Y : Submodule ℂ V) (hY : ∀ g, ∀ y ∈ Y, gl g y ∈ Y) (hCY : ∀ y ∈ Y, ∀ w, C y w = 0)
    (ξ : Fin (m + 1) → k) {y : V} (hy : y ∈ Y) (w : V) : Df gl s C ξ y w = 0 := by
  by_cases h : ξ = 0
  · subst h
    simp [Df_zero]
  · simp only [Df, if_neg h]
    rw [Ct_apply, hCY _ (hY _ _ hy), mul_zero]

omit hCp hCc in

theorem Df_loc {ζ : Fin (m + 1) → k} (hζ : ζ ≠ 0) (v w : V) : ∀ᶠ ξ in 𝓝 ζ, Df gl s C ξ v w = Df gl s C ζ v w := by
  obtain ⟨N, hNo, hζN, f, hf, hf1, hfN⟩ := GlobalTheory.T.local_continuous_section_vecMul_orbit k (m + 1) ζ hζ
  have hH : {h : GL (Fin (m + 1)) k | gl h v = v} ∩ {h | gl h w = w} ∩ {h | md h = 1} ∈ 𝓝 (1 : GL (Fin (m + 1)) k) := by
    refine Filter.inter_mem (Filter.inter_mem ?_ ?_) ?_
    · exact (hS.smooth_gl v).mem_nhds (by simp)
    · exact (hS.smooth_gl w).mem_nhds (by simp)
    · filter_upwards [GlobalTheory.T.eventually_haar_det_eq_one_near_one k (m + 1)] with h hh
      simp [md, nabs, hh]
  have hfc : ContinuousAt f ζ := hf.continuousAt (hNo.mem_nhds hζN)
  have hpre : f ⁻¹' ({h : GL (Fin (m + 1)) k | gl h v = v} ∩ {h | gl h w = w} ∩ {h | md h = 1}) ∈ 𝓝 ζ :=
    hfc (by rw [hf1]; exact hH)
  filter_upwards [hNo.mem_nhds hζN, hpre] with ξ hξN hξH
  obtain ⟨⟨hv, hw⟩, hd⟩ := hξH
  have hξ : ζ ᵥ* (f ξ : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ := hfN ξ hξN
  have hξ0 : ξ ≠ 0 := by
    intro h0
    apply hζ
    have := congrArg (fun x => x ᵥ* (((f ξ)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) (hξ.trans h0)
    simpa [vecMul_vecMul, ← Units.val_mul] using this
  have hτ : xz m ᵥ* ((((f ξ)⁻¹ * sect ζ)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ := by
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← vecMul_vecMul, sect_spec hζ, hξ]
  rw [Df_eq hC hξ0 hτ, Df_eq hC hζ (sect_spec hζ), Ct_apply, Ct_apply, _root_.mul_inv_rev, inv_inv, map_mul,
    Module.End.mul_apply, Module.End.mul_apply, hv, hw, md_mul, md_inv, hd, inv_one, one_mul]

end Forms2

section Meas

local instance instMeasK : MeasurableSpace k := borel k
local instance instBorelK : BorelSpace k := ⟨rfl⟩
local instance instSCK : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k

variable {m : ℕ} (ψ : AddChar k Circle) (ν : Measure (Fin (m + 1) → k)) [ν.IsAddHaarMeasure]

theorem meas_perp_index (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {A₀ A : AddSubgroup (Fin (m + 1) → k)} (h₀ : Lat A₀) (h : Lat A)
    (hle : A₀ ≤ A) : ν (perp ψ A₀) = (A₀.relIndex A : ℝ≥0∞) * ν (perp ψ A) := by
  have := GlobalTheory.T.haar_measure_subgroup_relIndex_mul (Fin (m + 1) → k) ν (perp ψ A) (perp ψ A₀) (perp_anti ψ hle)
    (perp_open ψ hψ hψ1 h).measurableSet (by rw [perp_relIndex ψ hψ hψ1 h₀ h hle]; exact relIndex_ne_zero_of_lat h₀ h)
  rw [this, perp_relIndex ψ hψ hψ1 h₀ h hle]

theorem meas_perp_lt_top (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {A : AddSubgroup (Fin (m + 1) → k)} (h : Lat A) :
    ν (perp ψ A) < ∞ := (perp_compact ψ hψ hψ1 h).measure_lt_top

theorem meas_perp_ne_zero (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {A : AddSubgroup (Fin (m + 1) → k)} (h : Lat A) :
    ν (perp ψ A) ≠ 0 := (perp_open ψ hψ hψ1 h).measure_ne_zero ν ⟨0, (perp ψ A).zero_mem⟩

def gT (g : GL (Fin (m + 1)) k) : GL (Fin (m + 1)) k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k)ᵀ)
    (by rw [det_transpose]; exact (Matrix.isUnits_det_units g).ne_zero)

theorem md_gT (g : GL (Fin (m + 1)) k) : md (gT g) = md g := by
  have : Matrix.GeneralLinearGroup.det (gT g) = Matrix.GeneralLinearGroup.det g := by
    ext
    simp [gT, Matrix.GeneralLinearGroup.mkOfDetNeZero, det_transpose]
  simp only [md, this]

theorem integral_vecMul (f : (Fin (m + 1) → k) → ℂ) (g : GL (Fin (m + 1)) k) :
    ∫ ξ, f (ξ ᵥ* (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) ∂ν = ((md g)⁻¹ : ℝ) * ∫ ξ, f ξ ∂ν := by
  have h := GlobalTheory.InertLagChar.haarChar_det_mul_integral_comp_mulVec_localField k (m + 1) _ BorelSpace.measurable_eq ν inferInstance (gT g) f
  have h2 : ∀ y : Fin (m + 1) → k, ((gT g : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ y =
      y ᵥ* (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) := by
    intro y
    simp [gT, Matrix.GeneralLinearGroup.mkOfDetNeZero, mulVec_transpose]
  simp_rw [h2] at h
  have hmd : ((distribHaarChar k (Matrix.GeneralLinearGroup.det (gT g)) : ℝ≥0) : ℝ) = md g := by
    rw [← md_gT]; rfl
  rw [← h, ← mul_assoc, ← Complex.ofReal_mul, hmd, inv_mul_cancel₀ (md_pos g).ne', Complex.ofReal_one, one_mul]

theorem perp_gmap (g : GL (Fin (m + 1)) k) (A : AddSubgroup (Fin (m + 1) → k)) (ξ : Fin (m + 1) → k) :
    ξ ∈ perp ψ (gmap g A) ↔ ξ ᵥ* (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ∈ perp ψ A := by
  simp only [mem_perp, gmap, AddSubgroup.mem_map, forall_exists_index, and_imp]
  constructor
  · intro h a ha
    rw [← dotProduct_mulVec]
    exact h _ a ha (by simp)
  · rintro h _ a ha rfl
    simp only [LinearMap.toAddMonoidHom_coe, mulVecLin_apply]
    rw [dotProduct_mulVec]
    exact h a ha

theorem meas_perp_gmap (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (g : GL (Fin (m + 1)) k) {A : AddSubgroup (Fin (m + 1) → k)}
    (hA : Lat A) : (ν (perp ψ (gmap g A))).toReal = (md g)⁻¹ * (ν (perp ψ A)).toReal := by
  have hmeas : MeasurableSet (perp ψ A : Set (Fin (m + 1) → k)) := (perp_open ψ hψ hψ1 hA).measurableSet
  have hmeas' : MeasurableSet (perp ψ (gmap g A) : Set (Fin (m + 1) → k)) :=
    (perp_open ψ hψ hψ1 (lat_gmap g A hA)).measurableSet
  have h := integral_vecMul ν ((perp ψ A : Set (Fin (m + 1) → k)).indicator fun _ => (1 : ℂ)) g
  have hset : (fun ξ => (perp ψ A : Set (Fin (m + 1) → k)).indicator (fun _ => (1 : ℂ))
      (ξ ᵥ* (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k))) =
      (perp ψ (gmap g A) : Set (Fin (m + 1) → k)).indicator fun _ => (1 : ℂ) := by
    funext ξ
    by_cases hξ : ξ ∈ perp ψ (gmap g A)
    · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem ((perp_gmap ψ g A ξ).1 hξ)]
    · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem (fun h => hξ ((perp_gmap ψ g A ξ).2 h))]
  rw [hset, integral_indicator_const _ hmeas', integral_indicator_const _ hmeas] at h
  simp only [Complex.real_smul, mul_one] at h
  exact_mod_cast h

end Meas

section Psd

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem psd_norm_le (E : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hE : Psd E) (v w : V) : ‖E v w‖ ≤ ((E v v).re + (E w w).re) / 2 := by
  set c := E v w with hc
  by_cases h0 : c = 0
  · rw [h0, norm_zero]
    exact div_nonneg (add_nonneg (hE.2 v) (hE.2 w)) zero_le_two
  have hn : (‖c‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr h0
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = c / (‖c‖ : ℂ) := ⟨_, rfl⟩
  have h := hE.2 (v - z • w)
  have hwv : E w v = starRingEnd ℂ c := hE.1 v w
  have e1 : starRingEnd ℂ z * c = (‖c‖ : ℂ) := by
    rw [hz, map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    field_simp
  have e2 : z * starRingEnd ℂ c = (‖c‖ : ℂ) := by
    have := congrArg (starRingEnd ℂ) e1
    rwa [map_mul, Complex.conj_conj, Complex.conj_ofReal] at this
  have e3 : z * starRingEnd ℂ z = 1 := by
    rw [hz, map_div₀, Complex.conj_ofReal, div_mul_div_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rw [← pow_two]
    exact div_self (pow_ne_zero 2 (by exact_mod_cast hn))
  have hexp : E (v - z • w) (v - z • w) = E v v - (‖c‖ : ℂ) - (‖c‖ : ℂ) + E w w := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul]
    rw [← hc, hwv]
    linear_combination -e1 - e2 + (E w w) * e3
  rw [hexp] at h
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re] at h
  linarith

end Psd

section Main

local instance measurableSpaceSecondLift : MeasurableSpace k := borel k
local instance borelSpaceSecondLift : BorelSpace k := ⟨rfl⟩
local instance instSCK2 : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k

theorem gmap_gmap_inv {n : ℕ} (g : GL (Fin n) k) (M : AddSubgroup (Fin n → k)) : gmap g (gmap g⁻¹ M) = M := by
  ext x
  simp only [gmap, AddSubgroup.mem_map, LinearMap.toAddMonoidHom_coe, mulVecLin_apply]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    rwa [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  · intro hx
    refine ⟨((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ x, ⟨x, hx, rfl⟩, ?_⟩
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

variable {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
  {col : (Fin (m + 1) → k) → V →ₗ[ℂ] V} {gl : GL (Fin (m + 1)) k →* (V →ₗ[ℂ] V)} (hS : Setup col gl) {s : ℝ}
  {B B' C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {A₀ : AddSubgroup (Fin (m + 1) → k)} (hA₀ : Lat A₀)
  (hBp : Psd B) (hBc : ∀ x v w, B (col x v) (col x w) = B v w)
  (hBg : ∀ g v w, B (gl g v) (gl g w) = ((md g ^ s : ℝ) : ℂ) * B v w)
  (hD : IsD ψ col A₀ B B') (hCp : Psd C) (hCc : ∀ x v w, C (col x v) w = ((ψ (xz m ⬝ᵥ x) : Circle) : ℂ) * C v w)
  (hC : ∀ p ∈ Mir k m, ∀ v w, C (gl p v) (gl p w) = ((md p ^ (s + 1) : ℝ) : ℂ) * C v w)
  (hCB : ∀ v, (C v v).re ≤ (B' v v).re)
  {ν : Measure (Fin (m + 1) → k)} [ν.IsAddHaarMeasure] (hν : ν (perp ψ A₀) = 1)

include hψ hψ1 hS hA₀ hBg hD hCp hC hCB hν in

theorem locB {ζ : Fin (m + 1) → k} (hζ : ζ ≠ 0) (v : V) :
    ∃ M₀ : AddSubgroup (Fin (m + 1) → k), Lat M₀ ∧ ∀ ξ, ξ - ζ ∈ perp ψ M₀ →
      Df gl s C ξ v v = Df gl s C ζ v v ∧ ∀ M, Lat M → M₀ ≤ M →
        (Df gl s C ζ v v).re * (ν (perp ψ M)).toReal ≤ (B (av ψ col ξ M v) v).re := by
  obtain ⟨A₁, hA₁, hA₀₁, hA₁s⟩ := hD (gl (sect ζ)⁻¹ v) (gl (sect ζ)⁻¹ v)
  obtain ⟨N, hNo, hζN, f, hf, hf1, hfN⟩ := GlobalTheory.T.local_continuous_section_vecMul_orbit k (m + 1) ζ hζ
  have hH : {h : GL (Fin (m + 1)) k | gl h v = v} ∩ {h | md h = 1} ∈ 𝓝 (1 : GL (Fin (m + 1)) k) := by
    refine Filter.inter_mem ((hS.smooth_gl v).mem_nhds (by simp)) ?_
    filter_upwards [GlobalTheory.T.eventually_haar_det_eq_one_near_one k (m + 1)] with h hh
    simp [md, nabs, hh]
  have hfc : ContinuousAt f ζ := hf.continuousAt (hNo.mem_nhds hζN)
  have hW : N ∩ f ⁻¹' ({h : GL (Fin (m + 1)) k | gl h v = v} ∩ {h | md h = 1}) ∈ 𝓝 ζ :=
    Filter.inter_mem (hNo.mem_nhds hζN) (hfc (by rw [hf1]; exact hH))
  have hU : (fun η => ζ + η) ⁻¹' (N ∩ f ⁻¹' ({h : GL (Fin (m + 1)) k | gl h v = v} ∩ {h | md h = 1})) ∈
      𝓝 (0 : Fin (m + 1) → k) := by
    have : Filter.Tendsto (fun η : Fin (m + 1) → k => ζ + η) (𝓝 0) (𝓝 ζ) := by
      simpa using (continuous_add_left ζ).tendsto (0 : Fin (m + 1) → k)
    exact this hW
  obtain ⟨M₁, hM₁, hM₁U⟩ := lat_shrink ψ hψ hψ1 hU
  have hSc : IsCompact ((fun η => ζ + η) '' (perp ψ M₁ : Set (Fin (m + 1) → k))) :=
    (perp_compact ψ hψ hψ1 hM₁).image (continuous_const.add continuous_id)
  have hSN : (fun η => ζ + η) '' (perp ψ M₁ : Set (Fin (m + 1) → k)) ⊆ N := by
    rintro _ ⟨η, hη, rfl⟩
    exact (hM₁U hη).1
  have hSH : ∀ ξ ∈ (fun η => ζ + η) '' (perp ψ M₁ : Set (Fin (m + 1) → k)), gl (f ξ) v = v ∧ md (f ξ) = 1 := by
    rintro _ ⟨η, hη, rfl⟩
    exact (hM₁U hη).2
  have hKc : IsCompact ((fun p : (Fin (m + 1) → k) × (Fin (m + 1) → k) =>
      ((((f p.1)⁻¹ * sect ζ : GL (Fin (m + 1)) k)) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ p.2) ''
        (((fun η => ζ + η) '' (perp ψ M₁ : Set (Fin (m + 1) → k))) ×ˢ (A₁ : Set (Fin (m + 1) → k)))) := by
    refine (hSc.prod hA₁.1).image_of_continuousOn ?_
    have h1 : ContinuousOn (fun p : (Fin (m + 1) → k) × (Fin (m + 1) → k) => f p.1)
        (((fun η => ζ + η) '' (perp ψ M₁ : Set (Fin (m + 1) → k))) ×ˢ (A₁ : Set (Fin (m + 1) → k))) :=
      (hf.mono hSN).comp continuous_fst.continuousOn (fun p hp => hp.1)
    have h2 := Units.continuous_val.comp_continuousOn (h1.inv.mul continuousOn_const
      (g := fun _ => (sect ζ : GL (Fin (m + 1)) k)))
    exact (continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn (h2.prodMk continuous_snd.continuousOn)
  obtain ⟨M₂, hM₂, hKM₂⟩ := lat_over hKc
  obtain ⟨M₀, hM₀, hM₁M₀, hM₂M₀⟩ := lat_sup hM₁ hM₂
  refine ⟨M₀, hM₀, fun ξ hξ => ?_⟩
  have hξS : ξ ∈ (fun η => ζ + η) '' (perp ψ M₁ : Set (Fin (m + 1) → k)) :=
    ⟨ξ - ζ, perp_anti ψ hM₁M₀ hξ, by abel⟩
  obtain ⟨hhv, hhd⟩ := hSH ξ hξS
  have hζh : ζ ᵥ* (f ξ : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ := hfN ξ (hSN hξS)
  have hg'ξ : xz m ᵥ* ((((f ξ)⁻¹ * sect ζ)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ := by
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← vecMul_vecMul, sect_spec hζ, hζh]
  have hξ0 : ξ ≠ 0 := by
    intro h0
    apply hζ
    have := congrArg (fun x => x ᵥ* (((f ξ)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) (hζh.trans h0)
    simpa [vecMul_vecMul, ← Units.val_mul] using this
  have hu : gl ((f ξ)⁻¹ * sect ζ)⁻¹ v = gl (sect ζ)⁻¹ v := by
    rw [_root_.mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply, hhv]
  have hDg : Df gl s C ξ v v = Ct gl s C ((f ξ)⁻¹ * sect ζ) v v := by rw [Df_eq hC hξ0 hg'ξ]
  have hconst : Df gl s C ξ v v = Df gl s C ζ v v := by
    rw [hDg, Df_eq hC hζ (sect_spec hζ), Ct_apply, Ct_apply, hu, md_mul, md_inv, hhd, inv_one, one_mul]
  refine ⟨hconst, fun M hM hM₀M => ?_⟩
  set g' : GL (Fin (m + 1)) k := (f ξ)⁻¹ * sect ζ with hg'
  have hA : Lat (gmap g'⁻¹ M) := lat_gmap _ M hM
  have hA₁A : A₁ ≤ gmap g'⁻¹ M := by
    intro a ha
    have hK : ((g' : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ a) ∈ M :=
      hM₀M (hM₂M₀ (hKM₂ ⟨(ξ, a), ⟨hξS, ha⟩, rfl⟩))
    refine AddSubgroup.mem_map.mpr ⟨_, hK, ?_⟩
    simp only [LinearMap.toAddMonoidHom_coe, mulVecLin_apply]
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have hdens := hA₁s _ hA hA₁A
  have hav := av_conj ψ hψ col hS.col_zero hS.col_add hS.smooth_col gl hS.conj g'⁻¹ M hM ξ v
  have hξg' : ξ ᵥ* (((g'⁻¹)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = xz m := by
    rw [inv_inv, ← hg'ξ, vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, vecMul_one]
  rw [hξg', hu] at hav
  rw [← hav, ← hu, hBg] at hdens

  have hmM : (ν (perp ψ M)).toReal = (md g')⁻¹ * (ν (perp ψ (gmap g'⁻¹ M))).toReal := by
    rw [← meas_perp_gmap ψ ν hψ hψ1 g' hA, gmap_gmap_inv]
  have hidx := meas_perp_index ψ ν hψ hψ1 hA₀ hA (hA₀₁.trans hA₁A)
  rw [hν] at hidx
  have hr : ((A₀.relIndex (gmap g'⁻¹ M) : ℕ) : ℝ) * (ν (perp ψ (gmap g'⁻¹ M))).toReal = 1 := by
    have := congrArg ENNReal.toReal hidx
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one] at this
    exact this.symm
  have hrpos : (0 : ℝ) < (A₀.relIndex (gmap g'⁻¹ M) : ℕ) := by
    exact_mod_cast Nat.pos_of_ne_zero (relIndex_ne_zero_of_lat hA₀ hA)

  have hre1 : (Df gl s C ζ v v).re = md g' ^ (s + 1) * (C (gl g'⁻¹ v) (gl g'⁻¹ v)).re := by
    rw [← hconst, hDg, Ct_apply, Complex.re_ofReal_mul]
  have hre2 : (B' (gl g'⁻¹ v) (gl g'⁻¹ v)).re =
      ((A₀.relIndex (gmap g'⁻¹ M) : ℕ) : ℝ) * (md g'⁻¹ ^ s * (B (av ψ col ξ M v) v).re) := by
    rw [hdens, ← Complex.ofReal_natCast, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have hle := hCB (gl g'⁻¹ v)
  set t := md g' with ht
  have htpos : 0 < t := md_pos g'
  set r : ℝ := ((A₀.relIndex (gmap g'⁻¹ M) : ℕ) : ℝ) with hrdef
  set b := (B (av ψ col ξ M v) v).re with hb
  set c := (C (gl g'⁻¹ v) (gl g'⁻¹ v)).re with hc
  set μA := (ν (perp ψ (gmap g'⁻¹ M))).toReal with hμA
  rw [md_inv, ← ht] at hre2
  rw [hre1, hmM]
  have hμA' : μA = r⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hr)
  rw [hμA']
  have hts : t ^ (s + 1) = t ^ s * t := Real.rpow_add_one htpos.ne' s
  have hti : t⁻¹ ^ s = (t ^ s)⁻¹ := Real.inv_rpow htpos.le s
  rw [hti] at hre2
  have htspos : 0 < t ^ s := Real.rpow_pos_of_pos htpos s
  calc t ^ (s + 1) * c * (t⁻¹ * r⁻¹) ≤ t ^ (s + 1) * (r * ((t ^ s)⁻¹ * b)) * (t⁻¹ * r⁻¹) := by
        rw [← hre2]
        gcongr
    _ = b := by
        rw [hts]
        field_simp

end Main

end PositivityTheory.RgUd.Form.U.Lift2
end
end

section
noncomputable section

open Matrix MeasureTheory GlobalTheory.SplitWeil GlobalTheory.BZMir Filter
open scoped Topology ENNReal NNReal

namespace PositivityTheory.RgUd.Form.U.Lift2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Main

local instance measurableSpaceThirdLift : MeasurableSpace k := borel k
local instance borelSpaceThirdLift : BorelSpace k := ⟨rfl⟩
local instance instSCK3 : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k

variable {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
  {col : (Fin (m + 1) → k) → V →ₗ[ℂ] V} {gl : GL (Fin (m + 1)) k →* (V →ₗ[ℂ] V)} (hS : Setup col gl) {s : ℝ}
  {B B' C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {A₀ : AddSubgroup (Fin (m + 1) → k)} (hA₀ : Lat A₀)
  (hBp : Psd B) (hBc : ∀ x v w, B (col x v) (col x w) = B v w)
  (hBg : ∀ g v w, B (gl g v) (gl g w) = ((md g ^ s : ℝ) : ℂ) * B v w)
  (hD : IsD ψ col A₀ B B') (hCp : Psd C) (hCc : ∀ x v w, C (col x v) w = ((ψ (xz m ⬝ᵥ x) : Circle) : ℂ) * C v w)
  (hC : ∀ p ∈ Mir k m, ∀ v w, C (gl p v) (gl p w) = ((md p ^ (s + 1) : ℝ) : ℂ) * C v w)
  (hCB : ∀ v, (C v v).re ≤ (B' v v).re)
  {ν : Measure (Fin (m + 1) → k)} [ν.IsAddHaarMeasure] (hν : ν (perp ψ A₀) = 1)

include hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν in

theorem cov {K : Set (Fin (m + 1) → k)} (hK : IsCompact K) (h0 : (0 : Fin (m + 1) → k) ∉ K) (v : V) :
    ∫⁻ ξ in K, ENNReal.ofReal (Df gl s C ξ v v).re ∂ν ≤ ENNReal.ofReal (B v v).re := by
  classical
  have hloc : ∀ ζ ∈ K, ∃ M₀ : AddSubgroup (Fin (m + 1) → k), Lat M₀ ∧
      ∀ ξ, ξ - ζ ∈ perp ψ M₀ → Df gl s C ξ v v = Df gl s C ζ v v ∧
        ∀ M : AddSubgroup (Fin (m + 1) → k), Lat M → M₀ ≤ M →
          (Df gl s C ζ v v).re * (ν (perp ψ M)).toReal ≤ (B (av ψ col ξ M v) v).re :=
    fun ζ hζ => locB hψ hψ1 hS hA₀ hBg hD hCp hC hCB hν (fun h => h0 (h ▸ hζ)) v
  choose! M₀ hM₀L hM₀ using hloc
  obtain ⟨F, hFK, hFfin, hFcov⟩ := hK.elim_finite_subcover_image (b := K)
    (c := fun ζ => (fun ξ => ξ - ζ) ⁻¹' (perp ψ (M₀ ζ) : Set (Fin (m + 1) → k)))
    (fun ζ hζ => (perp_open ψ hψ hψ1 (hM₀L ζ hζ)).preimage (continuous_sub_right ζ))
    (fun ζ hζ => Set.mem_biUnion hζ (by simp))
  have hcomp : IsCompact (⋃ ζ ∈ F, (M₀ ζ : Set (Fin (m + 1) → k))) :=
    hFfin.isCompact_biUnion fun ζ hζ => (hM₀L ζ (hFK hζ)).1
  obtain ⟨M, hML, hMsub⟩ := lat_over hcomp
  have hMle : ∀ ζ ∈ F, M₀ ζ ≤ M := fun ζ hζ x hx => hMsub (Set.mem_biUnion hζ hx)
  have hPle : ∀ ζ ∈ F, perp ψ M ≤ perp ψ (M₀ ζ) := fun ζ hζ => perp_anti ψ (hMle ζ hζ)
  have hPo : IsOpen (perp ψ M : Set (Fin (m + 1) → k)) := perp_open ψ hψ hψ1 hML
  obtain ⟨T, hTK, hTfin, hTcov⟩ := hK.elim_finite_subcover_image (b := K)
    (c := fun t => (fun ξ => ξ - t) ⁻¹' (perp ψ M : Set (Fin (m + 1) → k)))
    (fun t _ => hPo.preimage (continuous_sub_right t))
    (fun ξ hξ => Set.mem_biUnion hξ (by simp))
  let q : (Fin (m + 1) → k) → (Fin (m + 1) → k) ⧸ perp ψ M := QuotientAddGroup.mk
  have hq : ∀ a b, q a = q b → a - b ∈ perp ψ M := fun a b h => by
    have h1 := (perp ψ M).neg_mem (QuotientAddGroup.eq.mp h)
    rwa [show -(-a + b) = a - b by abel] at h1
  have hq' : ∀ a b, a - b ∈ perp ψ M → q a = q b := fun a b h => by
    apply QuotientAddGroup.eq.mpr
    rw [show -a + b = -(a - b) by abel]
    exact (perp ψ M).neg_mem h
  have hout : ∀ t, q (q t).out = q t := fun t => QuotientAddGroup.out_eq' (q t)
  let S : Finset (Fin (m + 1) → k) := hTfin.toFinset.image (fun t => (q t).out)
  have hSF : ∀ η ∈ S, ∃ ζ ∈ F, ∀ ξ, ξ - η ∈ perp ψ M → ξ - ζ ∈ perp ψ (M₀ ζ) := by
    intro η hη
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hη
    have htK : t ∈ K := hTK (hTfin.mem_toFinset.mp ht)
    obtain ⟨ζ, hζ, hζt⟩ := Set.mem_iUnion₂.mp (hFcov htK)
    refine ⟨ζ, hζ, fun ξ hξ => ?_⟩
    have h1 : (q t).out - t ∈ perp ψ M := hq _ _ (hout t)
    have h2 : ξ - ζ = (ξ - (q t).out) + ((q t).out - t) + (t - ζ) := by abel
    rw [h2]
    exact add_mem (add_mem (hPle ζ hζ hξ) (hPle ζ hζ h1)) (show t - ζ ∈ perp ψ (M₀ ζ) from hζt)
  have hSd : ∀ η ∈ S, ∀ η' ∈ S, η - η' ∈ perp ψ M → η = η' := by
    intro η hη η' hη' h
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hη
    obtain ⟨t', -, rfl⟩ := Finset.mem_image.mp hη'
    have h1 := hq' _ _ h
    rw [hout, hout] at h1
    rw [h1]
  have hKS : K ⊆ ⋃ η ∈ S, (fun ξ => ξ - η) ⁻¹' (perp ψ M : Set (Fin (m + 1) → k)) := by
    intro ξ hξ
    obtain ⟨t, ht, hξt⟩ := Set.mem_iUnion₂.mp (hTcov hξ)
    refine Set.mem_iUnion₂.mpr ⟨(q t).out, Finset.mem_image.mpr ⟨t, hTfin.mem_toFinset.mpr ht, rfl⟩, ?_⟩
    have h1 : t - (q t).out ∈ perp ψ M := hq _ _ (hout t).symm
    show ξ - (q t).out ∈ perp ψ M
    rw [show ξ - (q t).out = (ξ - t) + (t - (q t).out) by abel]
    exact add_mem (show ξ - t ∈ perp ψ M from hξt) h1
  have hdisj : Set.PairwiseDisjoint (↑S)
      (fun η => (fun ξ => ξ - η) ⁻¹' (perp ψ M : Set (Fin (m + 1) → k))) := by
    intro η hη η' hη' hne
    refine Set.disjoint_left.mpr fun ξ h1 h2 => hne (hSd η hη η' hη' ?_)
    rw [show η - η' = (ξ - η') - (ξ - η) by abel]
    exact sub_mem (show ξ - η' ∈ perp ψ M from h2) (show ξ - η ∈ perp ψ M from h1)
  have hPfin : ν (perp ψ M) < ∞ := meas_perp_lt_top ψ ν hψ hψ1 hML
  have hbd : ∀ η ∈ S, (Df gl s C η v v).re * (ν (perp ψ M)).toReal ≤ (B (av ψ col η M v) v).re ∧
      ∃ ζ ∈ F, Df gl s C η v v = Df gl s C ζ v v ∧
        ∀ ξ, ξ - η ∈ perp ψ M → Df gl s C ξ v v = Df gl s C η v v := by
    intro η hη
    obtain ⟨ζ, hζ, hζη⟩ := hSF η hη
    have hζK := hFK hζ
    have e0 : Df gl s C η v v = Df gl s C ζ v v := ((hM₀ ζ hζK) η (hζη η (by simp))).1
    have hb := ((hM₀ ζ hζK) η (hζη η (by simp))).2 M hML (hMle ζ hζ)
    refine ⟨by rw [e0]; exact hb, ζ, hζ, e0, fun ξ hξ => ?_⟩
    rw [e0]
    exact ((hM₀ ζ hζK) ξ (hζη ξ hξ)).1
  have step : ∀ η ∈ S, ∫⁻ ξ in (fun ξ => ξ - η) ⁻¹' (perp ψ M : Set (Fin (m + 1) → k)),
      ENNReal.ofReal (Df gl s C ξ v v).re ∂ν ≤ ENNReal.ofReal (B (av ψ col η M v) v).re := by
    intro η hη
    obtain ⟨hb, -, -, -, hc⟩ := hbd η hη
    rw [setLIntegral_congr_fun (g := fun _ => ENNReal.ofReal (Df gl s C η v v).re)
      (hPo.preimage (continuous_sub_right η)).measurableSet
      (fun ξ hξ => by simp only; rw [hc ξ hξ]), setLIntegral_const]
    have hmeas : ν ((fun ξ => ξ - η) ⁻¹' (perp ψ M : Set (Fin (m + 1) → k))) = ν (perp ψ M) := by
      simp only [sub_eq_add_neg]
      exact measure_preimage_add_right ν (-η) _
    rw [hmeas, ← ENNReal.ofReal_toReal hPfin.ne, ← ENNReal.ofReal_mul (Df_re_nonneg hCp η v)]
    exact ENNReal.ofReal_le_ofReal hb
  have hnn : ∀ η ∈ S, 0 ≤ (B (av ψ col η M v) v).re := fun η hη =>
    le_trans (mul_nonneg (Df_re_nonneg hCp η v) ENNReal.toReal_nonneg) (hbd η hη).1
  have hbes := av_bessel ψ hψ col hS.col_zero hS.col_add hS.smooth_col B hBp hBc M hML S hSd v
  calc ∫⁻ ξ in K, ENNReal.ofReal (Df gl s C ξ v v).re ∂ν
      ≤ ∫⁻ ξ in ⋃ η ∈ S, (fun ξ => ξ - η) ⁻¹' (perp ψ M : Set (Fin (m + 1) → k)),
          ENNReal.ofReal (Df gl s C ξ v v).re ∂ν := lintegral_mono_set hKS
    _ = ∑ η ∈ S, ∫⁻ ξ in (fun ξ => ξ - η) ⁻¹' (perp ψ M : Set (Fin (m + 1) → k)),
          ENNReal.ofReal (Df gl s C ξ v v).re ∂ν :=
        lintegral_biUnion_finset hdisj (fun η _ => (hPo.preimage (continuous_sub_right η)).measurableSet) _
    _ ≤ ∑ η ∈ S, ENNReal.ofReal (B (av ψ col η M v) v).re := Finset.sum_le_sum step
    _ = ENNReal.ofReal (∑ η ∈ S, (B (av ψ col η M v) v).re) := (ENNReal.ofReal_sum_of_nonneg hnn).symm
    _ ≤ ENNReal.ofReal (B v v).re := ENNReal.ofReal_le_ofReal hbes

include hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν in

theorem bessel (v : V) : ∫⁻ ξ, ENNReal.ofReal (Df gl s C ξ v v).re ∂ν ≤ ENNReal.ofReal (B v v).re := by
  classical
  let f : (Fin (m + 1) → k) → ℝ≥0∞ := fun ξ => ENNReal.ofReal (Df gl s C ξ v v).re
  have hDm : Measurable fun ξ => Df gl s C ξ v v := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro ζ hζ
    exact (continuousAt_const.congr
      ((Df_loc hS hC hζ v v).mono fun ξ hξ => hξ.symm)).continuousWithinAt
  have hfm : Measurable f := ENNReal.measurable_ofReal.comp (Complex.measurable_re.comp hDm)
  obtain ⟨W, hWp, hW⟩ := (nhds_basis_opens (0 : Fin (m + 1) → k)).exists_antitone_subbasis
  let E := CompactExhaustion.choice (Fin (m + 1) → k)
  let K : ℕ → Set (Fin (m + 1) → k) := fun n => E n \ W n
  have hKc : ∀ n, IsCompact (K n) := fun n => (E.isCompact n).diff (hWp n).2
  have h0K : ∀ n, (0 : Fin (m + 1) → k) ∉ K n := fun n h => h.2 (hWp n).1
  have hKmono : Monotone K := fun a b hab => Set.diff_subset_diff (E.subset hab) (hW.antitone hab)
  let g : ℕ → (Fin (m + 1) → k) → ℝ≥0∞ := fun n => (K n).indicator f
  have hgm : ∀ n, Measurable (g n) := fun n => hfm.indicator (hKc n).measurableSet
  have hgmono : Monotone g := fun a b hab ξ =>
    Set.indicator_le_indicator_of_subset (hKmono hab) (fun _ => bot_le) ξ
  have hsup : ∀ ξ, f ξ = ⨆ n, g n ξ := by
    intro ξ
    by_cases hξ : ξ = 0
    · subst hξ
      have hf0 : f 0 = 0 := by simp [f, Df_zero]
      rw [hf0]
      symm
      exact ENNReal.iSup_eq_zero.mpr fun n => by simp [g, Set.indicator_apply, h0K n]
    · obtain ⟨n₁, hn₁⟩ := E.exists_mem ξ
      obtain ⟨i, -, hi⟩ := hW.toHasBasis.mem_iff.mp (isOpen_compl_singleton.mem_nhds (Ne.symm hξ))
      have hmem : ξ ∈ K (max n₁ i) := by
        refine ⟨E.subset (le_max_left _ _) hn₁, fun h => ?_⟩
        exact hi (hW.antitone (le_max_right _ _) h) rfl
      refine le_antisymm (le_iSup_of_le (max n₁ i) ?_) (iSup_le fun n => Set.indicator_le_self _ _ ξ)
      simp [g, Set.indicator_apply, hmem]
  show ∫⁻ ξ, f ξ ∂ν ≤ _
  calc ∫⁻ ξ, f ξ ∂ν = ∫⁻ ξ, ⨆ n, g n ξ ∂ν := lintegral_congr hsup
    _ = ⨆ n, ∫⁻ ξ, g n ξ ∂ν := lintegral_iSup hgm hgmono
    _ ≤ ENNReal.ofReal (B v v).re := iSup_le fun n => by
        simp only [g]
        rw [lintegral_indicator (hKc n).measurableSet]
        exact cov hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν (hKc n) (h0K n) v

omit hψ hψ1 hA₀ hBp hBc hBg hD hCp hCB hν [ν.IsAddHaarMeasure] in
include hS hC in
theorem Df_meas (v w : V) : Measurable fun ξ => Df gl s C ξ v w := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro ζ hζ
  exact (continuousAt_const.congr
    ((Df_loc hS hC hζ v w).mono fun ξ hξ => hξ.symm)).continuousWithinAt

include hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν in
theorem integrable_re (v : V) : Integrable (fun ξ => (Df gl s C ξ v v).re) ν := by
  refine ⟨(Complex.measurable_re.comp (Df_meas hS hC v v)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ξ => Df_re_nonneg hCp ξ v)]
  exact lt_of_le_of_lt (bessel hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν v) ENNReal.ofReal_lt_top

include hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν in
theorem integrable_Df (v w : V) : Integrable (fun ξ => Df gl s C ξ v w) ν := by
  refine Integrable.mono'
    (((integrable_re hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν v).add
      (integrable_re hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν w)).div_const 2)
    (Df_meas hS hC v w).aestronglyMeasurable
    (Eventually.of_forall fun ξ => psd_norm_le _ ⟨Df_herm hCp ξ, Df_re_nonneg hCp ξ⟩ v w)

end Main

end PositivityTheory.RgUd.Form.U.Lift2
end
end

section
noncomputable section

open Matrix MeasureTheory GlobalTheory.SplitWeil GlobalTheory.BZMir Filter
open scoped Topology ENNReal NNReal

namespace PositivityTheory.RgUd.Form.U.Lift2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Main

local instance measurableSpaceFourthLift : MeasurableSpace k := borel k
local instance borelSpaceOnK : BorelSpace k := ⟨rfl⟩
local instance instSCK4 : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k

variable {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
  {col : (Fin (m + 1) → k) → V →ₗ[ℂ] V} {gl : GL (Fin (m + 1)) k →* (V →ₗ[ℂ] V)} (hS : Setup col gl) {s : ℝ}
  {B B' C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {A₀ : AddSubgroup (Fin (m + 1) → k)} (hA₀ : Lat A₀)
  (hBp : Psd B) (hBc : ∀ x v w, B (col x v) (col x w) = B v w)
  (hBg : ∀ g v w, B (gl g v) (gl g w) = ((md g ^ s : ℝ) : ℂ) * B v w)
  (hD : IsD ψ col A₀ B B') (hCp : Psd C) (hCc : ∀ x v w, C (col x v) w = ((ψ (xz m ⬝ᵥ x) : Circle) : ℂ) * C v w)
  (hC : ∀ p ∈ Mir k m, ∀ v w, C (gl p v) (gl p w) = ((md p ^ (s + 1) : ℝ) : ℂ) * C v w)
  (hCB : ∀ v, (C v v).re ≤ (B' v v).re)
  {ν : Measure (Fin (m + 1) → k)} [ν.IsAddHaarMeasure] (hν : ν (perp ψ A₀) = 1)

private theorem addHaar_singleton_zero_eq_zero {m : ℕ} {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (ν : Measure (Fin (m + 1) → k)) [ν.IsAddHaarMeasure] : ν {0} = 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (ValuativeRel.valuation k).integer
  have hϖ0 : (ϖ : k) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  set x : kˣ := Units.mk0 (ϖ : k) hϖ0 with hxdef
  have hx : nabs k x < 1 := by
    rw [nabs_uniformiser hϖ rfl]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast one_lt_resCard k)
  have hx0 : 0 < nabs k x := nabs_pos k x
  let g : GL (Fin (m + 1)) k :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero (((x⁻¹ : kˣ) : k) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k))
      (by simp [Matrix.det_smul])
  have hdet : Matrix.GeneralLinearGroup.det g = x⁻¹ ^ (m + 1) := by
    ext
    simp [g, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_smul]
  have hg : md g = (nabs k x)⁻¹ ^ (m + 1) := by
    show nabs k (Matrix.GeneralLinearGroup.det g) = _
    rw [hdet]
    simp [nabs, map_pow, map_inv]
  have hg1 : 1 < md g := by
    rw [hg]
    exact one_lt_pow₀ (one_lt_inv₀ hx0 |>.2 hx) (Nat.succ_ne_zero m)
  obtain ⟨A, hA, -⟩ := lat_over (isCompact_empty (X := Fin (m + 1) → k))
  have hpow : ∀ j : ℕ, md (g ^ j) = md g ^ j := by
    intro j
    induction j with
    | zero => simp [md_one]
    | succ j ih => rw [pow_succ, md_mul, ih, pow_succ]
  have hbound : ∀ j : ℕ, (ν {0}).toReal ≤ ((md g)⁻¹) ^ j * (ν (perp ψ A)).toReal := by
    intro j
    have h0 : ({0} : Set (Fin (m + 1) → k)) ⊆ (perp ψ (gmap (g ^ j) A) : Set _) := by
      simp [(perp ψ (gmap (g ^ j) A)).zero_mem]
    calc (ν {0}).toReal ≤ (ν (perp ψ (gmap (g ^ j) A))).toReal :=
          ENNReal.toReal_mono (meas_perp_lt_top ψ ν hψ hψ1 (lat_gmap _ _ hA)).ne (measure_mono h0)
      _ = _ := by rw [meas_perp_gmap ψ ν hψ hψ1 _ hA, hpow, inv_pow]
  have hlim : Tendsto (fun j : ℕ => ((md g)⁻¹) ^ j * (ν (perp ψ A)).toReal) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 (md_pos g).le) (inv_lt_one_of_one_lt₀ hg1)
    simpa using this.mul_const (ν (perp ψ A)).toReal
  have hle : (ν {0}).toReal ≤ 0 := ge_of_tendsto' hlim hbound
  have hfin : ν {0} ≠ ⊤ := by
    refine ne_top_of_le_ne_top (meas_perp_lt_top ψ ν hψ hψ1 hA).ne (measure_mono ?_)
    simp [(perp ψ A).zero_mem]
  have := le_antisymm hle ENNReal.toReal_nonneg
  rcases (ENNReal.toReal_eq_zero_iff _).1 this with h | h
  · exact h
  · exact absurd h hfin

include hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hCc hC hCB hν in

theorem lift_form : ∃ I : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ, Psd I ∧ (∀ x v w, I (col x v) (col x w) = I v w) ∧
      (∀ g v w, I (gl g v) (gl g w) = ((nabs k (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * I v w) ∧
      (∀ v, (I v v).re ≤ (B v v).re) ∧ IsD ψ col A₀ I C ∧ IsA col I 0 ∧
      ∀ Y : Submodule ℂ V, (∀ g, ∀ y ∈ Y, gl g y ∈ Y) → (∀ y ∈ Y, ∀ w, C y w = 0) → ∀ y ∈ Y, ∀ w, I y w = 0 := by
  have hC' : ∀ p ∈ Mir k m, ∀ v w, C (gl p v) (gl p w) = ((md p ^ (s + 1) : ℝ) : ℂ) * C v w := hC
  have hint : ∀ v w, Integrable (fun ξ => Df gl s C ξ v w) ν :=
    integrable_Df hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC' hCB hν
  let I : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v w => ∫ ξ, Df gl s C ξ v w ∂ν)
    (fun v₁ v₂ w => by
      simp only [map_add, LinearMap.add_apply]
      exact integral_add (hint _ _) (hint _ _))
    (fun c v w => by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
      exact integral_const_mul c _)
    (fun v w₁ w₂ => by
      simp only [map_add]
      exact integral_add (hint _ _) (hint _ _))
    (fun c v w => by
      simp only [LinearMap.map_smulₛₗ, smul_eq_mul]
      exact integral_const_mul _ _)
  have hI : ∀ v w, I v w = ∫ ξ, Df gl s C ξ v w ∂ν := fun _ _ => rfl
  refine ⟨I, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v w
    rw [hI, hI, ← integral_conj]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => Df_herm hCp ξ v w)
  · intro v
    rw [hI]
    have := integral_re (hint v v)
    simp only [RCLike.re_to_complex] at this
    rw [← this]
    exact integral_nonneg fun ξ => Df_re_nonneg hCp ξ v
  · intro x v w
    rw [hI, hI]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => form_column_invariant hS hCp hCc hC' ξ x v w)
  · intro g v w
    rw [hI, hI]
    have h1 : ∀ ξ, Df gl s C ξ (gl g v) (gl g w) =
        ((md g ^ (s + 1) : ℝ) : ℂ) * Df gl s C (ξ ᵥ* (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) v w := by
      intro ξ
      by_cases hξ : ξ = 0
      · subst hξ
        simp [Df_zero, Matrix.zero_vecMul]
      · exact Df_gl hS hC' hξ g v w
    simp_rw [h1]
    rw [integral_const_mul, integral_vecMul ν (fun ξ => Df gl s C ξ v w) g, ← mul_assoc]
    congr 1
    have hp := md_pos g
    rw [Real.rpow_add_one hp.ne']
    push_cast
    exact mul_div_cancel_right₀ _ (by exact_mod_cast hp.ne')
  · intro v
    rw [hI]
    have := integral_re (hint v v)
    simp only [RCLike.re_to_complex] at this
    rw [← this]
    have hb := bessel hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC' hCB hν v
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ξ => Df_re_nonneg hCp ξ v)
      (integrable_re hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC' hCB hν v).aestronglyMeasurable]
    calc _ ≤ (ENNReal.ofReal (B v v).re).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
      _ = _ := ENNReal.toReal_ofReal (hBp.2 v)
  · intro v w
    have hxz : xz m ≠ (0 : Fin (m + 1) → k) := by
      intro h
      have := congrFun h (Fin.last m)
      simp [xz] at this
    have hloc := Df_loc hS hC' hxz v w
    rw [Df_xz hC'] at hloc
    have hU : (fun η => xz m + η) ⁻¹' {ξ | Df gl s C ξ v w = C v w} ∈ 𝓝 (0 : Fin (m + 1) → k) := by
      have ht : Tendsto (fun η : Fin (m + 1) → k => xz m + η) (𝓝 0) (𝓝 (xz m)) := by
        have := (continuous_add_left (xz m)).tendsto (0 : Fin (m + 1) → k)
        simpa using this
      exact ht hloc
    obtain ⟨A₂, hA₂, hsub⟩ := lat_shrink ψ hψ hψ1 hU
    obtain ⟨A₁, hA₁, h01, h21⟩ := lat_sup hA₀ hA₂
    refine ⟨A₁, hA₁, h01, fun A hA hA1 => ?_⟩
    rw [hI]
    have hav : ∀ ξ, Df gl s C ξ (av ψ col (xz m) A v) w =
        Set.indicator {ξ | ξ - xz m ∈ perp ψ A} (fun _ => C v w) ξ := by
      intro ξ
      rw [AvA.av_eigen' ψ hψ col hS.col_zero hS.col_add hS.smooth_col (Df gl s C ξ) ψ ξ
        (Df_col hS hCc hC' ξ) A hA (xz m) v w]
      by_cases hm : ξ - xz m ∈ perp ψ A
      · rw [Set.indicator_of_mem (show ξ ∈ {ξ | ξ - xz m ∈ perp ψ A} from hm), if_pos]
        · have h2 : ξ - xz m ∈ perp ψ A₂ := perp_anti ψ (h21.trans hA1) hm
          have h3 := hsub h2
          simpa using h3
        · intro a ha
          have := (mem_perp ψ A _).1 hm a ha
          rw [sub_dotProduct, AddChar.map_sub_eq_div, div_eq_one] at this
          exact this
      · rw [Set.indicator_of_notMem (show ξ ∉ {ξ | ξ - xz m ∈ perp ψ A} from hm), if_neg]
        intro hall
        apply hm
        rw [mem_perp]
        intro a ha
        rw [sub_dotProduct, AddChar.map_sub_eq_div, hall a ha, div_self']
    have hset : {ξ | ξ - xz m ∈ perp ψ A} = (fun ξ => ξ + -xz m) ⁻¹' (perp ψ A : Set (Fin (m + 1) → k)) := by
      ext ξ
      simp [sub_eq_add_neg]
    have hmeas : MeasurableSet {ξ | ξ - xz m ∈ perp ψ A} := by
      rw [hset]
      exact (perp_open ψ hψ hψ1 hA).measurableSet.preimage (measurable_add_const _)
    simp_rw [hav]
    rw [integral_indicator_const _ hmeas, measureReal_def, hset, measure_preimage_add_right]
    have h1 : ((A₀.relIndex A : ℝ)) * (ν (perp ψ A)).toReal = 1 := by
      have := meas_perp_index ψ ν hψ hψ1 hA₀ hA (h01.trans hA1)
      rw [hν] at this
      have := congrArg ENNReal.toReal this
      rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at this
      simpa using this.symm
    have h2 : ((A₀.relIndex A : ℂ)) * (((ν (perp ψ A)).toReal : ℝ) : ℂ) = 1 := by
      exact_mod_cast h1
    rw [Complex.real_smul, ← mul_assoc, h2, one_mul]
  · intro v w
    simp only [LinearMap.zero_apply]
    have hone : Continuous ⇑(1 : AddChar k Circle) := by
      have : ⇑(1 : AddChar k Circle) = fun _ => 1 := by
        funext x
        exact AddChar.one_apply x
      rw [this]
      exact continuous_const
    have hav : ∀ A : {A : AddSubgroup (Fin (m + 1) → k) // Lat A},
        I (av 1 col 0 A.1 v) w = ∫ ξ in (perp ψ A.1 : Set (Fin (m + 1) → k)), Df gl s C ξ v w ∂ν := by
      intro A
      rw [hI, ← integral_indicator (perp_open ψ hψ hψ1 A.2).measurableSet]
      congr 1
      funext ξ
      rw [AvA.av_eigen' 1 hone col hS.col_zero hS.col_add hS.smooth_col (Df gl s C ξ) ψ ξ
        (Df_col hS hCc hC' ξ) A.1 A.2 0 v w]
      by_cases hm : ξ ∈ perp ψ A.1
      · rw [Set.indicator_of_mem (show ξ ∈ (perp ψ A.1 : Set (Fin (m + 1) → k)) from hm), if_pos]
        intro a ha
        rw [(mem_perp ψ _ _).1 hm a ha, AddChar.one_apply]
      · rw [Set.indicator_of_notMem (show ξ ∉ (perp ψ A.1 : Set (Fin (m + 1) → k)) from hm), if_neg]
        intro hall
        apply hm
        rw [mem_perp]
        intro a ha
        rw [hall a ha, AddChar.one_apply]
    have hfun : (fun A : {A : AddSubgroup (Fin (m + 1) → k) // Lat A} => I (av 1 col 0 A.1 v) w) =
        fun A => ∫ ξ in (perp ψ A.1 : Set (Fin (m + 1) → k)), Df gl s C ξ v w ∂ν := funext hav
    rw [hfun]
    apply (hint v w).tendsto_setIntegral_nhds_zero
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    have h0 : ν {0} < ε := by
      rw [addHaar_singleton_zero_eq_zero hψ hψ1 ν]
      exact hε
    obtain ⟨U, hU0, hUo, hUε⟩ := Set.exists_isOpen_lt_of_lt _ _ h0
    obtain ⟨A₂, hA₂, hsub⟩ := lat_shrink ψ hψ hψ1 (hUo.mem_nhds (hU0 rfl))
    filter_upwards [Filter.mem_atTop (⟨A₂, hA₂⟩ : {A : AddSubgroup (Fin (m + 1) → k) // Lat A})] with A hA
    have hsub2 : (perp ψ A.1 : Set (Fin (m + 1) → k)) ⊆ U :=
      (SetLike.coe_subset_coe.2 (perp_anti ψ (show A₂ ≤ A.1 from hA))).trans hsub
    exact (measure_mono hsub2).trans hUε.le
  · intro Y hY hCY y hy w
    rw [hI]
    have : (fun ξ => Df gl s C ξ y w) = fun _ => (0 : ℂ) := funext fun ξ => Df_ker hCp hC' Y hY hCY ξ hy w
    rw [this, integral_zero]

end Main

theorem absLift : @AbsLift k _ _ _ _ := by
  intro ψ hψ hψ1 m V _ _ col gl hS s B B' C A₀ hA₀ hBp hBc hBg hD hCp hCc hC hCB
  letI : MeasurableSpace k := measurableSpaceFourthLift
  haveI : BorelSpace k := borelSpaceOnK
  haveI : SecondCountableTopology k := instSCK4
  let μ : Measure (Fin (m + 1) → k) := Measure.addHaar
  have h0 : μ (perp ψ A₀) ≠ 0 := meas_perp_ne_zero ψ μ hψ hψ1 hA₀
  have htop : μ (perp ψ A₀) ≠ ⊤ := (meas_perp_lt_top ψ μ hψ hψ1 hA₀).ne
  let ν : Measure (Fin (m + 1) → k) := (μ (perp ψ A₀))⁻¹ • μ
  haveI : ν.IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul μ (ENNReal.inv_ne_zero.2 htop) (ENNReal.inv_ne_top.2 h0)
  have hν : ν (perp ψ A₀) = 1 := by
    simp only [ν, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel h0 htop
  exact lift_form hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hCc hC hCB hν

end PositivityTheory.RgUd.Form.U.Lift2
end
end

section
namespace PositivityTheory.RgUd.Form.U.Lift2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem uLift : PositivityTheory.RgUd.Form.U.ULift k := uLift_of_abs absLift

end PositivityTheory.RgUd.Form.U.Lift2
end
