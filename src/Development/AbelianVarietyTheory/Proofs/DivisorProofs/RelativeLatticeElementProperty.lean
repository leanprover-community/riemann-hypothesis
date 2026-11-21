import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTensorExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomsDvrCardEqFinrank
import BuildAid.ForwardExisting

section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory

theorem embedding_matrix_independent : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (d : ℕ) (b : Module.Basis (Fin d) ℤ_[p] Λ) (c : Fin d → C), (∀ σ : Λ →+* O, ∑ j, c j * algebraMap O C (σ (b j)) = 0) → c = 0 := by
  intro p _ C _ _ _ v O _ _ _ _ hv Λ _ _ _ _ _ _ d b c hc
  classical
  obtain ⟨hfin, hcard⟩ := GlobalTheory.card_ringHom_to_integers_eq_finrank p C v O hv Λ
  haveI : Fintype (Λ →+* O) := Fintype.ofFinite _
  have hd : Module.finrank ℤ_[p] Λ = d := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  let ι : ℤ_[p] →+* C := (algebraMap O C).comp (padicToO p O)
  let w : (Λ →+* O) → (Fin d → C) := fun σ j => algebraMap O C (σ (b j))
  have hlin : ∀ σ : Λ →+* O, ∀ z : ℤ_[p], ∀ x : Λ,
      algebraMap O C (σ (z • x)) = ι z * algebraMap O C (σ x) := by
    intro σ z x
    rw [Algebra.smul_def, map_mul, map_mul]
    congr 1
    have hu := GlobalTheory.padicToO_unique p O (σ.comp (algebraMap ℤ_[p] Λ))
    have := RingHom.congr_fun hu z
    simp only [RingHom.comp_apply] at this
    rw [this]
    rfl
  have hind : LinearIndependent C w := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have hcol : ∀ j, ∑ σ, a σ * algebraMap O C (σ (b j)) = 0 := by
      intro j
      have := congrFun ha j
      simpa [w, Finset.sum_apply, smul_eq_mul] using this
    have hall : ∀ x : Λ, ∑ σ, a σ * algebraMap O C (σ x) = 0 := by
      intro x
      have hx : ∀ σ : Λ →+* O, algebraMap O C (σ x)
          = ∑ j, ι (b.repr x j) * algebraMap O C (σ (b j)) := by
        intro σ
        conv_lhs => rw [← b.sum_repr x]
        rw [map_sum, map_sum]
        exact Finset.sum_congr rfl (fun j _ => hlin σ _ _)
      simp_rw [hx, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero (fun j _ => ?_)
      have : ∑ σ, a σ * (ι (b.repr x j) * algebraMap O C (σ (b j)))
          = ι (b.repr x j) * ∑ σ, a σ * algebraMap O C (σ (b j)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun σ _ => by ring)
      rw [this, hcol j, mul_zero]
    let τ : (Λ →+* O) → (Λ →* C) := fun σ => ((algebraMap O C).comp σ).toMonoidHom
    have hτ : Function.Injective τ := by
      intro σ σ' h
      ext x
      exact hv.hom_inj (DFunLike.congr_fun h x)
    have hD := (linearIndependent_monoidHom Λ C).comp τ hτ
    rw [Fintype.linearIndependent_iff] at hD
    apply hD a
    funext x
    simpa [τ, Finset.sum_apply] using hall x
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    funext j
    exact j.elim0
  haveI : Nonempty (Λ →+* O) := (Nat.card_pos_iff.mp (by rw [hcard, hd]; exact hdpos)).1
  have hspan : Submodule.span C (Set.range w) = ⊤ := by
    apply hind.span_eq_top_of_card_eq_finrank
    rw [Module.finrank_fin_fun, ← Nat.card_eq_fintype_card, hcard, hd]
  let f : (Fin d → C) →ₗ[C] C := ∑ j, c j • LinearMap.proj j
  have hf : f = 0 := by
    apply LinearMap.ext_on_range hspan
    intro σ
    have := hc σ
    simpa [f, w, LinearMap.sum_apply, smul_eq_mul] using this
  funext j
  have := LinearMap.congr_fun hf (Pi.single j 1)
  simpa [f, LinearMap.sum_apply, Pi.single_apply] using this

end GlobalTheory
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem dvd_xi_of_theta_tensor_vanish : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ r : RL p O Λ, (∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → f r = 0) → (inA (xi ε) : RL p O Λ) ∣ r := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ r hr
  classical
  obtain ⟨-, -, hker, -, -, -, -⟩ := GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hε
  haveI : Module.Free ℤ_[p] Λ := inferInstance
  let b := Module.finBasis ℤ_[p] Λ
  let B := Algebra.TensorProduct.basis (Ainf p O) b
  have hrsum : r = ∑ j, B.repr r j ⊗ₜ b j := by
    conv_lhs => rw [← B.sum_repr r]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hθ : ∀ j, WittVector.fontaineTheta O p (B.repr r j) = 0 := by
    have hc := GlobalTheory.embedding_matrix_independent p C v O hv Λ _ b
      (fun j => algebraMap O C (WittVector.fontaineTheta O p (B.repr r j))) (by
        intro σ
        obtain ⟨f, hf, -⟩ := theta_tensor_exists p C v O hv ε hε Λ σ
        have h0 := hr σ f hf
        rw [hrsum, map_sum] at h0
        simp_rw [show ∀ a l, f (a ⊗ₜ l) = _ from hf] at h0
        have h1 := congrArg (algebraMap O C) h0
        simpa [map_sum, map_mul] using h1)
    intro j
    have := congrFun hc j
    exact hv.hom_inj (by simpa using this)
  rw [hrsum]
  refine Finset.dvd_sum fun j _ => ?_
  have hmem : B.repr r j ∈ Ideal.span {xi ε} := by
    rw [← hker]; exact hθ j
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨c ⊗ₜ b j, ?_⟩
  show _ = (xi ε ⊗ₜ[ℤ_[p]] (1 : Λ)) * _
  rw [← hc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm]

end GlobalTheory.DetInv
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relative_lattice_element_property : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ r : RL p O Λ, (∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → f r = 0) → (inA (xi ε) : RL p O Λ) ∣ r := by
  atlas_forward_decl GlobalTheory.DetInv.dvd_xi_of_theta_tensor_vanish
end
