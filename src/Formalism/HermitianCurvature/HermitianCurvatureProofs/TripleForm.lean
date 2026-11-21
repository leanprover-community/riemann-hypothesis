import Formalism.HermitianCurvature.BlockKernelPropertiesOfSteps

open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.A5x1

theorem lamN_last {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (j : ℕ) (hj : j + 1 = n) : lamN R Z j = lamLin R Z := by
  unfold lamN lamTil lamLin rowN lastCoord
  congr 2
  apply Finset.sum_congr rfl
  intro a _
  have : (a.val = j ↔ a.val + 1 = n) := by omega
  simp [this]

theorem card_isoSet {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (C : Type) [AddCommGroup C] [Module R C] (e : C) (lam : C →ₗ[R] KR R)
    (φ0 : coker R Z ≃ₗ[R] C) (hφ0 : φ0 ∈ isoSet R Z C e lam) :
    Nat.card (isoSet R Z C e lam) = Nat.card (autSet R C e lam) := by
  refine Nat.card_congr ⟨fun φ => ⟨φ0.symm.trans φ.1, ?_⟩, fun σ => ⟨φ0.trans σ.1, ?_⟩, ?_, ?_⟩
  · refine ⟨?_, fun c => ?_⟩
    · have : φ0.symm e = eZ R Z := by rw [← hφ0.1]; simp
      simp [this, φ.2.1]
    · obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (φ0.symm c)
      have h3 : φ0 (Submodule.Quotient.mk v) = c := by rw [hv]; simp
      simp only [LinearEquiv.trans_apply]
      rw [← hv, φ.2.2 v, ← hφ0.2 v, h3]
  · refine ⟨?_, fun v => ?_⟩
    · simp [hφ0.1, σ.2.1]
    · simp only [LinearEquiv.trans_apply]
      rw [σ.2.2, hφ0.2]
  · intro φ; ext x; simp
  · intro σ; ext x; simp

theorem card_isoZZ {K : Type} [CommRing K] (R : Subring K) {n n' : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (Z' : Matrix (Fin n') (Fin n') K)
    (C : Type) [AddCommGroup C] [Module R C] (e : C) (lam : C →ₗ[R] KR R)
    (φ0 : coker R Z ≃ₗ[R] C) (hφ0 : φ0 ∈ isoSet R Z C e lam) :
    Nat.card (isoSet R Z' C e lam) = Nat.card (isoZZ R Z Z') := by
  refine Nat.card_congr ⟨fun ρ => ⟨φ0.trans ρ.1.symm, ?_⟩, fun φ => ⟨φ.1.symm.trans φ0, ?_⟩, ?_, ?_⟩
  · refine ⟨?_, fun v v' hv => ?_⟩
    · simp only [LinearEquiv.trans_apply, hφ0.1]
      exact (LinearEquiv.symm_apply_eq _).2 ρ.2.1.symm
    · simp only [LinearEquiv.trans_apply] at hv
      have h4 : φ0 (Submodule.Quotient.mk v) = ρ.1 (Submodule.Quotient.mk v') := by
        rw [← hv]; simp
      rw [← ρ.2.2 v', ← h4, hφ0.2]
  · refine ⟨?_, fun v' => ?_⟩
    · have : φ.1.symm (eZ R Z') = eZ R Z := by rw [← φ.2.1]; simp
      simp [this, hφ0.1]
    · obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (φ.1.symm (Submodule.Quotient.mk v'))
      have h3 : φ.1 (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' := by rw [hv]; simp
      simp only [LinearEquiv.trans_apply]
      rw [← hv, hφ0.2 v, φ.2.2 v v' h3]
  · intro ρ; ext x; simp
  · intro φ; ext x; simp

end Formalism.FourierDecayAlt.P.A5x1

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.A5x1




theorem tripleForm : Formalism.FourierDecayAlt.A5.TripleForm := by
  intro K _ R ψ w w' k hw hw'
  unfold Kp intTT pairTerm
  apply finsum_congr
  intro q
  congr 2
  split_ifs with hI
  · congr 1
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight ?_
    intro φ
    constructor
    · intro hφ
      refine ⟨hφ, ?_⟩
      intro j hkj hjn
      have hj : j = k := by omega
      subst hj
      refine ⟨0, ?_⟩
      intro v v' hv
      have h2 := hφ.2 v v' hv
      rw [lamN_last R _ j hw'.symm, lamN_last R _ j hw.symm, h2]
      simp
    · exact fun h => h.1
  · rfl

end Formalism.FourierDecayAlt.P
