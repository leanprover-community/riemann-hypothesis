import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDetEltOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusOfPadic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomsDvrCardEqFinrank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiDeterminantElementProperty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTensorExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeLatticeElementProperty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TiltIsDomainValuationRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusTwistedDivisibility
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuCoeffZeroNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfElementThetaCompatible
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeadMulUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfElementThetaCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineThetaNatural
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder

section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_twisted_divisibility : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [IsDomain S] [ValuationRing S] [CharP S p] [PerfectRing S p] (d : ℕ) (m : WittVector p S) (U : Matrix (Fin d) (Fin d) (WittVector p S)) (Z : Fin d → WittVector p S), m.coeff 0 ≠ 0 → (∀ i, m * WittVector.frobenius (Z i) = WittVector.frobenius m * (U *ᵥ Z) i) → ∀ i, m ∣ Z i := by
  first | exact @GlobalTheory.LemY.dvd_of_frobenius_eq | exact GlobalTheory.LemY.dvd_of_frobenius_eq | (intros; apply GlobalTheory.LemY.dvd_of_frobenius_eq <;> assumption)
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

noncomputable section

namespace GlobalTheory.LemYR

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]

def phiT : RL p O Λ →+* RL p O Λ :=
  (Algebra.TensorProduct.map (PsiPhi.frobAlg (p := p) (O := O)) (AlgHom.id ℤ_[p] Λ)).toRingHom

theorem phiT_tmul (a : Ainf p O) (l : Λ) : phiT (a ⊗ₜ l) = WittVector.frobenius a ⊗ₜ l := rfl

theorem phiT_psi {ψ : RL p O Λ →+* RL p O Λ} (hψ : IsPsi ψ) (r : RL p O Λ) : phiT (ψ r) = r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a l => rw [hψ, phiT_tmul, PsiPhi.frobenius_phiInv']
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem phiT_inA (a : Ainf p O) : phiT (inA a : RL p O Λ) = inA (WittVector.frobenius a) := by
  show phiT (a ⊗ₜ 1) = WittVector.frobenius a ⊗ₜ 1
  rfl

theorem repr_phiT {ι : Type} (b : Module.Basis ι ℤ_[p] Λ) (r : RL p O Λ) (i : ι) :
    (Algebra.TensorProduct.basis (Ainf p O) b).repr (phiT r) i =
      WittVector.frobenius ((Algebra.TensorProduct.basis (Ainf p O) b).repr r i) := by
  have hc : ∀ c : ℤ_[p], WittVector.frobenius (algebraMap ℤ_[p] (Ainf p O) c) =
      algebraMap ℤ_[p] (Ainf p O) c := PsiPhi.frobenius_ofPadic
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a l =>
    rw [phiT_tmul, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul]
    simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, hc]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

end GlobalTheory.LemYR

open GlobalTheory.LemYR in

theorem GlobalTheory.LemYR.lemY_tensor : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → ∀ m : Ainf p O, m.coeff 0 ≠ 0 → ∀ z w : RL p O Λ, z * ψ (inA m) = inA m * w * ψ z → (inA m : RL p O Λ) ∣ z := by
  intro p _ C _ _ _ v O _ _ _ _ hv Λ _ _ _ _ _ _ ψ hψ m hm z w hzw
  obtain ⟨hD, hV⟩ := GlobalTheory.TiltValuation.tilt_isDomain_valuationRing p C v O hv
  haveI : Module.IsTorsionFree ℤ_[p] Λ := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (FaithfulSMul.algebraMap_injective ℤ_[p] Λ)
  haveI : Module.Free ℤ_[p] Λ := Module.free_of_finite_type_torsion_free'
  set b := Module.finBasis ℤ_[p] Λ
  set B := Algebra.TensorProduct.basis (Ainf p O) b
  have h1 : phiT z * inA m = inA (WittVector.frobenius m) * phiT w * z := by
    have := congrArg phiT hzw
    simpa only [map_mul, phiT_psi hψ, phiT_inA] using this
  have hA : ∀ (a : Ainf p O) (r : RL p O Λ) i, B.repr (inA a * r) i = a * B.repr r i := by
    intro a r i
    rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have key : ∀ i, m * WittVector.frobenius (B.repr z i) =
      WittVector.frobenius m * (Algebra.leftMulMatrix B (phiT w) *ᵥ fun j => B.repr z j) i := by
    intro i
    have := congrArg (fun r => B.repr r i) h1
    rw [mul_comm, hA, repr_phiT, mul_assoc, hA] at this
    rw [this]
    congr 1
    exact congrFun (Algebra.leftMulMatrix_mulVec_repr B (phiT w) z) i |>.symm
  have hdiv := GlobalTheory.T.frobenius_twisted_divisibility p (PreTilt O p) (Module.finrank ℤ_[p] Λ) m
    (Algebra.leftMulMatrix B (phiT w)) (fun j => B.repr z j) hm key
  choose c hc using hdiv
  refine ⟨∑ i, c i • B i, ?_⟩
  conv_lhs => rw [← B.sum_repr z]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hc i, mul_smul, Algebra.smul_def (m : Ainf p O) (c i • B i)]
end
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_coefficient_psi_property : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → ∀ m : Ainf p O, m.coeff 0 ≠ 0 → ∀ z w : RL p O Λ, z * ψ (inA m) = inA m * w * ψ z → (inA m : RL p O Λ) ∣ z := by
  atlas_forward_decl GlobalTheory.LemYR.lemY_tensor
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory

theorem DetInv.dvd_pow_of_local_dvd_pow (R C ι : Type) [CommRing R] [Field C] (f : ι → (R →+* C)) (ξ : R)
    (hξ : ξ ∈ nonZeroDivisors R) (hf : ∀ i, f i ξ = 0) (hker : ∀ r : R, (∀ i, f i r = 0) → ξ ∣ r) :
    ∀ (n : ℕ) (r : R), (∀ i, ∃ s : R, f i s ≠ 0 ∧ ξ ^ n ∣ s * r) → ξ ^ n ∣ r := by
  intro n
  induction n with
  | zero => intro r _; simp
  | succ n ih =>
    intro r h
    have hr0 : ∀ i, f i r = 0 := by
      intro i
      obtain ⟨s, hs, t, ht⟩ := h i
      have h1 : f i (s * r) = 0 := by
        rw [ht, map_mul, map_pow, hf i, zero_pow (Nat.succ_ne_zero n), zero_mul]
      rw [map_mul] at h1
      exact (mul_eq_zero.mp h1).resolve_left hs
    obtain ⟨r1, rfl⟩ := hker r hr0
    have h2 : ∀ i, ∃ s : R, f i s ≠ 0 ∧ ξ ^ n ∣ s * r1 := by
      intro i
      obtain ⟨s, hs, t, ht⟩ := h i
      refine ⟨s, hs, t, ?_⟩
      have : ξ * (s * r1) = ξ * (ξ ^ n * t) := by
        rw [← mul_assoc, mul_comm ξ s, mul_assoc, ht]; ring
      exact (mul_cancel_left_mem_nonZeroDivisors hξ).mp this
    obtain ⟨u, hu⟩ := ih r1 h2
    exact ⟨u, by rw [hu]; ring⟩

example : ∀ (R C ι : Type) [CommRing R] [Field C] (f : ι → (R →+* C)) (ξ : R), ξ ∈ nonZeroDivisors R → (∀ i, f i ξ = 0) → (∀ r : R, (∀ i, f i r = 0) → ξ ∣ r) → ∀ (n : ℕ) (r : R), (∀ i, ∃ s : R, f i s ≠ 0 ∧ ξ ^ n ∣ s * r) → ξ ^ n ∣ r :=
  @DetInv.dvd_pow_of_local_dvd_pow

end GlobalTheory
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisibility_of_vanishing_powers : ∀ (R C ι : Type) [CommRing R] [Field C] (f : ι → (R →+* C)) (ξ : R), ξ ∈ nonZeroDivisors R → (∀ i, f i ξ = 0) → (∀ r : R, (∀ i, f i r = 0) → ξ ∣ r) → ∀ (n : ℕ) (r : R), (∀ i, ∃ s : R, f i s ≠ 0 ∧ ξ ^ n ∣ s * r) → ξ ^ n ∣ r := by
  atlas_forward_decl GlobalTheory.DetInv.dvd_pow_of_local_dvd_pow
end

section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem dvd_of_lead_orders_eq : ∀ (R C ι : Type) [CommRing R] [Field C] (f : ι → (R →+* C))
    (ξ : R) (N : ℕ) (a : ι → ℕ) (c c' : ι → C) (Δ Δ' u u' g g' g₁ : R),
    ξ ∈ nonZeroDivisors R → (∀ i, f i ξ = 0) → (∀ r : R, (∀ i, f i r = 0) → ξ ∣ r) →
    (∀ i, a i ≤ N) → (∀ i, c i ≠ 0) → (∀ i, Lead (f i) ξ Δ (a i) (c i)) →
    (∀ i, Lead (f i) ξ Δ' (a i) (c' i)) → Δ = g * u → Δ' = g' * u' → (∀ i, f i u' ≠ 0) →
    g * g₁ = ξ ^ N → g ∣ g' := by
  intro R C ι _ _ f ξ N a c c' Δ Δ' u u' g g' g₁ hξ hf0 hker haN hc hL hL' hΔ hΔ' hu' hgg
  have hpow : ∀ n : ℕ, ξ ^ n ∈ nonZeroDivisors R := fun n => pow_mem hξ n
  have hloc : ∀ i, ∃ s : R, f i s ≠ 0 ∧ ξ ^ N ∣ s * (g' * g₁) := by
    intro i
    obtain ⟨s, t, hs, hst, hft⟩ := hL i
    obtain ⟨s', t', hs', hst', -⟩ := hL' i
    have ht : f i t ≠ 0 := by rw [hft]; exact mul_ne_zero (hc i) hs
    have hsplit : ξ ^ a i * ξ ^ (N - a i) = ξ ^ N := pow_mul_pow_sub ξ (haN i)
    have key : t * g₁ = s * u * ξ ^ (N - a i) := by
      have h1 : (t * g₁ - s * u * ξ ^ (N - a i)) * ξ ^ a i = 0 := by
        have e1 : ξ ^ a i * t * g₁ = s * u * ξ ^ N := by
          calc ξ ^ a i * t * g₁ = (s * Δ) * g₁ := by rw [hst]
            _ = s * u * (g * g₁) := by rw [hΔ]; ring
            _ = s * u * ξ ^ N := by rw [hgg]
        rw [← hsplit] at e1
        linear_combination e1
      have := (mul_right_mem_nonZeroDivisors_eq_zero_iff (hpow (a i))).mp h1
      exact sub_eq_zero.mp this
    refine ⟨s' * u' * t, ?_, ⟨t' * s * u, ?_⟩⟩
    · simp only [map_mul]
      exact mul_ne_zero (mul_ne_zero hs' (hu' i)) ht
    · calc s' * u' * t * (g' * g₁) = (s' * Δ') * (t * g₁) := by rw [hΔ']; ring
        _ = ξ ^ a i * t' * (s * u * ξ ^ (N - a i)) := by rw [hst', key]
        _ = (ξ ^ a i * ξ ^ (N - a i)) * (t' * s * u) := by ring
        _ = ξ ^ N * (t' * s * u) := by rw [hsplit]
  obtain ⟨b, hb⟩ := GlobalTheory.T.divisibility_of_vanishing_powers R C ι f ξ hξ hf0 hker N (g' * g₁) hloc
  have hg₁ : g₁ ∈ nonZeroDivisors R := by
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    have : x * ξ ^ N = 0 := by rw [← hgg, ← mul_assoc, mul_comm x g, mul_assoc, hx, mul_zero]
    exact (mul_right_mem_nonZeroDivisors_eq_zero_iff (hpow N)).mp this
  refine ⟨b, ?_⟩
  have h2 : (g' - g * b) * g₁ = 0 := by
    rw [sub_mul, hb, ← hgg]; ring
  exact sub_eq_zero.mp ((mul_right_mem_nonZeroDivisors_eq_zero_iff hg₁).mp h2)

end GlobalTheory.DetInv
end

section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem dvd_of_twisted_eq :
    ∀ (R : Type) [CommRing R] (ψ : R →+* R) (m Δ Δs Δ' g b : R), m ∈ nonZeroDivisors R →
      Δ * Δs = m → Δ = g * ψ Δ → Δ' = g * b * ψ Δ' →
      (∀ z w : R, z * ψ m = m * w * ψ z → m ∣ z) → Δ ∣ Δ' := by
  intro R _ ψ m Δ Δs Δ' g b hm hmul hΔ hΔ' key
  have hz : (Δ' * Δs) * ψ m = m * b * ψ (Δ' * Δs) := by
    have h1 : Δ' * ψ Δ = b * ψ Δ' * Δ := by
      calc Δ' * ψ Δ = (g * b * ψ Δ') * ψ Δ := by rw [← hΔ']
        _ = b * ψ Δ' * (g * ψ Δ) := by ring
        _ = b * ψ Δ' * Δ := by rw [← hΔ]
    rw [← hmul, map_mul, map_mul]
    calc Δ' * Δs * (ψ Δ * ψ Δs) = (Δ' * ψ Δ) * (Δs * ψ Δs) := by ring
      _ = (b * ψ Δ' * Δ) * (Δs * ψ Δs) := by rw [h1]
      _ = Δ * Δs * b * (ψ Δ' * ψ Δs) := by ring
  obtain ⟨c, hc⟩ := key _ _ hz
  refine ⟨c, ?_⟩
  have hzero : (Δ' - Δ * c) * m = 0 := by
    have : (Δ' - Δ * c) * Δs = 0 := by
      rw [sub_mul, hc, ← hmul]; ring
    calc (Δ' - Δ * c) * m = ((Δ' - Δ * c) * Δs) * Δ := by rw [← hmul]; ring
      _ = 0 := by rw [this, zero_mul]
  exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff_right.mp hm) _ hzero)

end GlobalTheory.DetInv
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem dvd_of_detElt_orders_eq : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → ∀ (N : ℕ) (Δ Δ' : RL p O Λ) (a : (Λ →+* O) → ℕ) (c : (Λ →+* O) → C) (c' : (Λ →+* O) → C), IsDetElt ε ψ N Δ → IsDetElt ε ψ N Δ' → HasOrders C ε N Δ a c → HasOrders C ε N Δ' a c' → Δ ∣ Δ' := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ ψ hψ N Δ Δ' a c c' hD hD' hO hO'
  obtain ⟨hAdom, -, hker, -, hnu, hxi, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε
  obtain ⟨hmu0, hmu, -⟩ := GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv ε hε
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  have hinA : ∀ x : Ainf p O, (inA x : RL p O Λ) = x ⊗ₜ[ℤ_[p]] (1 : Λ) := fun x => by
    first | rfl | simp [inA, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self]
  have hθ : ∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → ∀ x, f (inA x) = WittVector.fontaineTheta O p x := by
    intro σ f hf x; rw [hinA, hf, map_one, mul_one]
  have hθxi : WittVector.fontaineTheta O p (xi ε) = 0 := by
    rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self _
  have hψmu : ψ (inA (mu ε)) = inA (nu ε) := by
    rw [hinA, hψ, hinA, phiInv_mu]

  have hu' : ∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → algebraMap O C (f (ψ Δ')) ≠ 0 := by
    intro σ f hf h0
    obtain ⟨k, hk⟩ := hD'.1
    have h1 := congrArg (fun x => algebraMap O C (f (ψ x))) hk
    simp only [map_pow, map_mul, hψmu, hθ σ f hf, h0, zero_mul] at h1
    exact pow_ne_zero N ((map_ne_zero_iff _ hinj).mpr hnu) h1
  obtain ⟨g, hΔg, g₁, hgg⟩ := hD.2
  obtain ⟨g', hΔg', -⟩ := hD'.2
  let ι := {q : (Λ →+* O) × (RL p O Λ →+* O) // IsTheta q.1 q.2}
  have hξ : (inA (xi ε) : RL p O Λ) ∈ nonZeroDivisors (RL p O Λ) :=
    GlobalTheory.DetInv.inA_mem_nonZeroDivisors p C v O hv ε hε Λ (xi ε) hxi
  obtain ⟨b, hb⟩ := GlobalTheory.DetInv.dvd_of_lead_orders_eq (RL p O Λ) C ι
    (fun i => (algebraMap O C).comp i.1.2) (inA (xi ε)) N (fun i => a i.1.1)
    (fun i => c i.1.1) (fun i => c' i.1.1) Δ Δ' (ψ Δ) (ψ Δ') g g' g₁ hξ
    (fun i => by
      show algebraMap O C (i.1.2 (inA (xi ε))) = 0
      rw [hθ _ _ i.2, hθxi, map_zero])
    (fun r hr => GlobalTheory.T.relative_lattice_element_property p C v O hv ε hε Λ r (fun σ f hf => hinj (by
      simpa using hr ⟨(σ, f), hf⟩)))
    (fun i => (hO i.1.1 i.1.2 i.2).1) (fun i => (hO i.1.1 i.1.2 i.2).2.1)
    (fun i => (hO i.1.1 i.1.2 i.2).2.2) (fun i => (hO' i.1.1 i.1.2 i.2).2.2)
    hΔg hΔg' (fun i => by simpa using hu' i.1.1 i.1.2 i.2) hgg.symm
  haveI := hAdom
  obtain ⟨Δs, hΔs⟩ := hD.1
  have hcoeff : (mu ε ^ N).coeff 0 ≠ 0 := by
    haveI : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
    have : ∀ n : ℕ, (mu ε ^ n).coeff 0 = (mu ε).coeff 0 ^ n := by
      intro n; induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, WittVector.mul_coeff_zero, ih, pow_succ]
    rw [this]; exact pow_ne_zero N hmu0
  refine GlobalTheory.DetInv.dvd_of_twisted_eq (RL p O Λ) ψ (inA (mu ε ^ N)) Δ Δs Δ' g b
    (GlobalTheory.DetInv.inA_mem_nonZeroDivisors p C v O hv ε hε Λ _ (pow_ne_zero N hmu))
    (by
      show Δ * Δs = algebraMap (Ainf p O) (RL p O Λ) (mu ε ^ N)
      rw [map_pow]; exact hΔs.symm) hΔg (by rw [hb] at hΔg'; exact hΔg') ?_
  exact GlobalTheory.T.ainf_coefficient_psi_property p C v O hv Λ ψ hψ (mu ε ^ N) hcoeff

end GlobalTheory.DetInv
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_determinant_orders_property : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → ∀ (N : ℕ) (Δ Δ' : RL p O Λ) (a : (Λ →+* O) → ℕ) (c : (Λ →+* O) → C) (c' : (Λ →+* O) → C), IsDetElt ε ψ N Δ → IsDetElt ε ψ N Δ' → HasOrders C ε N Δ a c → HasOrders C ε N Δ' a c' → Δ ∣ Δ' := by
  atlas_forward_decl GlobalTheory.DetInv.dvd_of_detElt_orders_eq
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem lead_valuation_eq : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → ∀ (N : ℕ) (Δ Δ' : RL p O Λ) (a : (Λ →+* O) → ℕ) (c : (Λ →+* O) → C) (c' : (Λ →+* O) → C), IsDetElt ε ψ N Δ → IsDetElt ε ψ N Δ' → HasOrders C ε N Δ a c → HasOrders C ε N Δ' a c' → ∀ τ, v (c τ) = v (c' τ) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ ψ hψ N Δ Δ' a c c' hΔ hΔ' hO hO' τ
  obtain ⟨f, hf, -, hfξ, -⟩ := GlobalTheory.DetInv.theta_tensor_exists p C v O hv ε hε Λ τ
  have hξ0 : xi ε ≠ 0 := (GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hε).2.2.2.2.2.1
  have hreg : (inA (xi ε) : RL p O Λ) ∈ nonZeroDivisors (RL p O Λ) :=
    GlobalTheory.T.ainf_element_theta_compatible p C v O hv ε hε Λ (xi ε) hξ0
  obtain ⟨y, hy⟩ := GlobalTheory.T.psi_determinant_orders_property p C v O hv ε hε Λ ψ hψ N Δ Δ' a c c' hΔ hΔ' hO hO'
  obtain ⟨y', hy'⟩ := GlobalTheory.T.psi_determinant_orders_property p C v O hv ε hε Λ ψ hψ N Δ' Δ a c' c hΔ' hΔ hO' hO
  obtain ⟨-, -, hL⟩ := hO τ f hf
  obtain ⟨-, -, hL'⟩ := hO' τ f hf
  set F := (algebraMap O C).comp f
  have hL2 : Lead F (inA (xi ε)) (y * Δ) (a τ) (c' τ) := by rw [mul_comm, ← hy]; exact hL'
  have hL2' : Lead F (inA (xi ε)) (y' * Δ') (a τ) (c τ) := by rw [mul_comm, ← hy']; exact hL
  have e1 := GlobalTheory.DetInv.lead_mul_unique _ _ F _ _ _ _ _ _ hreg hL hL2
  have e2 := GlobalTheory.DetInv.lead_mul_unique _ _ F _ _ _ _ _ _ hreg hL' hL2'
  have b1 : v (F y) ≤ 1 := hv.map_le_one (f y)
  have b2 : v (F y') ≤ 1 := hv.map_le_one (f y')
  apply le_antisymm
  · rw [e2, map_mul]; exact mul_le_of_le_one_left' b2
  · rw [e1, map_mul]; exact mul_le_of_le_one_left' b1

end GlobalTheory.DetInv
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_determinant_eigen_property : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → ∀ (N : ℕ) (Δ Δ' : RL p O Λ) (a : (Λ →+* O) → ℕ) (c : (Λ →+* O) → C) (c' : (Λ →+* O) → C), IsDetElt ε ψ N Δ → IsDetElt ε ψ N Δ' → HasOrders C ε N Δ a c → HasOrders C ε N Δ' a c' → ∀ τ, v (c τ) = v (c' τ) := by
  atlas_forward_decl GlobalTheory.DetInv.lead_valuation_eq
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem lead_mul {R C : Type} [CommRing R] [Field C] (f : R →+* C) (ξ r r' : R) (n n' : ℕ)
    (c c' : C) (h : Lead f ξ r n c) (h' : Lead f ξ r' n' c') :
    Lead f ξ (r * r') (n + n') (c * c') := by
  obtain ⟨s, t, hs, hr, ht⟩ := h
  obtain ⟨s', t', hs', hr', ht'⟩ := h'
  refine ⟨s * s', t * t', ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero hs hs'
  · calc s * s' * (r * r') = (s * r) * (s' * r') := by ring
      _ = ξ ^ (n + n') * (t * t') := by rw [hr, hr', pow_add]; ring
  · rw [map_mul, map_mul, ht, ht']; ring

theorem detData_mul : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (C : Type) [Field C] [Algebra O C] (ε : PreTilt O p) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (ψ : RL p O Λ →+* RL p O Λ) (N N' : ℕ) (Δ Δ' : RL p O Λ) (a a' : (Λ →+* O) → ℕ) (c c' : (Λ →+* O) → C), IsDetElt ε ψ N Δ → IsDetElt ε ψ N' Δ' → HasOrders C ε N Δ a c → HasOrders C ε N' Δ' a' c' → IsDetElt ε ψ (N + N') (Δ * Δ') ∧ HasOrders C ε (N + N') (Δ * Δ') (a + a') (c * c') := by
  intro p _ O _ _ _ C _ _ ε Λ _ _ ψ N N' Δ Δ' a a' c c' h1 h2 h3 h4
  obtain ⟨hd, g, hg, hgd⟩ := h1
  obtain ⟨hd', g', hg', hgd'⟩ := h2
  refine ⟨⟨?_, g * g', ?_, ?_⟩, ?_⟩
  · rw [pow_add]; exact mul_dvd_mul hd hd'
  · rw [map_mul]
    calc Δ * Δ' = (g * ψ Δ) * (g' * ψ Δ') := by rw [← hg, ← hg']
      _ = g * g' * (ψ Δ * ψ Δ') := by ring
  · rw [pow_add]; exact mul_dvd_mul hgd hgd'
  · intro σ f hf
    obtain ⟨ha, hc, hl⟩ := h3 σ f hf
    obtain ⟨ha', hc', hl'⟩ := h4 σ f hf
    refine ⟨?_, ?_, ?_⟩
    · simp only [Pi.add_apply]; omega
    · simp only [Pi.mul_apply]; exact mul_ne_zero hc hc'
    · simpa only [Pi.add_apply, Pi.mul_apply] using lead_mul _ _ _ _ _ _ _ _ hl hl'

end GlobalTheory.DetInv
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_element_product : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (C : Type) [Field C] [Algebra O C] (ε : PreTilt O p) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (ψ : RL p O Λ →+* RL p O Λ) (N N' : ℕ) (Δ Δ' : RL p O Λ) (a a' : (Λ →+* O) → ℕ) (c c' : (Λ →+* O) → C), IsDetElt ε ψ N Δ → IsDetElt ε ψ N' Δ' → HasOrders C ε N Δ a c → HasOrders C ε N' Δ' a' c' → IsDetElt ε ψ (N + N') (Δ * Δ') ∧ HasOrders C ε (N + N') (Δ * Δ') (a + a') (c * c') := by
  atlas_forward_decl GlobalTheory.DetInv.detData_mul
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

noncomputable section
namespace GlobalTheory.AddExt

theorem nat_comb {ι : Type} (S : Set (ι → ℕ)) (c : (ι → ℕ) → ℝ)
    (hS : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S ∧ c (x + y) = c x + c y) {x0 : ι → ℕ} (hx0 : x0 ∈ S)
    (T : Finset S) (n : S → ℕ) :
    x0 + ∑ s ∈ T, n s • (s : ι → ℕ) ∈ S ∧
      c (x0 + ∑ s ∈ T, n s • (s : ι → ℕ)) = c x0 + ∑ s ∈ T, (n s : ℝ) * c s := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [hx0]
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    suffices key : ∀ k : ℕ, x0 + (k • (a : ι → ℕ) + ∑ s ∈ T, n s • (s : ι → ℕ)) ∈ S ∧
        c (x0 + (k • (a : ι → ℕ) + ∑ s ∈ T, n s • (s : ι → ℕ))) =
          c x0 + ((k : ℝ) * c a + ∑ s ∈ T, (n s : ℝ) * c s) from key (n a)
    intro k
    induction k with
    | zero => simpa using ih
    | succ k ihk =>
      have e : x0 + ((k+1) • (a : ι → ℕ) + ∑ s ∈ T, n s • (s : ι → ℕ)) =
          (x0 + (k • (a : ι → ℕ) + ∑ s ∈ T, n s • (s : ι → ℕ))) + a := by
        rw [succ_nsmul]; abel
      rw [e]
      obtain ⟨h1, h2⟩ := hS _ ihk.1 _ a.2
      refine ⟨h1, ?_⟩
      rw [h2, ihk.2]; push_cast; ring

theorem ker_le {ι : Type} (S : Set (ι → ℕ)) (c : (ι → ℕ) → ℝ)
    (hS : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S ∧ c (x + y) = c x + c y) {x0 : ι → ℕ} (hx0 : x0 ∈ S)
    (l : S →₀ ℤ)
    (hl : Finsupp.linearCombination ℤ (fun s : S => fun i => ((s : ι → ℕ) i : ℤ)) l = 0) :
    Finsupp.linearCombination ℤ (fun s : S => c s) l = 0 := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hl ⊢
  obtain ⟨p, hp⟩ : ∃ p : S → ℕ, ∀ s, p s = (l s).toNat := ⟨_, fun _ => rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : S → ℕ, ∀ s, q s = (-l s).toNat := ⟨_, fun _ => rfl⟩
  have hpq : ∀ s, l s = (p s : ℤ) - q s := fun s => by
    rw [hp, hq]; omega
  have heq : ∑ s ∈ l.support, p s • (s : ι → ℕ) = ∑ s ∈ l.support, q s • (s : ι → ℕ) := by
    funext i
    have := congrFun hl i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hpq, sub_mul] at this
    rw [Finset.sum_sub_distrib, sub_eq_zero] at this
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact_mod_cast this
  have h1 := (nat_comb S c hS hx0 l.support p).2
  have h2 := (nat_comb S c hS hx0 l.support q).2
  rw [heq, h2] at h1
  have h3 : ∑ s ∈ l.support, (p s : ℝ) * c s = ∑ s ∈ l.support, (q s : ℝ) * c s := by linarith
  simp only [hpq, zsmul_eq_mul, Int.cast_sub, Int.cast_natCast, sub_mul, Finset.sum_sub_distrib, h3, sub_self]

theorem exists_linear : ∀ (ι : Type) [Fintype ι] (S : Set (ι → ℕ)) (c : (ι → ℕ) → ℝ),
    (∀ x ∈ S, ∀ y ∈ S, x + y ∈ S ∧ c (x + y) = c x + c y) →
      ∃ κ : ι → ℝ, ∀ x ∈ S, c x = ∑ i, (x i : ℝ) * κ i := by
  intro ι _ S c hS
  classical
  rcases S.eq_empty_or_nonempty with hE | ⟨x0, hx0⟩
  · exact ⟨0, by simp [hE]⟩
  let v : S → ι → ℤ := fun s i => ((s : ι → ℕ) i : ℤ)
  let A : (S →₀ ℤ) →+ (ι → ℤ) := (Finsupp.linearCombination ℤ v).toAddMonoidHom
  let C : (S →₀ ℤ) →+ ℝ := (Finsupp.linearCombination ℤ (fun s : S => c s)).toAddMonoidHom
  have hker : A.ker ≤ C.ker := fun l hl =>
    AddMonoidHom.mem_ker.mpr (ker_le S c hS hx0 l (AddMonoidHom.mem_ker.mp hl))
  letI : DivisibleBy ℝ ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u => ⟨u / n, by
      have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      show n • (u / (n : ℝ)) = u
      rw [nsmul_eq_mul]; field_simp⟩
  letI : DivisibleBy ℝ ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨g, hg⟩ := (Module.Baer.of_divisible ℝ).extension_property_addMonoidHom
    (QuotientAddGroup.kerLift A) (QuotientAddGroup.kerLift_injective A)
    (QuotientAddGroup.lift A.ker C hker)
  refine ⟨fun i => g (Pi.single i 1), fun x hx => ?_⟩
  have h1 := DFunLike.congr_fun hg (QuotientAddGroup.mk (Finsupp.single ⟨x, hx⟩ 1))
  have hA : A (Finsupp.single ⟨x, hx⟩ 1) = ∑ i, ((x i : ℤ)) • (Pi.single i (1:ℤ) : ι → ℤ) := by
    ext j; simp [A, v, Finset.sum_apply, Pi.single_apply]
  have hC : C (Finsupp.single ⟨x, hx⟩ 1) = c x := by simp [C]
  simp only [AddMonoidHom.comp_apply, QuotientAddGroup.kerLift_mk, QuotientAddGroup.lift_mk] at h1
  rw [hA, hC, map_sum] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, zsmul_eq_mul, Int.cast_natCast]

end GlobalTheory.AddExt
end
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_function_on_monoid_linear : ∀ (ι : Type) [Fintype ι] (S : Set (ι → ℕ)) (c : (ι → ℕ) → ℝ), (∀ x ∈ S, ∀ y ∈ S, x + y ∈ S ∧ c (x + y) = c x + c y) → ∃ κ : ι → ℝ, ∀ x ∈ S, c x = ∑ i, (x i : ℝ) * κ i := by
  atlas_forward_decl GlobalTheory.AddExt.exists_linear
end

section
section
noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem log_val_lead_linear : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → ∀ τ : Λ →+* O, ∃ (κ₀ : ℝ) (κ : (Λ →+* O) → ℝ), ∀ (N : ℕ) (Δ : RL p O Λ) (a : (Λ →+* O) → ℕ) (c : (Λ →+* O) → C), IsDetElt ε ψ N Δ → HasOrders C ε N Δ a c → Real.log (v (c τ)) = N * κ₀ + ∑ᶠ σ, (a σ : ℝ) * κ σ := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ ψ hψ τ
  classical
  haveI : Finite (Λ →+* O) := (GlobalTheory.card_ringHom_to_integers_eq_finrank p C v O hv Λ).1
  letI : Fintype (Λ →+* O) := Fintype.ofFinite _
  let S : Set (Option (Λ →+* O) → ℕ) := {x | ∃ (Δ : RL p O Λ) (c : (Λ →+* O) → C),
    IsDetElt ε ψ (x none) Δ ∧ HasOrders C ε (x none) Δ (fun σ => x (some σ)) c}
  let F : (Option (Λ →+* O) → ℕ) → ℝ := fun x =>
    if h : x ∈ S then Real.log (v (Classical.choose (Classical.choose_spec h) τ)) else 0
  have hF : ∀ x (h : x ∈ S) (Δ : RL p O Λ) (c : (Λ →+* O) → C), IsDetElt ε ψ (x none) Δ →
      HasOrders C ε (x none) Δ (fun σ => x (some σ)) c → F x = Real.log (v (c τ)) := by
    intro x h Δ c h1 h2
    simp only [F, dif_pos h]
    obtain ⟨h1', h2'⟩ := Classical.choose_spec (Classical.choose_spec h)
    rw [GlobalTheory.T.psi_determinant_eigen_property p C v O hv ε hε Λ ψ hψ (x none) _ Δ _ _ c h1' h1 h2' h2 τ]
  obtain ⟨f, hf, -⟩ := theta_tensor_exists p C v O hv ε hε Λ τ
  have hne : ∀ N (Δ : RL p O Λ) a (c : (Λ →+* O) → C), HasOrders C ε N Δ a c →
      ((v (c τ) : NNReal) : ℝ) ≠ 0 := fun N Δ a c h =>
    NNReal.coe_ne_zero.2 ((Valuation.ne_zero_iff v).2 (h τ f hf).2.1)
  obtain ⟨κ', hκ'⟩ := GlobalTheory.T.additive_function_on_monoid_linear (Option (Λ →+* O)) S F (by
    rintro x ⟨Δ, c, h1, h2⟩ y ⟨Δ', c', h1', h2'⟩
    obtain ⟨k1, k2⟩ := GlobalTheory.T.determinant_element_product p O C ε Λ ψ _ _ Δ Δ' _ _ c c' h1 h1' h2 h2'
    have hxy : x + y ∈ S := ⟨Δ * Δ', c * c', k1, k2⟩
    refine ⟨hxy, ?_⟩
    rw [hF _ hxy _ _ k1 k2, hF x ⟨Δ, c, h1, h2⟩ _ _ h1 h2, hF y ⟨Δ', c', h1', h2'⟩ _ _ h1' h2',
      Pi.mul_apply, map_mul, NNReal.coe_mul, Real.log_mul (hne _ _ _ _ h2) (hne _ _ _ _ h2')])
  refine ⟨κ' none, fun σ => κ' (some σ), ?_⟩
  intro N Δ a c h1 h2
  let x : Option (Λ →+* O) → ℕ := fun o => o.elim N a
  have hx : x ∈ S := ⟨Δ, c, h1, h2⟩
  rw [← hF x hx Δ c h1 h2, hκ' x hx, Fintype.sum_option, finsum_eq_sum_of_fintype]
  rfl

end GlobalTheory.DetInv
end
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_determinant_valuation_bound : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → ∀ τ : Λ →+* O, ∃ (κ₀ : ℝ) (κ : (Λ →+* O) → ℝ), ∀ (N : ℕ) (Δ : RL p O Λ) (a : (Λ →+* O) → ℕ) (c : (Λ →+* O) → C), IsDetElt ε ψ N Δ → HasOrders C ε N Δ a c → Real.log (v (c τ)) = N * κ₀ + ∑ᶠ σ, (a σ : ℝ) * κ σ := by
  atlas_forward_decl GlobalTheory.DetInv.log_val_lead_linear
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

noncomputable section
namespace GlobalTheory.DetInv

theorem span_p_map_ringEquiv (p : ℕ) {O : Type} [CommRing O] (γ : O ≃+* O) :
    Ideal.span {(p : O)} = Ideal.map (γ : O →+* O) (Ideal.span {(p : O)}) := by
  rw [Ideal.map_span, Set.image_singleton]
  simp

def modPEquiv (p : ℕ) {O : Type} [CommRing O] (γ : O ≃+* O) : ModP O p ≃+* ModP O p :=
  Ideal.quotientEquiv _ _ γ (span_p_map_ringEquiv p γ)

def perfectionEquiv (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [CharP R p] (e : R ≃+* R) :
    Perfection R p ≃+* Perfection R p :=
  RingEquiv.ofRingHom (Perfection.map p (e : R →+* R)) (Perfection.map p (e.symm : R →+* R))
    (RingHom.ext fun x => Perfection.ext (R := R) (p := p) fun n => by simp [Perfection.coeff_map])
    (RingHom.ext fun x => Perfection.ext (R := R) (p := p) fun n => by simp [Perfection.coeff_map])

theorem perfectionEquiv_coeff (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]
    (e : R ≃+* R) (x : Perfection R p) (n : ℕ) :
    Perfection.coeff R p n (perfectionEquiv p e x) = e (Perfection.coeff R p n x) :=
  Perfection.coeff_map p (e : R →+* R) x n

def tiltEquiv (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    (γ : O ≃+* O) : PreTilt O p ≃+* PreTilt O p :=
  perfectionEquiv p (modPEquiv p γ)

theorem tiltEquiv_coeff (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    (γ : O ≃+* O) (x : PreTilt O p) (n : ℕ) (y : O)
    (hy : PreTilt.coeff n x = Ideal.Quotient.mk (Ideal.span {(p : O)}) y) :
    PreTilt.coeff n (tiltEquiv p γ x) = Ideal.Quotient.mk (Ideal.span {(p : O)}) (γ y) := by
  have : PreTilt.coeff n (tiltEquiv p γ x) = modPEquiv p γ (PreTilt.coeff n x) :=
    perfectionEquiv_coeff p (modPEquiv p γ) x n
  rw [this, hy]
  exact Ideal.quotientEquiv_mk _ _ γ _ y

theorem ringEquiv_tilt_theta : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (γ : O ≃+* O), ∃ Γ : PreTilt O p ≃+* PreTilt O p,
    (∀ x, (Γ x).untilt = γ x.untilt) ∧ ∀ a : Ainf p O, WittVector.fontaineTheta O p
      (WittVector.map (Γ : PreTilt O p →+* PreTilt O p) a) = γ (WittVector.fontaineTheta O p a) := by
  intro p _ O _ _ _ γ
  refine ⟨tiltEquiv p γ, fun x => ?_, fun a => ?_⟩
  · exact GlobalTheory.Per.untilt_natural (γ : O →+* O) (tiltEquiv p γ : PreTilt O p →+* PreTilt O p)
      (fun x n y hy => tiltEquiv_coeff p γ x n y hy) x
  · exact GlobalTheory.Per.fontaineTheta_natural (γ : O →+* O) (tiltEquiv p γ : PreTilt O p →+* PreTilt O p)
      (fun x n y hy => tiltEquiv_coeff p γ x n y hy) a

end GlobalTheory.DetInv
end
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_lift_of_ring_automorphism : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (γ : O ≃+* O), ∃ Γ : PreTilt O p ≃+* PreTilt O p, (∀ x, (Γ x).untilt = γ x.untilt) ∧ ∀ a : Ainf p O, WittVector.fontaineTheta O p (WittVector.map (Γ : PreTilt O p →+* PreTilt O p) a) = γ (WittVector.fontaineTheta O p a) := by
  atlas_forward_decl GlobalTheory.DetInv.ringEquiv_tilt_theta
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

noncomputable section
namespace GlobalTheory.GammaAct

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

def wittEquiv (G : PreTilt O p ≃+* PreTilt O p) : Ainf p O ≃+* Ainf p O :=
  RingEquiv.ofRingHom (WittVector.map (G : PreTilt O p →+* PreTilt O p))
    (WittVector.map (G.symm : PreTilt O p →+* PreTilt O p))
    (by ext x n; simp [WittVector.map_coeff])
    (by ext x n; simp [WittVector.map_coeff])

theorem wittEquiv_apply (G : PreTilt O p ≃+* PreTilt O p) (a : Ainf p O) :
    wittEquiv G a = WittVector.map (G : PreTilt O p →+* PreTilt O p) a := rfl

theorem wittEquiv_ofPadic (G : PreTilt O p ≃+* PreTilt O p) (x : ℤ_[p]) :
    wittEquiv G (ofPadic p O x) = ofPadic p O x := by
  rw [wittEquiv_apply, ofPadic, RingHom.comp_apply]
  generalize (WittVector.equiv p).symm.toRingHom x = y
  ext n
  simp only [WittVector.map_coeff]
  exact congrArg (fun f : ZMod p →+* PreTilt O p => f (y.coeff n))
    (RingHom.ext_zmod ((G : PreTilt O p →+* PreTilt O p).comp (ZMod.castHom (dvd_refl p) _)) _)

theorem frob_symm_comm (G : PreTilt O p ≃+* PreTilt O p) (x : PreTilt O p) :
    G ((_root_.frobeniusEquiv (PreTilt O p) p).symm x) =
      (_root_.frobeniusEquiv (PreTilt O p) p).symm (G x) := by
  apply (_root_.frobeniusEquiv (PreTilt O p) p).injective
  rw [RingEquiv.apply_symm_apply, frobeniusEquiv_apply, frobenius_def, ← map_pow,
    ← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]

theorem wittEquiv_phiInv (G : PreTilt O p ≃+* PreTilt O p) (a : Ainf p O) :
    wittEquiv G (phiInv p O a) = phiInv p O (wittEquiv G a) := by
  ext n
  simp [wittEquiv_apply, phiInv, WittVector.map_coeff, frob_symm_comm]

theorem wittEquiv_teich (G : PreTilt O p ≃+* PreTilt O p) (x : PreTilt O p) :
    wittEquiv G (WittVector.teichmuller p x) = WittVector.teichmuller p (G x) := by
  rw [wittEquiv_apply, WittVector.map_teichmuller]; rfl

end GlobalTheory.GammaAct

namespace GlobalTheory.GammaAct

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

def wittAlgEquiv (G : PreTilt O p ≃+* PreTilt O p) : Ainf p O ≃ₐ[ℤ_[p]] Ainf p O :=
  AlgEquiv.ofRingEquiv (f := wittEquiv G) (fun x => wittEquiv_ofPadic G x)

variable (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ]

def tensorEquiv (G : PreTilt O p ≃+* PreTilt O p) : RL p O Λ ≃+* RL p O Λ :=
  (Algebra.TensorProduct.congr (wittAlgEquiv G) (AlgEquiv.refl : Λ ≃ₐ[ℤ_[p]] Λ)).toRingEquiv

theorem tensorEquiv_tmul (G : PreTilt O p ≃+* PreTilt O p) (a : Ainf p O) (l : Λ) :
    tensorEquiv Λ G (a ⊗ₜ l) = wittEquiv G a ⊗ₜ l := rfl

theorem tensorEquiv_symm_tmul (G : PreTilt O p ≃+* PreTilt O p) (a : Ainf p O) (l : Λ) :
    (tensorEquiv Λ G).symm (a ⊗ₜ l) = (wittEquiv G).symm a ⊗ₜ l := rfl

end GlobalTheory.GammaAct

namespace GlobalTheory.GammaAct

section
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem map_root (G : PreTilt O p ≃+* PreTilt O p) (ε : PreTilt O p) :
    G (root ε) = root (G ε) := frob_symm_comm G ε

theorem wittEquiv_xi (G : PreTilt O p ≃+* PreTilt O p) (ε : PreTilt O p) :
    wittEquiv G (xi ε) = xi (G ε) := by
  simp only [xi, map_sum, map_pow, wittEquiv_teich, map_root]

theorem wittEquiv_mu (G : PreTilt O p ≃+* PreTilt O p) (ε : PreTilt O p) :
    wittEquiv G (mu ε) = mu (G ε) := by
  simp only [mu, map_sub, map_one, wittEquiv_teich]

theorem tensorEquiv_inA (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ]
    (G : PreTilt O p ≃+* PreTilt O p) (a : Ainf p O) :
    tensorEquiv Λ G (inA a) = inA (wittEquiv G a) := rfl

end

theorem exists_tensor_action : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (ψ : RL p O Λ →+* RL p O Λ) (γ : O ≃+* O), IsPsi ψ → IsPrimitiveRoot (root ε).untilt p → ∃ (Γ : RL p O Λ ≃+* RL p O Λ) (ε' : PreTilt O p), IsPrimitiveRoot (root ε').untilt p ∧ Γ (inA (xi ε)) = inA (xi ε') ∧ Γ (inA (mu ε)) = inA (mu ε') ∧ (∀ r, Γ (ψ r) = ψ (Γ r)) ∧ ∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → ∃ f', IsTheta ((γ : O →+* O).comp σ) f' ∧ ∀ r, f' (Γ r) = γ (f r) := by
  intro p _ O _ _ _ ε Λ _ _ ψ γ hψ hε
  obtain ⟨G, hu, hθ⟩ := GlobalTheory.T.tilt_lift_of_ring_automorphism p O γ
  refine ⟨tensorEquiv Λ G, G ε, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_root, hu]
    exact hε.map_of_injective γ.injective
  · rw [tensorEquiv_inA, wittEquiv_xi]
  · rw [tensorEquiv_inA, wittEquiv_mu]
  · intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul a l => rw [hψ, tensorEquiv_tmul, tensorEquiv_tmul, hψ, wittEquiv_phiInv]
    | add x y hx hy => simp only [map_add, hx, hy]
  · intro σ f hf
    refine ⟨((γ : O →+* O).comp f).comp ((tensorEquiv Λ G).symm : RL p O Λ →+* RL p O Λ),
      fun a l => ?_, fun r => by simp⟩
    have h := hθ ((wittEquiv G).symm a)
    rw [← wittEquiv_apply, RingEquiv.apply_symm_apply] at h
    show γ (f ((tensorEquiv Λ G).symm (a ⊗ₜ l))) = _ * γ (σ l)
    rw [tensorEquiv_symm_tmul, hf, map_mul, h]

end GlobalTheory.GammaAct
end
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tilt_automorphism_transport : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (ψ : RL p O Λ →+* RL p O Λ) (γ : O ≃+* O), IsPsi ψ → IsPrimitiveRoot (root ε).untilt p → ∃ (Γ : RL p O Λ ≃+* RL p O Λ) (ε' : PreTilt O p), IsPrimitiveRoot (root ε').untilt p ∧ Γ (inA (xi ε)) = inA (xi ε') ∧ Γ (inA (mu ε)) = inA (mu ε') ∧ (∀ r, Γ (ψ r) = ψ (Γ r)) ∧ ∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → ∃ f', IsTheta ((γ : O →+* O).comp σ) f' ∧ ∀ r, f' (Γ r) = γ (f r) := by
  atlas_forward_decl GlobalTheory.GammaAct.exists_tensor_action
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem frobenius_nu {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) :
    WittVector.frobenius (nu ε) = mu ε := by
  unfold nu mu root
  rw [map_sub, map_one, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller,
    frobenius_apply_frobeniusEquiv_symm]

theorem xi_mu_associated : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p),
    IsPrimitiveRoot (root ε).untilt p → ∀ ε' : PreTilt O p, IsPrimitiveRoot (root ε').untilt p →
    Associated (xi ε) (xi ε') ∧ Associated (mu ε) (mu ε') := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε ε' hε'
  obtain ⟨hdom, -, hker, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε
  obtain ⟨-, -, hker', -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε' hε'
  have hA : Associated (xi ε) (xi ε') := by
    rw [← Ideal.span_singleton_eq_span_singleton, ← hker, ← hker']
  refine ⟨hA, ?_⟩
  obtain ⟨hS, hVR⟩ := GlobalTheory.TiltValuation.tilt_isDomain_valuationRing p C v O hv

  have key : ∀ e e' : PreTilt O p, IsPrimitiveRoot (root e).untilt p →
      Associated (xi e) (xi e') → mu e ∣ mu e' := by
    intro e e' he hee'
    obtain ⟨u, hu⟩ := hee'
    have h0 := (GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv e he).1
    have hrel : ∀ i : Fin 1, mu e * WittVector.frobenius ((fun _ : Fin 1 => mu e') i) =
        WittVector.frobenius (mu e) *
          ((fun _ _ => WittVector.frobenius (u : WittVector p (PreTilt O p))) *ᵥ
            (fun _ : Fin 1 => mu e')) i := by
      intro i
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one]
      have hφ : ∀ x : PreTilt O p, WittVector.frobenius (mu x) =
          WittVector.frobenius (xi x) * mu x := fun x => by
        conv_lhs => rw [← xi_mul_nu x, map_mul, frobenius_nu]
      rw [hφ e, hφ e', ← hu, map_mul]
      ring
    exact GlobalTheory.LemY.dvd_of_frobenius_eq p (PreTilt O p) 1 (mu e) _ _ h0 hrel 0
  exact associated_of_dvd_dvd (key ε ε' hε hA) (key ε' ε hε' hA.symm)

end GlobalTheory.DetInv
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.xi_mu_associated_of_primitive_roots : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ ε' : PreTilt O p, IsPrimitiveRoot (root ε').untilt p → Associated (xi ε) (xi ε') ∧ Associated (mu ε) (mu ε') := by
  atlas_forward_decl GlobalTheory.DetInv.xi_mu_associated
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

open WittVector

namespace GlobalTheory

theorem detData_indep_eps : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε ε' : PreTilt O p) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (ψ : RL p O Λ →+* RL p O Λ) (N : ℕ) (Δ : RL p O Λ) (a : (Λ →+* O) → ℕ) (c : (Λ →+* O) → C), Associated (xi ε) (xi ε') → Associated (mu ε) (mu ε') → IsDetElt ε ψ N Δ → HasOrders C ε N Δ a c → ∃ c' : (Λ →+* O) → C, IsDetElt ε' ψ N Δ ∧ HasOrders C ε' N Δ a c' ∧ ∀ σ, v (c' σ) = v (c σ) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε ε' Λ _ _ ψ N Δ a c hxi hmu hD hH
  obtain ⟨u, hu⟩ := hxi
  obtain ⟨w, hw⟩ := hmu
  have key : ∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → ∀ x : Ainf p O,
      f (inA x) = fontaineTheta O p x := by
    intro σ f hf x
    have := hf x 1
    rw [map_one, mul_one] at this
    rw [← this]
    rfl
  have hxd : (inA (xi ε) : RL p O Λ) ^ N ∣ (inA (xi ε') : RL p O Λ) ^ N :=
    pow_dvd_pow_of_dvd (map_dvd _ ⟨(u : Ainf p O), hu.symm⟩) N
  have hmd : (inA (mu ε) : RL p O Λ) ^ N ∣ (inA (mu ε') : RL p O Λ) ^ N :=
    pow_dvd_pow_of_dvd (map_dvd _ ⟨(w : Ainf p O), hw.symm⟩) N
  have hunit : IsUnit (fontaineTheta O p (↑u⁻¹ : Ainf p O)) := (Units.isUnit u⁻¹).map _
  refine ⟨fun σ => algebraMap O C (fontaineTheta O p (↑u⁻¹ : Ainf p O)) ^ a σ * c σ, ?_, ?_, ?_⟩
  · obtain ⟨h1, g, hg, hg2⟩ := hD
    exact ⟨h1.trans hmd, g, hg, hg2.trans hxd⟩
  · intro σ f hf
    obtain ⟨h1, h2, s, t, hs, hst, ht⟩ := hH σ f hf
    refine ⟨h1, mul_ne_zero (pow_ne_zero _ (hunit.map _).ne_zero) h2, s,
      (inA (↑u⁻¹ : Ainf p O) : RL p O Λ) ^ a σ * t, hs, ?_, ?_⟩
    · rw [hst, ← hu, ← mul_assoc, ← mul_pow, ← map_mul, mul_assoc, Units.mul_inv, mul_one]
    · simp only [RingHom.comp_apply, map_mul, map_pow] at ht ⊢
      rw [key σ f hf, ht]
      ring
  · intro σ
    simp only [map_mul, map_pow, hv.one_of_isUnit hunit, one_pow, one_mul]

end GlobalTheory
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_orders_independent_of_root : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε ε' : PreTilt O p) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (ψ : RL p O Λ →+* RL p O Λ) (N : ℕ) (Δ : RL p O Λ) (a : (Λ →+* O) → ℕ) (c : (Λ →+* O) → C), Associated (xi ε) (xi ε') → Associated (mu ε) (mu ε') → IsDetElt ε ψ N Δ → HasOrders C ε N Δ a c → ∃ c' : (Λ →+* O) → C, IsDetElt ε' ψ N Δ ∧ HasOrders C ε' N Δ a c' ∧ ∀ σ, v (c' σ) = v (c σ) := by
  atlas_forward_decl GlobalTheory.detData_indep_eps
end

section
section
noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem detElt_transport_isom : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → ∀ (γ : O ≃+* O), IsIsom C v γ → ∀ (N : ℕ) (Δ : RL p O Λ) (a : (Λ →+* O) → ℕ) (c : (Λ →+* O) → C), IsDetElt ε ψ N Δ → HasOrders C ε N Δ a c → ∃ (Δ' : RL p O Λ) (c' : (Λ →+* O) → C), IsDetElt ε ψ N Δ' ∧ HasOrders C ε N Δ' (fun σ => a ((γ : O →+* O).comp σ)) c' ∧ ∀ σ, v (c' σ) = v (c ((γ : O →+* O).comp σ)) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ ψ hψ γ hγ N Δ a c hΔ hord
  obtain ⟨γC, hγC, hvγ⟩ := hγ
  obtain ⟨Γ, ε', hε', hξ, hμ, hψΓ, hθ⟩ := GlobalTheory.T.exists_tilt_automorphism_transport p O ε Λ ψ γ.symm hψ hε
  have halg : ∀ x : O, algebraMap O C (γ.symm x) = γC.symm (algebraMap O C x) := by
    intro x
    apply γC.injective
    rw [hγC, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  have huniq : ∀ (σ : Λ →+* O) (f g : RL p O Λ →+* O), IsTheta σ f → IsTheta σ g → f = g := by
    intro σ f g hf hg
    apply RingHom.ext
    intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => rw [hf, hg]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hcomp : ∀ σ : Λ →+* O, ((γ.symm : O ≃+* O) : O →+* O).comp ((γ : O →+* O).comp σ) = σ := by
    intro σ
    ext l
    simp
  have hkey : ∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f →
      ∃ f₁ : RL p O Λ →+* O, IsTheta ((γ : O →+* O).comp σ) f₁ ∧ ∀ r, f (Γ r) = γ.symm (f₁ r) := by
    intro σ f hf
    obtain ⟨f₁, hf₁, -⟩ := theta_tensor_exists p C v O hv ε hε Λ ((γ : O →+* O).comp σ)
    obtain ⟨f'', hf'', hf''Γ⟩ := hθ _ f₁ hf₁
    rw [hcomp] at hf''
    have he := huniq σ f'' f hf'' hf
    exact ⟨f₁, hf₁, fun r => by rw [← he]; exact hf''Γ r⟩
  have hΔ' : IsDetElt ε' ψ N (Γ Δ) := by
    obtain ⟨hdiv, g, hg, hgdiv⟩ := hΔ
    refine ⟨?_, Γ g, ?_, ?_⟩
    · rw [← hμ, ← map_pow]; exact map_dvd Γ hdiv
    · rw [← hψΓ, ← map_mul, ← hg]
    · rw [← hξ, ← map_pow]; exact map_dvd Γ hgdiv
  have hord' : HasOrders C ε' N (Γ Δ) (fun σ => a ((γ : O →+* O).comp σ))
      (fun σ => γC.symm (c ((γ : O →+* O).comp σ))) := by
    intro σ f hf
    obtain ⟨f₁, hf₁, hfΓ⟩ := hkey σ f hf
    obtain ⟨hle, hc, s, t, hs, hst, ht⟩ := hord _ f₁ hf₁
    refine ⟨hle, (map_ne_zero γC.symm).mpr hc, Γ s, Γ t, ?_, ?_, ?_⟩
    · simp only [RingHom.comp_apply] at hs ⊢
      rw [hfΓ, halg]
      exact (map_ne_zero γC.symm).mpr hs
    · rw [← map_mul, hst, map_mul, map_pow, hξ]
    · simp only [RingHom.comp_apply] at ht ⊢
      rw [hfΓ, hfΓ, halg, halg, ht, map_mul]
  obtain ⟨hxi, hmu⟩ := GlobalTheory.T.xi_mu_associated_of_primitive_roots p C v O hv ε' hε' ε hε
  obtain ⟨c', h1, h2, h3⟩ := GlobalTheory.T.determinant_orders_independent_of_root p C v O hv ε' ε Λ ψ N (Γ Δ) _ _ hxi hmu hΔ' hord'
  refine ⟨Γ Δ, c', h1, h2, fun σ => ?_⟩
  rw [h3, ← hvγ (γC.symm _), RingEquiv.apply_symm_apply]

end GlobalTheory.DetInv
end
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_determinant_rank_property : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → ∀ (γ : O ≃+* O), IsIsom C v γ → ∀ (N : ℕ) (Δ : RL p O Λ) (a : (Λ →+* O) → ℕ) (c : (Λ →+* O) → C), IsDetElt ε ψ N Δ → HasOrders C ε N Δ a c → ∃ (Δ' : RL p O Λ) (c' : (Λ →+* O) → C), IsDetElt ε ψ N Δ' ∧ HasOrders C ε N Δ' (fun σ => a ((γ : O →+* O).comp σ)) c' ∧ ∀ σ, v (c' σ) = v (c ((γ : O →+* O).comp σ)) := by
  atlas_forward_decl GlobalTheory.DetInv.detElt_transport_isom
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem detConst_linear_isom : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ τ₀ : Λ →+* O, ∃ (κ₀ : ℝ) (κ : (Λ →+* O) → ℝ), ∀ (γ : O ≃+* O), IsIsom C v γ → ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) ι (lam : C), IsIota C D ((γ : O →+* O).comp τ₀) N ι → lam ≠ 0 → ι '' (detLattice C (actT D) ((γ : O →+* O).comp τ₀) N : Set (detLine C (actT D) ((γ : O →+* O).comp τ₀) N)) = (fun w => lam • w) '' (detLattice C (actH D) ((γ : O →+* O).comp τ₀) N : Set (detLine C (actH D) ((γ : O →+* O).comp τ₀) N)) → Real.log (v lam) = N * κ₀ + ∑ᶠ σ, (D.lieRank ((γ : O →+* O).comp σ) : ℝ) * κ σ := by
  classical
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ τ₀
  obtain ⟨-, -, ψ, -, hψ, -⟩ := GlobalTheory.DetInv.psi_phi_tensor p O Λ
  obtain ⟨κ₀, κ, hlin⟩ := GlobalTheory.T.psi_determinant_valuation_bound p C v O hv ε hε Λ ψ hψ τ₀
  obtain ⟨hfin, -⟩ := GlobalTheory.card_ringHom_to_integers_eq_finrank p C v O hv Λ
  obtain ⟨-, -, -, -, hθν, -, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε
  set t : ℝ := Real.log (v (algebraMap O C (WittVector.fontaineTheta O p (nu ε)))) with ht
  refine ⟨κ₀, fun σ => κ σ - if σ = τ₀ then t else 0, ?_⟩
  intro γ hγ N h hh D ι lam hι hlam hlat
  obtain ⟨Δ, c, hΔ, hord, hc⟩ :=
    GlobalTheory.T.psi_determinant_element_property p C v O hv ε hε Λ ψ hψ N h hh D ((γ : O →+* O).comp τ₀) ι lam hι hlat
  obtain ⟨Δ', c', hΔ', hord', hc'⟩ :=
    GlobalTheory.T.psi_determinant_rank_property p C v O hv ε hε Λ ψ hψ γ hγ N Δ D.lieRank c hΔ hord
  have key := hlin N Δ' _ c' hΔ' hord'
  rw [hc' τ₀, hc] at key
  have hv0 : v lam ≠ 0 := (Valuation.ne_zero_iff v).mpr hlam
  have hθ0 : algebraMap O C (WittVector.fontaineTheta O p (nu ε)) ≠ 0 := by
    intro h0
    apply hθν
    apply hv.hom_inj
    rw [h0, map_zero]
  have hvθ : v (algebraMap O C (WittVector.fontaineTheta O p (nu ε))) ≠ 0 :=
    (Valuation.ne_zero_iff v).mpr hθ0
  have hlog : Real.log ((v lam * v (algebraMap O C (WittVector.fontaineTheta O p (nu ε))) ^
      D.lieRank ((γ : O →+* O).comp τ₀) : NNReal) : ℝ) =
      Real.log (v lam) + (D.lieRank ((γ : O →+* O).comp τ₀) : ℝ) * t := by
    rw [NNReal.coe_mul, NNReal.coe_pow, Real.log_mul, Real.log_pow]
    · exact_mod_cast hv0
    · exact pow_ne_zero _ (by exact_mod_cast hvθ)
  rw [hlog] at key
  haveI := hfin
  letI := Fintype.ofFinite (Λ →+* O)
  rw [finsum_eq_sum_of_fintype] at key ⊢
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  linarith

end GlobalTheory.DetInv
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_embedding_determinant_property : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ τ₀ : Λ →+* O, ∃ (κ₀ : ℝ) (κ : (Λ →+* O) → ℝ), ∀ (γ : O ≃+* O), IsIsom C v γ → ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) ι (lam : C), IsIota C D ((γ : O →+* O).comp τ₀) N ι → lam ≠ 0 → ι '' (detLattice C (actT D) ((γ : O →+* O).comp τ₀) N : Set (detLine C (actT D) ((γ : O →+* O).comp τ₀) N)) = (fun w => lam • w) '' (detLattice C (actH D) ((γ : O →+* O).comp τ₀) N : Set (detLine C (actH D) ((γ : O →+* O).comp τ₀) N)) → Real.log (v lam) = N * κ₀ + ∑ᶠ σ, (D.lieRank ((γ : O →+* O).comp σ) : ℝ) * κ σ := by
  atlas_forward_decl GlobalTheory.DetInv.detConst_linear_isom
end
