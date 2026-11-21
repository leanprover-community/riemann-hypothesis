import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizationAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFreePDThickeningFrameValuationIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentLinearKillsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstFormalGroupLawNatMultipleEqCoboundarySum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPowerSeriesFamilyToFractionsFormalGroupLawNat
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffSubstOfForallConstantCoeffZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualBasisCoordMemMaximalIdealOfForallApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstSubIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedInOfQuasiLogarithm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChgPfTP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfSquareZeroFrameReflTransGenCyclicChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmBasisLiftPdThickening
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftQuasiLogarithmAlongPdThickening
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedQuasiLogBasisPDivGroupLieDual
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFreePDThickeningFrameValuationIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentOfQuasiLogarithm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentLinearKillsIntegralStatement

section
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem map_algebraMap_powerSeriesEvalTwoGroups : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (d : ℕ) (τ : Type)
    (t : MvPowerSeries (Fin d ⊕ Fin d) R) (u v : Fin d → MvPowerSeries τ R),
    (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
    map (algebraMap R S) (at2 t u v) = at2 (map (algebraMap R S) t) (up S u) (up S v) := by
  intro R S _ _ _ d τ t u v hu hv
  have ha : HasSubst (Sum.elim u v) :=
    hasSubst_of_constantCoeff_zero (fun i => by cases i <;> simp [hu, hv])
  rw [at2, at2, map_subst ha]
  congr 1
  funext i
  cases i <;> rfl

end GlobalTheory.QLog
end

section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.IdealAt2

theorem coeff_powerSeriesEvalTwoGroups_mem_ideal : ∀ (R : Type) [CommRing R] (d : ℕ) (τ : Type) (I : Ideal R)
    (t : MvPowerSeries (Fin d ⊕ Fin d) R) (u v : Fin d → MvPowerSeries τ R),
    (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
    (∀ α, coeff α t ∈ I) → ∀ α, coeff α (at2 t u v) ∈ I := by
  intro R _ d τ I t u v hu hv ht α
  have hs : HasSubst (Sum.elim u v) :=
    hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [hu, hv]
  rw [at2, coeff_subst hs]
  refine finsum_induction (fun x => x ∈ I) I.zero_mem (fun x y hx hy => I.add_mem hx hy) ?_
  intro e
  rw [smul_eq_mul]
  exact I.mul_mem_right _ (ht e)

end GlobalTheory.IdealAt2
end

section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem Chart.ev_mem_ideal_smul_add_p (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ)
    (c : QLog.Chart G d) (n : ℕ) (I : Ideal O) (h : MvPowerSeries (Fin d) O) :
    (∀ α, coeff α h ∈ I) → ∃ a ∈ I • (⊤ : Submodule O (G.A n)), ∃ b : G.A n,
      c.ev n h = a + (p : G.A n) * b := by
  intro hI
  classical
  obtain ⟨N, hN⟩ := (c.isEval n).2 1
  let S : Finset (Fin d →₀ ℕ) := Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => N)
  let h₁ : MvPowerSeries (Fin d) O := ∑ α ∈ S, monomial α (coeff α h)
  have hmon : ∀ α, (monomial α (coeff α h) : MvPowerSeries (Fin d) O) =
      coeff α h • monomial α (1 : O) := by
    intro α
    ext β
    simp only [coeff_monomial, coeff_smul]
    split_ifs <;> simp
  have hcoeff : ∀ β ∈ S, coeff β h₁ = coeff β h := by
    intro β hβ
    simp only [h₁, map_sum, coeff_monomial]
    rw [Finset.sum_eq_single_of_mem β hβ]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
  have h₂ : (p : G.A n) ^ 1 ∣ c.ev n (h - h₁) := by
    apply hN
    intro β hβ
    have hmem : β ∈ S := by
      simp only [S, Finset.mem_Iic]
      intro i
      show β i ≤ N
      have : β i ≤ β.degree := by
        by_cases h0 : β i = 0
        · omega
        rw [Finsupp.degree]
        exact Finset.single_le_sum (f := fun j => β j) (fun _ _ => Nat.zero_le _)
          (by simpa using h0)
      omega
    rw [map_sub, hcoeff β hmem, sub_self]
  obtain ⟨b, hb⟩ := h₂
  refine ⟨c.ev n h₁, ?_, b, ?_⟩
  · simp only [h₁, map_sum]
    refine Submodule.sum_mem _ fun α _ => ?_
    rw [hmon, map_smul]
    exact Submodule.smul_mem_smul (hI α) Submodule.mem_top
  · rw [map_sub, pow_one] at hb
    rw [← hb]; ring

end GlobalTheory
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.PadicMvPowerSeriesExt

theorem eq_zero_of_forall_pow_dvd (p : ℕ) (O : Type) [CommRing O]
    [IsHausdorff (Ideal.span {(p : O)}) O] (A : Type) [CommRing A] [Algebra O A]
    [Module.Projective O A] (x : A) (hx : ∀ m : ℕ, (p : A) ^ m ∣ x) : x = 0 := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective O A)
  have h0 : s x = 0 := by
    ext a
    refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(p : O)}) O) _ fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    obtain ⟨y, hy⟩ := hx n
    have hxy : x = ((p : O) ^ n) • y := by
      rw [Algebra.smul_def, map_pow, map_natCast, hy]
    rw [hxy, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact dvd_mul_right _ _
  have h1 := LinearMap.congr_fun hs x
  rw [LinearMap.comp_apply, h0, map_zero, LinearMap.id_apply] at h1
  exact h1.symm

theorem algHom_ext : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Projective O A] (F F' : MvPowerSeries σ O →ₐ[O] A), (∀ i, F (X i) = F' (X i)) → (∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A) ^ m ∣ F f) → (∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A) ^ m ∣ F' f) → F = F' := by
  classical
  intro p O _ _ σ _ A _ _ _ _ F F' hX hF hF'
  apply AlgHom.ext
  intro f
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_pow_dvd p O A _ fun m => ?_
  obtain ⟨N₁, hN₁⟩ := hF m
  obtain ⟨N₂, hN₂⟩ := hF' m
  set g := MvPowerSeries.trunc' O (Finsupp.equivFunOnFinite.symm fun _ : σ => max N₁ N₂) f with hg
  have hpoly : F.comp (MvPolynomial.coeToMvPowerSeries.algHom O) =
      F'.comp (MvPolynomial.coeToMvPowerSeries.algHom O) :=
    MvPolynomial.algHom_ext fun i => by simpa using hX i
  have hg' : F (g : MvPowerSeries σ O) = F' (g : MvPowerSeries σ O) := by
    simpa using DFunLike.congr_fun hpoly g
  have hlow : ∀ α : σ →₀ ℕ, α.degree < max N₁ N₂ →
      MvPowerSeries.coeff α (f - (g : MvPowerSeries σ O)) = 0 := by
    intro α hα
    rw [map_sub, MvPolynomial.coeff_coe, hg, MvPowerSeries.coeff_trunc', if_pos, sub_self]
    intro i
    exact (Finsupp.le_degree i α).trans (by simpa using hα.le)
  have hdiff : F f - F' f = F (f - (g : MvPowerSeries σ O)) - F' (f - (g : MvPowerSeries σ O)) := by
    rw [map_sub, map_sub, hg']
    ring
  rw [hdiff]
  exact dvd_sub (hN₁ _ fun α h => hlow α (lt_of_lt_of_le h (le_max_left _ _)))
    (hN₂ _ fun α h => hlow α (lt_of_lt_of_le h (le_max_right _ _)))

end GlobalTheory.PadicMvPowerSeriesExt
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicContinuous_mvPowerSeries_algHom_ext : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Projective O A] (F F' : MvPowerSeries σ O →ₐ[O] A), (∀ i, F (X i) = F' (X i)) → (∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A) ^ m ∣ F f) → (∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A) ^ m ∣ F' f) → F = F' := by
  atlas_forward_decl GlobalTheory.PadicMvPowerSeriesExt.algHom_ext
end

section
set_option autoImplicit false

noncomputable section

open MvPowerSeries TensorProduct GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup WithConv

namespace GlobalTheory.EvMul

theorem coeff_subst_eq_zero_of_degree {R : Type} [CommRing R] {σ τ : Type} [Finite σ]
    {a : σ → MvPowerSeries τ R} (ha : ∀ i, constantCoeff (a i) = 0) {N : ℕ}
    {f : MvPowerSeries σ R} (hf : ∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0)
    (β : τ →₀ ℕ) (hβ : β.degree < N) : coeff β (subst a f) = 0 := by
  rw [coeff_subst (hasSubst_of_constantCoeff_zero ha)]
  refine finsum_eq_zero_of_forall_eq_zero fun α => ?_
  by_cases h : α.degree < N
  · rw [hf α h, zero_smul]
  · rw [coeff_of_lt_order (f := α.prod fun s e => a s ^ e) (d := β) ?_, smul_zero]
    refine lt_of_lt_of_le (b := ((α.degree : ℕ) : ℕ∞)) (by exact_mod_cast (by omega : β.degree < α.degree)) ?_
    rw [Finsupp.prod]
    refine le_trans ?_ (le_order_prod _ _)
    show ((∑ i ∈ α.support, α i : ℕ) : ℕ∞) ≤ _
    push_cast
    exact Finset.sum_le_sum fun i _ => le_order_pow_of_constantCoeff_eq_zero _ (ha i)

theorem constantCoeff_nmul {R : Type} [CommRing R] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : ∀ i, constantCoeff (μ i) = 0) (k : ℕ) (i : Fin d) :
    constantCoeff (nmul μ k i) = 0 := by
  induction k generalizing i with
  | zero => simp [nmul]
  | succ k ih =>
    have h : ∀ j, constantCoeff (Sum.elim (nmul μ k) (fun l => (X l : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j)
      · exact ih j
      · exact constantCoeff_X _
    have e : nmul μ (k + 1) i = at2 (μ i) (nmul μ k) (fun l => X l) := by
      unfold nmul; rw [Function.iterate_succ_apply']; rfl
    rw [e, at2]
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h) h (hμ i)

end GlobalTheory.EvMul

namespace GlobalTheory.EvMul

theorem mulBy_succ_apply {O A : Type} [CommRing O] [CommRing A] [Bialgebra O A] [Coalgebra.IsCocomm O A] (k : ℕ) (a : A) :
    PDiv.mulBy O A (k + 1) a = Algebra.TensorProduct.lmul' O
      (Algebra.TensorProduct.map (PDiv.mulBy O A k : A →ₐ[O] A) (AlgHom.id O A) (Coalgebra.comul a)) := by
  rw [PDiv.mulBy, pow_succ]
  rfl

theorem mulBy_zero_apply {O A : Type} [CommRing O] [CommRing A] [Bialgebra O A] [Coalgebra.IsCocomm O A] (a : A) :
    PDiv.mulBy O A 0 a = algebraMap O A (Coalgebra.counit a) := by
  rw [PDiv.mulBy, pow_zero]
  rfl

end GlobalTheory.EvMul

namespace GlobalTheory.EvMul

variable {p : ℕ} {O : Type} [CommRing O]

theorem pow_dvd_map {A B : Type} [CommRing A] [CommRing B] [Algebra O A] [Algebra O B]
    (φ : A →ₐ[O] B) {m : ℕ} {a : A} (h : (p : A) ^ m ∣ a) : (p : B) ^ m ∣ φ a := by
  obtain ⟨y, rfl⟩ := h
  exact ⟨φ y, by rw [map_mul, map_pow, map_natCast]⟩

theorem cont_subst {σ τ : Type} [Finite τ] {A : Type} [CommRing A] [Algebra O A]
    (E : MvPowerSeries σ O →ₐ[O] A)
    (hE : ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A) ^ m ∣ E f)
    {a : τ → MvPowerSeries σ O} (ha : ∀ i, constantCoeff (a i) = 0) :
    ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : τ →₀ ℕ, α.degree < N → coeff α f = 0) →
      (p : A) ^ m ∣ E.comp (substAlgHom (R := O) (hasSubst_of_constantCoeff_zero ha)) f := by
  intro m
  obtain ⟨N, hN⟩ := hE m
  exact ⟨N, fun f hf => by
    rw [AlgHom.comp_apply, substAlgHom_apply]
    exact hN _ (coeff_subst_eq_zero_of_degree ha hf)⟩

variable [IsAdicComplete (Ideal.span {(p : O)}) O] {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d)

theorem ev_subst_of_gen (n k : ℕ)
    (hk : ∀ i, c.ev n (nmul c.μ k i) = PDiv.mulBy O (G.A n) k (c.x n i))
    (h : MvPowerSeries (Fin d) O) :
    c.ev n (subst (nmul c.μ k) h) = PDiv.mulBy O (G.A n) k (c.ev n h) := by
  have ha := constantCoeff_nmul c.isLaw.const k
  have gens : ∀ i, ((c.ev n).comp (substAlgHom (R := O) (hasSubst_of_constantCoeff_zero ha))) (X i) =
      ((PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n).comp (c.ev n)) (X i) := by
    intro i
    rw [AlgHom.comp_apply, AlgHom.comp_apply, substAlgHom_X, (c.isEval n).1, hk]
    rfl
  have cont' : ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : Fin d →₀ ℕ, α.degree < N → coeff α f = 0) →
      (p : G.A n) ^ m ∣ ((PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n).comp (c.ev n)) f := by
    intro m
    obtain ⟨N, hN⟩ := (c.isEval n).2 m
    exact ⟨N, fun f hf => by
      rw [AlgHom.comp_apply]
      exact pow_dvd_map (PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n) (hN f hf)⟩
  have e := GlobalTheory.T.padicContinuous_mvPowerSeries_algHom_ext p O (Fin d) (G.A n) _ _ gens (cont_subst (c.ev n) (c.isEval n).2 ha) cont'
  have := DFunLike.congr_fun e h
  rw [AlgHom.comp_apply, AlgHom.comp_apply, substAlgHom_apply] at this
  exact this

end GlobalTheory.EvMul

namespace GlobalTheory.EvMul

variable {p : ℕ} {O : Type} [CommRing O]
variable [IsAdicComplete (Ideal.span {(p : O)}) O] {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d)

theorem ev_nmul (n k : ℕ) (i : Fin d) :
    c.ev n (nmul c.μ k i) = PDiv.mulBy O (G.A n) k (c.x n i) := by
  induction k generalizing i with
  | zero =>
    rw [mulBy_zero_apply, c.aug, map_zero]
    exact map_zero _
  | succ k ih =>
    have hs : ∀ j, constantCoeff (Sum.elim (nmul c.μ k) (fun l => (X l : MvPowerSeries (Fin d) O)) j) = 0 := by
      rintro (j | j)
      · exact constantCoeff_nmul c.isLaw.const k j
      · exact constantCoeff_X _
    set Θ := (c.ev n).comp (substAlgHom (R := O) (hasSubst_of_constantCoeff_zero hs)) with hΘ
    set Λ := (Algebra.TensorProduct.lmul' O).comp ((Algebra.TensorProduct.map
      (PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n) (AlgHom.id O (G.A n))).comp (c.ev₂ n)) with hΛ
    have gens : ∀ j, Θ (X j) = Λ (X j) := by
      rintro (j | j)
      · rw [hΘ, hΛ, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, substAlgHom_X,
          (c.isEval₂ n).1]
        simp only [Sum.elim_inl, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
          Algebra.TensorProduct.lmul'_apply_tmul, map_one, mul_one]
        exact ih j
      · rw [hΘ, hΛ, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, substAlgHom_X,
          (c.isEval₂ n).1]
        simp only [Sum.elim_inr, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
          Algebra.TensorProduct.lmul'_apply_tmul, map_one, one_mul]
        exact (c.isEval n).1 j
    have cont' : ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < N → coeff α f = 0) →
        (p : G.A n) ^ m ∣ Λ f := by
      intro m
      obtain ⟨N, hN⟩ := (c.isEval₂ n).2 m
      exact ⟨N, fun f hf => by
        rw [hΛ, AlgHom.comp_apply, AlgHom.comp_apply]
        exact pow_dvd_map _ (pow_dvd_map _ (hN f hf))⟩
    have e : Θ = Λ := GlobalTheory.T.padicContinuous_mvPowerSeries_algHom_ext p O (Fin d ⊕ Fin d) (G.A n) Θ Λ gens
      (cont_subst (c.ev n) (c.isEval n).2 hs) cont'
    have e1 : nmul c.μ (k + 1) i = subst (Sum.elim (nmul c.μ k) fun l => X l) (c.μ i) := by
      unfold nmul; rw [Function.iterate_succ_apply']; rfl
    have e2 := DFunLike.congr_fun e (c.μ i)
    rw [hΘ, hΛ, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, substAlgHom_apply,
      c.comul] at e2
    rw [e1, e2, mulBy_succ_apply]

theorem ev_subst_nmul : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d)
    (n k : ℕ) (h : MvPowerSeries (Fin d) O),
    c.ev n (subst (nmul c.μ k) h) = PDiv.mulBy O (G.A n) k (c.ev n h) := by
  intro p _ O _ _ G d c n k h
  exact ev_subst_of_gen c n k (ev_nmul c n k) h

end GlobalTheory.EvMul
end
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TangentIndep

theorem subst_nmul_eq (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (g : MvPowerSeries (Fin d) R) (n : ℕ) :
    subst (nmul μ n) g = C (constantCoeff g) + (n : R) • g +
      ∑ k ∈ Finset.range n, at2 (cob1 μ g) (nmul μ k) (fun i => X i) := _root_.GlobalTheory.QLog.subst_nmul_eq R d μ hμ g n

theorem up_nmul_eq (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) :
    up S (nmul μ n) = nmul (up S μ) n := _root_.GlobalTheory.QLog.up_nmul R S d μ hμ n

theorem map_at2_eq (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (d : ℕ) (τ : Type)
    (t : MvPowerSeries (Fin d ⊕ Fin d) R) (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    map (algebraMap R S) (at2 t u v) = at2 (map (algebraMap R S) t) (up S u) (up S v) := _root_.GlobalTheory.QLog.map_algebraMap_powerSeriesEvalTwoGroups R S d τ t u v hu hv

theorem constantCoeff_subst_eq (R : Type) [CommRing R] (σ τ : Type) [Finite σ] (a : σ → MvPowerSeries τ R)
    (ha : ∀ i, constantCoeff (a i) = 0) (g : MvPowerSeries σ R) :
    constantCoeff (subst a g) = constantCoeff g := _root_.GlobalTheory.constantCoeff_subst_of_constantCoeff_zero R σ τ a ha g

theorem coeff_powerSeriesEvalTwoGroups_mem_ideal (R : Type) [CommRing R] (d : ℕ) (τ : Type) (I : Ideal R)
    (t : MvPowerSeries (Fin d ⊕ Fin d) R) (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (ht : ∀ α, coeff α t ∈ I) (α : τ →₀ ℕ) : coeff α (at2 t u v) ∈ I := _root_.GlobalTheory.IdealAt2.coeff_powerSeriesEvalTwoGroups_mem_ideal R d τ I t u v hu hv ht α

theorem ev_mem_smul_add (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d)
    (n : ℕ) (I : Ideal O) (h : MvPowerSeries (Fin d) O) (hh : ∀ α, coeff α h ∈ I) :
    ∃ a ∈ I • (⊤ : Submodule O (G.A n)), ∃ b : G.A n, c.ev n h = a + (p : G.A n) * b := _root_.GlobalTheory.Chart.ev_mem_ideal_smul_add_p p O G d c n I h hh

theorem ev_subst_nmul (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]
    (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n k : ℕ) (h : MvPowerSeries (Fin d) O) :
    c.ev n (subst (nmul c.μ k) h) = PDiv.mulBy O (G.A n) k (c.ev n h) := _root_.GlobalTheory.EvMul.ev_subst_nmul p O G d c n k h

theorem repr_mem_maximalIdeal (O : Type) [CommRing O] [IsLocalRing O] (M : Type) [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] (k : ℕ) (lb : Module.Basis (Fin k) O (Module.Dual O M))
    (l : Module.Dual O M) (hl : ∀ w, l w ∈ IsLocalRing.maximalIdeal O) (j : Fin k) :
    lb.repr l j ∈ IsLocalRing.maximalIdeal O := _root_.GlobalTheory.dualBasis_coord_mem_maximalIdeal O M k lb l hl j

theorem nmul_const (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (k : ℕ) (i : Fin d) : constantCoeff (nmul μ k i) = 0 := by
  induction k generalizing i with
  | zero => simp [nmul]
  | succ k ih =>
    have h : nmul μ (k + 1) = op μ (nmul μ k) (fun i => X i) := by
      simp only [nmul]; rw [Function.iterate_succ_apply']
    rw [h, op, at2, constantCoeff_subst_eq R _ _ _ (fun x => by cases x with | inl a => exact ih a | inr a => simp), hμ]

theorem powerSeriesEvalTwoGroups_add (R : Type) [CommRing R] (d : ℕ) (τ : Type) (a b : MvPowerSeries (Fin d ⊕ Fin d) R)
    (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    at2 (a + b) u v = at2 a u v + at2 b u v := by
  unfold at2
  exact subst_add (hasSubst_of_constantCoeff_zero fun x => by cases x with | inl i => exact hu i | inr i => exact hv i) a b

theorem constantCoeff_formalGroupLawCoboundaryOne (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (g : MvPowerSeries (Fin d) R) :
    constantCoeff (cob1 μ g) = - constantCoeff g := by
  simp only [cob1, inL, inR, map_sub]
  rw [constantCoeff_subst_eq R _ _ _ hμ, constantCoeff_subst_eq R _ _ _ (fun _ => constantCoeff_X _), constantCoeff_subst_eq R _ _ _ (fun _ => constantCoeff_X _)]
  ring

theorem QL_comb (O E : Type) [CommRing O] [CommRing E] [Algebra O E] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (f g : MvPowerSeries (Fin d) E) (a : O) (hf : QL μ ⊤ f) (hg : QL μ ⊤ g) :
    QL μ ⊤ (f + algebraMap O E a • g) := by
  have hμE : ∀ i, constantCoeff (up E μ i) = 0 := fun i => by simp [up, hμ]
  refine ⟨?_, fun i => ?_, fun α => ?_⟩
  · simp [hf.1, hg.1]
  · obtain ⟨x, -, hx⟩ := hf.2.1 i
    obtain ⟨y, -, hy⟩ := hg.2.1 i
    refine ⟨x + a * y, trivial, ?_⟩
    simp only [lin] at hx hy ⊢
    rw [map_add, coeff_smul, hx, hy, map_add, map_mul]
  · obtain ⟨x, -, hx⟩ := hf.2.2 α
    obtain ⟨y, -, hy⟩ := hg.2.2 α
    refine ⟨x + a * y, trivial, ?_⟩
    rw [formalCoboundary_add hμE, formalCoboundary_smul hμE, map_add, coeff_smul, hx, hy, map_add, map_mul]

theorem tangent_coords_nonunit : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) E) (lb : Module.Basis (Fin k) O G.dual.Lie), (∀ i, QL c.μ ⊤ (e i)) → (∀ j, c.IsLie (e (Sum.inr j)) (lb j)) → (∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0) → ∀ (b : Fin k → O) (s : MvPowerSeries (Fin d) O), (∀ α, ∃ o : O, ¬IsUnit o ∧ coeff α (cob1 (up E c.μ) (comb (Sum.elim 0 b) e) - map (algebraMap O E) (cob1 c.μ s)) = algebraMap O E o) → ∀ j, ¬IsUnit (b j) := by
  intro p _ K _ _ _ v O _ _ _ _ _ hv G d c E _ _ hF k e lb hQL hLie hlog b s hH j
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hmem : ∀ o : O, o ∈ IsLocalRing.maximalIdeal O ↔ ¬IsUnit o := fun o => IsLocalRing.mem_maximalIdeal o
  have hpm : (p : O) ∈ IsLocalRing.maximalIdeal O := (hmem _).2 Fact.out
  have hμ : ∀ i, constantCoeff (c.μ i) = 0 := c.isLaw.const
  let f := comb (Sum.elim 0 b) e
  let l : G.dual.Lie := ∑ j, b j • lb j
  have lin : ∀ (f g : MvPowerSeries (Fin d) E) (l l' : G.dual.Lie) (a : O), c.IsLie f l → c.IsLie g l' →
      QL c.μ ⊤ f → QL c.μ ⊤ g → c.IsLie (f + algebraMap O E a • g) (l + a • l') :=
    fun f g l l' a hf hg => (_root_.GlobalTheory.LieLin.main p K v O hv G d c E hF f g l l' a hf hg).1
  have h00 : c.IsLie (0 : MvPowerSeries (Fin d) E) 0 := by
    have := lin _ _ _ _ (-1) (hLie j) (hLie j) (hQL _) (hQL _)
    simpa using this
  have hsum : ∀ S : Finset (Fin k), QL c.μ ⊤ (∑ i ∈ S, algebraMap O E (b i) • e (Sum.inr i)) ∧
      c.IsLie (∑ i ∈ S, algebraMap O E (b i) • e (Sum.inr i)) (∑ i ∈ S, b i • lb i) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨?_, by simpa using h00⟩
      simpa using QL_comb O E d c.μ hμ _ _ (-1) (hQL (Sum.inr j)) (hQL (Sum.inr j))
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm, add_comm (b a • lb a)]
      exact ⟨QL_comb O E d c.μ hμ _ _ (b a) ih.1 (hQL _), lin _ _ _ _ (b a) ih.2 (hLie a) ih.1 (hQL _)⟩
  have hf_eq : f = ∑ i, algebraMap O E (b i) • e (Sum.inr i) := by
    simp [f, comb, Fintype.sum_sum_type]
  have hfl : c.IsLie f l := by rw [hf_eq]; exact (hsum Finset.univ).2

  have hμE : ∀ i, constantCoeff (up E c.μ i) = 0 := fun i => by simp [up, hμ]
  choose t ht using hH
  let T : MvPowerSeries (Fin d ⊕ Fin d) O := fun α => t α
  have hT : ∀ α, coeff α T = t α := fun α => rfl
  have hcob : cob1 (up E c.μ) f = map (algebraMap O E) (cob1 c.μ s + T) := by
    ext α
    have h := (ht α).2
    rw [map_sub, sub_eq_iff_eq_add] at h
    rw [map_add, map_add, h]
    simp only [coeff_map, hT]
    ring
  have hf0 : constantCoeff f = algebraMap O E (constantCoeff s - t 0) := by
    have h := (ht 0).2
    rw [coeff_zero_eq_constantCoeff_apply, map_sub, constantCoeff_formalGroupLawCoboundaryOne E d _ hμE, constantCoeff_map,
      constantCoeff_formalGroupLawCoboundaryOne O d _ hμ] at h
    rw [map_sub, ← h, map_neg]; ring
  have hnc := nmul_const O d c.μ hμ
  let s' : MvPowerSeries (Fin d) O := -C (constantCoeff s - t 0) -
    ∑ k ∈ Finset.range p, at2 (cob1 c.μ s + T) (nmul c.μ k) (fun i => X i)
  have hX : up E (fun i : Fin d => (X i : MvPowerSeries (Fin d) O)) = fun i => X i := by
    funext i; simp [up, map_X]
  have hs' : map (algebraMap O E) s' = defect c.μ (p ^ 1) f := by
    rw [defect, pow_one, up_nmul_eq O E d c.μ hμ, subst_nmul_eq E d _ hμE f p, hcob, hf0]
    simp only [s', map_sub, map_neg, map_sum, map_C]
    rw [Finset.sum_congr rfl (fun k _ => map_at2_eq O E d (Fin d) _ _ _ (hnc k) (fun i => constantCoeff_X i))]
    simp only [hX, up_nmul_eq O E d c.μ hμ]
    abel
  have hs'2 : s' = C (t 0) + (p : O) • s - subst (nmul c.μ p) s -
      ∑ k ∈ Finset.range p, at2 T (nmul c.μ k) (fun i => X i) := by
    rw [subst_nmul_eq O d c.μ hμ s p]
    simp only [s']
    rw [Finset.sum_congr rfl (fun k _ => powerSeriesEvalTwoGroups_add O d (Fin d) _ _ _ _ (hnc k) (fun i => constantCoeff_X i)),
      Finset.sum_add_distrib, map_sub]
    abel
  have key : ∀ w : G.dual.omega, l w ∈ IsLocalRing.maximalIdeal O := by
    intro w
    obtain ⟨φ₀, hφ₀⟩ := AugCot.d_surjective _ (w.1 1)
    set φ : CartierDual O (G.A 1) := φ₀ - algebraMap O _ (Coalgebra.counit (R := O) φ₀) with hφdef
    have hφd : PDiv.dUnit O φ = w.1 1 := by
      rw [hφdef, PDiv.dUnit, map_sub, AugCot.d_algebraMap, sub_zero]; exact hφ₀
    have hφ1 : φ 1 = 0 := by
      rw [hφdef]
      simp [Algebra.algebraMap_eq_smul_one, CartierDual.counit_apply]

    have hL := hfl.2 1 w φ s' hφd hs'
    have hA : ∀ r : O, φ (algebraMap O (G.A 1) r) = 0 := fun r => by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hφ1, smul_zero]
    have hev : φ (c.ev 1 s') ∈ IsLocalRing.maximalIdeal O := by
      have h1 := G.mulBy_pow_self 1 (c.ev 1 s)
      rw [pow_one] at h1
      have hC : c.ev 1 (C (t 0)) = algebraMap O _ (t 0) := (c.ev 1).commutes (t 0)
      rw [hs'2]
      simp only [map_sub, map_add, map_smul, map_sum, ev_subst_nmul p O G d c 1 p s, h1, hC]
      have hA' : ∀ r : O, φ.ofConv (algebraMap O (G.A 1) r) = 0 := hA
      rw [hA', hA', zero_add, sub_zero, smul_eq_mul]
      refine Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hpm) (Ideal.sum_mem _ fun k _ => ?_)
      obtain ⟨a, ha, b', hb'⟩ := ev_mem_smul_add p O G d c 1 (IsLocalRing.maximalIdeal O) _
        (coeff_powerSeriesEvalTwoGroups_mem_ideal O d (Fin d) _ T _ _ (hnc k) (fun i => constantCoeff_X i) (fun α => (hmem _).2 (ht α).1))
      rw [hb', map_add]
      refine Ideal.add_mem _ ?_ ?_
      · have hle : IsLocalRing.maximalIdeal O • (⊤ : Submodule O (G.A 1)) ≤
            Submodule.comap φ.ofConv (IsLocalRing.maximalIdeal O) :=
          Submodule.smul_le.2 fun r hr x _ => by
            rw [Submodule.mem_comap, map_smul, smul_eq_mul]
            exact Ideal.mul_mem_right _ _ hr
        exact hle ha
      · rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
        exact Ideal.mul_mem_right _ _ hpm
    obtain ⟨q, hq⟩ := hL
    have : l w = (p : O) ^ 1 * q + φ (c.ev 1 s') := by rw [← hq]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (by simpa using hpm)) hev
  obtain ⟨hfin, hproj⟩ := GlobalTheory.PDiv.omega_finite_projective p K v O hv G.dual
  have h6 := repr_mem_maximalIdeal O G.dual.omega k lb l key j
  have hrep : lb.repr l j = b j := by
    have : l = lb.equivFun.symm b := by rw [Module.Basis.equivFun_symm_apply]
    rw [← Module.Basis.equivFun_apply, this, LinearEquiv.apply_symm_apply]
  rw [hrep] at h6
  exact (hmem _).1 h6

end GlobalTheory.TangentIndep
end
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_coords_nonunit_alt : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) E) (lb : Module.Basis (Fin k) O G.dual.Lie), (∀ i, QL c.μ ⊤ (e i)) → (∀ j, c.IsLie (e (Sum.inr j)) (lb j)) → (∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0) → ∀ (b : Fin k → O) (s : MvPowerSeries (Fin d) O), (∀ α, ∃ o : O, ¬IsUnit o ∧ coeff α (cob1 (up E c.μ) (comb (Sum.elim 0 b) e) - map (algebraMap O E) (cob1 c.μ s)) = algebraMap O E o) → ∀ j, ¬IsUnit (b j) := by
  atlas_forward_decl GlobalTheory.TangentIndep.tangent_coords_nonunit
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrobCongr

variable {Q : Type} [CommRing Q]

theorem frob_eq_expand {σ : Type} (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q) (f : MvPowerSeries σ Q) :
    frob p s f = expand p hp (map s f) := by
  rw [frob, expand, substAlgHom_apply]

theorem subst_frob {σ τ : Type} (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q) {a : σ → MvPowerSeries τ Q}
    (ha : HasSubst a) (g : MvPowerSeries σ Q) :
    subst a (frob p s g) = subst (fun i => a i ^ p) (map s g) := by
  rw [frob, subst_comp_subst_apply (HasSubst.X_pow hp) ha]
  congr 1
  funext i
  rw [subst_pow ha, subst_X ha]

theorem frob_subst {σ τ : Type} [Finite σ] (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q) {a : σ → MvPowerSeries τ Q}
    (ha : HasSubst a) (g : MvPowerSeries σ Q) :
    frob p s (subst a g) = subst (fun i => expand p hp (map s (a i))) (map s g) := by
  have ha' : HasSubst fun i => map s (a i) :=
    hasSubst_of_constantCoeff_nilpotent fun i => by
      rw [constantCoeff_map]; exact (ha.const_coeff i).map s
  rw [frob_eq_expand p hp, map_subst ha, expand_subst p hp ha']

end GlobalTheory.FrobCongr

namespace GlobalTheory.FrobCongr

theorem coeff_pow_sub_expand_mem {B τ : Type} [CommRing B] (p : ℕ) [hp : Fact p.Prime]
    (hnu : ¬IsUnit (p : B)) (σ : B →+* B) (hσ : ∀ b, (p : B) ∣ σ b - b ^ p)
    (g : MvPowerSeries τ B) (α : τ →₀ ℕ) :
    coeff α (g ^ p - expand p hp.out.ne_zero (map σ g)) ∈ Ideal.span {(p : B)} := by
  haveI : CharP (B ⧸ Ideal.span {(p : B)}) p := CharP.quotient B p hnu
  set π := Ideal.Quotient.mk (Ideal.span {(p : B)})
  have hπσ : π.comp σ = (frobenius (B ⧸ Ideal.span {(p : B)}) p).comp π := by
    ext b
    simp only [RingHom.comp_apply, frobenius_def]
    rw [← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.2 (hσ b)
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map]
  change coeff α (map π (g ^ p - expand p hp.out.ne_zero (map σ g))) = 0
  rw [map_sub, map_pow, map_expand, map_map, hπσ, ← map_map, ← map_expand,
    map_frobenius_expand, sub_self, map_zero]

end GlobalTheory.FrobCongr

namespace GlobalTheory.FrobCongr

theorem dIn_comb {B Q σ ι : Type} [CommRing B] [CommRing Q] [Algebra B Q] [Fintype ι]
    (b : ι → B) (e : ι → MvPowerSeries σ Q) (he : ∀ i, DIn (⊤ : Ideal B) (e i)) :
    DIn (⊤ : Ideal B) (comb b e) := by
  intro α j
  choose c _ hc using fun i => he i α j
  refine ⟨∑ i, b i * c i, trivial, ?_⟩
  simp only [comb, map_sum, coeff_smul, smul_eq_mul, Finset.mul_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hc i]; ring

theorem dIn_map {B Q σ : Type} [CommRing B] [CommRing Q] [Algebra B Q] (φ : B →+* B) (s : Q →+* Q)
    (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (φ b)) (f : MvPowerSeries σ Q)
    (hf : DIn (⊤ : Ideal B) f) : DIn (⊤ : Ideal B) (map s f) := by
  intro α j
  obtain ⟨c, -, hc⟩ := hf α j
  refine ⟨φ c, trivial, ?_⟩
  rw [coeff_map, ← hs, ← hc, map_mul, map_natCast]

theorem frob_cong : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (F : BFrame ε) (d : ℕ) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) F.Q), (∀ i, QL μ' ⊤ (e i)) → ∀ b : ι → F.B, In (Ideal.span {(p : F.B)}) (cob1 (up F.Q μ') (frob p F.s (comb b e)) - frob p F.s (cob1 (up F.Q μ') (comb b e))) := by
  intro p hp O _ hO _ ε F d μ' hμ ι _ e he b
  have hp0 : p ≠ 0 := hp.out.ne_zero
  set f := comb b e with hfdef
  set M := up F.Q μ' with hM
  have hM0 : ∀ i, constantCoeff (M i) = 0 := fun i => by
    rw [hM, up, constantCoeff_map, hμ.const i, map_zero]
  have hsM : HasSubst M := hasSubst_of_constantCoeff_zero hM0
  have hsL : HasSubst fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) F.Q) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hsR : HasSubst fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) F.Q) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

  have hX : ∀ (a : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.Q), (∀ i, ∃ j, a i = X j) → HasSubst a →
      subst a (frob p F.s f) = frob p F.s (subst a f) := by
    intro a ha has
    rw [subst_frob p hp0 F.s has, frob_subst p hp0 F.s has]
    congr 1
    funext i
    obtain ⟨j, hj⟩ := ha i
    rw [hj, map_X, expand_X]
  have hL := hX _ (fun i => ⟨_, rfl⟩) hsL
  have hR := hX _ (fun i => ⟨_, rfl⟩) hsR

  set u : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B := fun i => μ' i ^ p with hu
  set v : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B := fun i => expand p hp0 (map F.σ (μ' i)) with hv
  have hsalg : F.s.comp (algebraMap F.B F.Q) = (algebraMap F.B F.Q).comp F.σ :=
    RingHom.ext fun x => F.s_alg x
  have hup_u : up F.Q u = fun i => M i ^ p := by
    funext i; rw [up, hu, hM, up, map_pow]
  have hup_v : up F.Q v = fun i => expand p hp0 (map F.s (M i)) := by
    funext i; rw [up, hv, hM, up, map_expand, map_map, map_map, hsalg]
  have key : cob1 M (frob p F.s f) - frob p F.s (cob1 M f) =
      subst (up F.Q u) (map F.s f) - subst (up F.Q v) (map F.s f) := by
    rw [hup_u, hup_v, ← subst_frob p hp0 F.s hsM, ← frob_subst p hp0 F.s hsM]
    have hfs : ∀ a c : MvPowerSeries (Fin d ⊕ Fin d) F.Q,
        frob p F.s (a - c) = frob p F.s a - frob p F.s c := fun a c => by
      simp only [frob_eq_expand p hp0, map_sub]
    unfold cob1 inL inR
    rw [hfs, hfs, hL, hR]
    abel
  rw [key, ← Ideal.mul_top (Ideal.span {(p : F.B)})]
  have hnu : ¬IsUnit (p : F.B) := fun h => hO.out (by simpa using h.map F.θ)
  refine GlobalTheory.KatzCongr.subst_sub_in p F.B O F.Q F.θ F.frame _ ?_ (Fin d) (Fin d ⊕ Fin d) ⊤
    (map F.s f) u v ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    refine ⟨z ^ p * (p : F.B) ^ (p - 1),
      Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _
        (Nat.sub_pos_of_lt hp.out.one_lt)), ?_⟩
    rw [mul_pow, mul_left_comm, ← pow_succ', Nat.sub_add_cancel hp.out.one_le]
  · exact dIn_map F.σ F.s F.s_alg f
      (dIn_comb b e fun i => GlobalTheory.QLogDiff.dIn_of_QL p F.B O F.Q F.θ F.frame d μ' hμ ⊤ (e i) (he i))
  · intro i; rw [hu, map_pow, hμ.const i, zero_pow hp0]
  · intro i; rw [hv, constantCoeff_expand, constantCoeff_map, hμ.const i, map_zero]
  · intro i α
    exact coeff_pow_sub_expand_mem p hnu F.σ F.σ_pow (μ' i) α

end GlobalTheory.FrobCongr
end
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_frobenius_commute_mod_p_quasiLog : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (F : BFrame ε) (d : ℕ) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) F.Q), (∀ i, QL μ' ⊤ (e i)) → ∀ b : ι → F.B, In (Ideal.span {(p : F.B)}) (cob1 (up F.Q μ') (frob p F.s (comb b e)) - frob p F.s (cob1 (up F.Q μ') (comb b e))) := by
  atlas_forward_decl GlobalTheory.FrobCongr.frob_cong
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrobComb

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type}

theorem in_top_sum {ι : Type} [Fintype ι] (c : ι → B) (g : ι → MvPowerSeries σ Q)
    (hg : ∀ i, In (⊤ : Ideal B) (g i)) :
    In (⊤ : Ideal B) (∑ i, algebraMap B Q (c i) • g i) := by
  choose t ht using fun i => In.top_iff.1 (hg i)
  refine In.top_iff.2 ⟨∑ i, c i • t i, ?_⟩
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_C_mul, map_mul, map_C, ht i, smul_eq_C_mul]

theorem frob_sum (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q) {ι : Type} [Fintype ι] (c : ι → Q)
    (f : ι → MvPowerSeries σ Q) :
    frob p s (∑ i, c i • f i) = ∑ i, s (c i) • frob p s (f i) := by
  have hX : HasSubst (fun i : σ => (X i : MvPowerSeries σ Q) ^ p) := HasSubst.X_pow hp
  simp only [frob, ← coe_substAlgHom hX, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul, map_smul]

end GlobalTheory.FrobComb

open GlobalTheory.FrobComb

theorem GlobalTheory.frob_comb_zero_left : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (F : BFrame ε) (d k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B), (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → ∀ b : Fin k → F.B, In (⊤ : Ideal F.B) (frob p F.s (comb (Sum.elim (fun _ => 0) b) e) - comb (U.mulVec (fun j => F.σ ((Sum.elim (fun _ => 0) b : Fin d ⊕ Fin k → F.B) j))) e) := by
  intro p _ O _ _ _ ε F d k e U he b
  set b' : Fin d ⊕ Fin k → F.B := Sum.elim (fun _ => 0) b with hb'
  set c : Fin d ⊕ Fin k → F.B := fun j => F.σ (b' j) with hc
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have key : ∀ l i, (U * blk d k (p : F.B) 1) l i * c i = U l i * c i := by
    intro l i
    rcases i with i | i
    · simp [hc, hb']
    · simp [blk, Matrix.mul_diagonal]
  have hf : frob p F.s (comb b' e) = ∑ i, algebraMap F.B F.Q (c i) • frob p F.s (e i) := by
    rw [comb, frob_sum p hp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [F.s_alg]
  have hsplit : frob p F.s (comb b' e) - comb (U.mulVec c) e =
      ∑ i, algebraMap F.B F.Q (c i) •
        (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) := by
    rw [hf]
    simp only [smul_sub, Finset.sum_sub_distrib]
    congr 1
    simp only [comb, Matrix.mulVec, dotProduct, Finset.smul_sum, smul_smul, ← map_mul,
      map_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (c _), key]
  rw [hsplit]
  exact in_top_sum c _ he
end
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_linearCombination_zero_left_ainfFrame : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (F : BFrame ε) (d k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B), (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → ∀ b : Fin k → F.B, In (⊤ : Ideal F.B) (frob p F.s (comb (Sum.elim (fun _ => 0) b) e) - comb (U.mulVec (fun j => F.σ ((Sum.elim (fun _ => 0) b : Fin d ⊕ Fin k → F.B) j))) e) := by
  atlas_forward_decl GlobalTheory.frob_comb_zero_left
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

namespace GlobalTheory.SmallSecond.ToO

theorem frob_eq_expand {Q τ : Type} [CommRing Q] (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q)
    (f : MvPowerSeries τ Q) : frob p s f = expand p hp (map s f) := by
  rw [frob, expand, substAlgHom_apply]

theorem coeff_frob_smul {Q τ : Type} [CommRing Q] (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q)
    (f : MvPowerSeries τ Q) (β : τ →₀ ℕ) : coeff (p • β) (frob p s f) = s (coeff β f) := by
  rw [frob_eq_expand p hp, coeff_expand_smul, coeff_map]

theorem coeff_frob_of_not_dvd {Q τ : Type} [CommRing Q] (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q)
    (f : MvPowerSeries τ Q) {α : τ →₀ ℕ} {i : τ} (h : ¬ p ∣ α i) : coeff α (frob p s f) = 0 := by
  rw [frob_eq_expand p hp]
  exact coeff_expand_of_not_dvd p hp _ h

theorem formalGroupLawCoboundaryOne_sub {Q : Type} [CommRing Q] {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) Q}
    (h : ∀ i, constantCoeff (μ i) = 0) (f g : MvPowerSeries (Fin d) Q) :
    cob1 μ (f - g) = cob1 μ f - cob1 μ g := by
  have := formalCoboundary_add h (f - g) g
  rw [sub_add_cancel] at this
  rw [this, add_sub_cancel_right]

theorem formalGroupLawCoboundaryOne_finset_sum {Q : Type} [CommRing Q] {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) Q}
    (h : ∀ i, constantCoeff (μ i) = 0) {ι : Type} (S : Finset ι) (f : ι → MvPowerSeries (Fin d) Q) :
    cob1 μ (∑ i ∈ S, f i) = ∑ i ∈ S, cob1 μ (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have := formalCoboundary_smul h 0 0
    simpa using this
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, formalCoboundary_add h, ih]

end GlobalTheory.SmallSecond.ToO

open GlobalTheory.SmallSecond.ToO in

theorem GlobalTheory.SmallSecond.frob_congr_to_O : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (F : BFrame ε) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), (∀ i, QL μ' ⊤ (e i)) → ∀ (W : Fin d ⊕ Fin k → F.B) (b : Fin k → F.B), (∀ l, ¬IsUnit (F.θ (W l))) → In (⊤ : Ideal F.B) (frob p F.s (comb (Sum.elim (fun _ => 0) b) e) - comb W e) → In (Ideal.span {(p : F.B)}) (cob1 (up F.Q μ') (frob p F.s (comb (Sum.elim (fun _ => 0) b) e)) - frob p F.s (cob1 (up F.Q μ') (comb (Sum.elim (fun _ => 0) b) e))) → ∃ (F₁ : MvPowerSeries (Fin d ⊕ Fin d) F.B) (t : MvPowerSeries (Fin d) O), map (algebraMap F.B F.Q) F₁ = cob1 (up F.Q μ') (comb (Sum.elim (fun _ => 0) b) e) ∧ (∀ i, ¬IsUnit (lin t i)) ∧ (∀ β : Fin d ⊕ Fin d →₀ ℕ, ¬IsUnit (coeff (p • β) (cob1 μ t) - F.θ (coeff β F₁) ^ p)) ∧ ∀ α : Fin d ⊕ Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α (cob1 μ t)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε F d μ μ' hlift hmap k e he W b hW hT hC
  classical
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : IsLocalRing O := ValuationRing.isLocalRing O
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set m := IsLocalRing.maximalIdeal O with hm
  have memm : ∀ x : O, x ∈ m ↔ ¬IsUnit x := fun x => by
    rw [hm, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hpm : (p : O) ∈ m := (memm _).2 Fact.out
  have hθp : ∀ x : F.B, F.θ ((p : F.B) * x) ∈ m := fun x => by
    rw [map_mul, map_natCast]; exact m.mul_mem_right _ hpm
  have hWm : ∀ l, F.θ (W l) ∈ m := fun l => (memm _).2 (hW l)
  have hμQ : ∀ i, constantCoeff (up F.Q μ' i) = 0 := fun i => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hlift.const, map_zero]
  have hcomb : ∀ c : Fin d ⊕ Fin k → F.B, cob1 (up F.Q μ') (comb c e) =
      ∑ l, algebraMap F.B F.Q (c l) • cob1 (up F.Q μ') (e l) := by
    intro c
    unfold comb
    rw [formalGroupLawCoboundaryOne_finset_sum hμQ]
    exact Finset.sum_congr rfl fun l _ => formalCoboundary_smul hμQ _ _
  choose g _ hg using fun l => (he l).2.2
  choose c1 _ hc1 using fun l => (he l).2.1
  have hSm : ∀ α, F.θ (∑ l, W l * g l α) ∈ m := fun α => by
    rw [map_sum]
    exact m.sum_mem fun l _ => by rw [map_mul]; exact m.mul_mem_right _ (hWm l)
  have hF : In (⊤ : Ideal F.B) (cob1 (up F.Q μ') (comb (Sum.elim (fun _ => (0 : F.B)) b) e)) := by
    intro α
    refine ⟨∑ l, Sum.elim (fun _ => (0 : F.B)) b l * g l α, trivial, ?_⟩
    rw [hcomb, map_sum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [MvPowerSeries.coeff_smul, hg, map_mul]
  obtain ⟨F₁, hF₁⟩ := In.top_iff.1 hF
  obtain ⟨T, hTT⟩ := In.top_iff.1 hT
  have hcobT : ∀ α, coeff α (cob1 μ (map F.θ T)) = F.θ (coeff α (cob1 μ' T)) := by
    intro α
    have hμeq : μ = fun i => map F.θ (μ' i) := funext fun i => (hmap i).symm
    rw [hμeq, ← map_formalGroupLawCoboundaryOne_eq F.θ μ' hlift.const T, coeff_map]
  have hup : map (algebraMap F.B F.Q) (cob1 μ' T) =
      cob1 (up F.Q μ') (frob p F.s (comb (Sum.elim (fun _ => (0 : F.B)) b) e)) -
        ∑ l, algebraMap F.B F.Q (W l) • cob1 (up F.Q μ') (e l) := by
    rw [map_formalGroupLawCoboundaryOne_eq (algebraMap F.B F.Q) μ' hlift.const T]
    change cob1 (up F.Q μ') (map (algebraMap F.B F.Q) T) = _
    rw [hTT, formalGroupLawCoboundaryOne_sub hμQ, hcomb]
  choose r hr hrC using hC
  have hgen : ∀ α, algebraMap F.B F.Q (coeff α (cob1 μ' T)) =
      coeff α (frob p F.s (map (algebraMap F.B F.Q) F₁)) + algebraMap F.B F.Q (r α) -
        algebraMap F.B F.Q (∑ l, W l * g l α) := by
    intro α
    have h1 := congrArg (coeff α) hup
    rw [coeff_map] at h1
    rw [h1, ← hrC α, map_sub, map_sub, hF₁, map_sum, map_sum]
    have h2 : ∑ l, coeff α (algebraMap F.B F.Q (W l) • cob1 (up F.Q μ') (e l)) =
        ∑ l, algebraMap F.B F.Q (W l * g l α) :=
      Finset.sum_congr rfl fun l _ => by rw [MvPowerSeries.coeff_smul, hg, map_mul]
    rw [h2]; ring
  refine ⟨F₁, map F.θ T, hF₁, fun i => (memm _).1 ?_, fun β => (memm _).1 ?_,
    fun α ⟨i, hi⟩ => (memm _).1 ?_⟩
  · have key : coeff (Finsupp.single i 1) T = -∑ l, W l * c1 l i := by
      apply F.frame.inj
      have h1 := congrArg (coeff (Finsupp.single i 1)) hTT
      rw [coeff_map] at h1
      have hnd : ¬ p ∣ (Finsupp.single i 1 : Fin d →₀ ℕ) i := by
        rw [Finsupp.single_eq_same]; exact (Fact.out : p.Prime).not_dvd_one
      rw [h1, map_sub, coeff_frob_of_not_dvd p hp0 _ _ hnd, zero_sub, map_neg, map_sum]
      unfold comb
      rw [map_sum]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      have := hc1 l i
      simp only [lin] at this
      rw [MvPowerSeries.coeff_smul, this, map_mul]
    unfold lin
    rw [coeff_map, key, map_neg, map_sum]
    exact m.neg_mem (m.sum_mem fun l _ => by rw [map_mul]; exact m.mul_mem_right _ (hWm l))
  · have h1 := hgen (p • β)
    rw [coeff_frob_smul p hp0, coeff_map, F.s_alg, ← map_add, ← map_sub] at h1
    rw [hcobT, F.frame.inj h1]
    obtain ⟨y, hy⟩ := F.σ_pow (coeff β F₁)
    obtain ⟨r', hr'⟩ := Ideal.mem_span_singleton.1 (hr (p • β))
    have e1 : F.θ (F.σ (coeff β F₁) + r (p • β) - ∑ l, W l * g l (p • β)) - F.θ (coeff β F₁) ^ p =
        F.θ (F.σ (coeff β F₁) - coeff β F₁ ^ p) + F.θ (r (p • β)) -
          F.θ (∑ l, W l * g l (p • β)) := by
      simp only [map_sub, map_add, map_pow]; ring
    rw [e1, hy, hr']
    exact m.sub_mem (m.add_mem (hθp y) (hθp r')) (hSm _)
  · have h1 := hgen α
    rw [coeff_frob_of_not_dvd p hp0 _ _ hi, zero_add, ← map_sub] at h1
    rw [hcobT, F.frame.inj h1, map_sub]
    obtain ⟨r', hr'⟩ := Ideal.mem_span_singleton.1 (hr α)
    rw [hr']
    exact m.sub_mem (hθp r') (hSm _)
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_congruence_combination_over_integers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (F : BFrame ε) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), (∀ i, QL μ' ⊤ (e i)) → ∀ (W : Fin d ⊕ Fin k → F.B) (b : Fin k → F.B), (∀ l, ¬IsUnit (F.θ (W l))) → In (⊤ : Ideal F.B) (frob p F.s (comb (Sum.elim (fun _ => 0) b) e) - comb W e) → In (Ideal.span {(p : F.B)}) (cob1 (up F.Q μ') (frob p F.s (comb (Sum.elim (fun _ => 0) b) e)) - frob p F.s (cob1 (up F.Q μ') (comb (Sum.elim (fun _ => 0) b) e))) → ∃ (F₁ : MvPowerSeries (Fin d ⊕ Fin d) F.B) (t : MvPowerSeries (Fin d) O), map (algebraMap F.B F.Q) F₁ = cob1 (up F.Q μ') (comb (Sum.elim (fun _ => 0) b) e) ∧ (∀ i, ¬IsUnit (lin t i)) ∧ (∀ β : Fin d ⊕ Fin d →₀ ℕ, ¬IsUnit (coeff (p • β) (cob1 μ t) - F.θ (coeff β F₁) ^ p)) ∧ ∀ α : Fin d ⊕ Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α (cob1 μ t)) := by
  atlas_forward_decl GlobalTheory.SmallSecond.frob_congr_to_O
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.SmallDeriv

variable {O : Type} [CommRing O] {d : ℕ}

def yZero : Fin d ⊕ Fin d → MvPowerSeries (Fin d) O := Sum.elim (fun i => X i) (fun _ => 0)

theorem yZero_const : ∀ s, constantCoeff (yZero (O := O) (d := d) s) = 0 := by
  intro s; cases s <;> simp [yZero]

theorem hasSubst_yZero : HasSubst (yZero (O := O) (d := d)) :=
  hasSubst_of_constantCoeff_zero yZero_const

theorem constantCoeff_subst_of {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ O}
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ O) :
    constantCoeff (subst a f) = constantCoeff f := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have h1 : f = (f - C (constantCoeff f)) + C (constantCoeff f) := by ring
  conv_lhs => rw [h1]
  rw [subst_add hs, map_add, constantCoeff_subst_eq_zero hs ha (by simp), subst_C, zero_add]
  simp

theorem constantCoeff_pderiv {σ : Type} (i : σ) (f : MvPowerSeries σ O) :
    constantCoeff (pderiv O i f) = coeff (Finsupp.single i 1) f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]; simp

theorem subst_X_self {σ : Type} (f : MvPowerSeries σ O) : subst (fun i => (X i : MvPowerSeries σ O)) f = f := by
  rw [← map_algebraMap_eq_subst_X]
  simp [Algebra.algebraMap_self, map_id]

theorem pderiv_right_formalGroupLawCoboundaryOne (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (t : MvPowerSeries (Fin d) O) (j : Fin d) :
    pderiv O (Sum.inr j) (cob1 μ t) =
      (∑ s, subst μ (pderiv O s t) * pderiv O (Sum.inr j) (μ s)) - inR (pderiv O j t) := by
  classical
  have hl : ∀ s : Fin d, constantCoeff (X (Sum.inl s) : MvPowerSeries (Fin d ⊕ Fin d) O) = 0 :=
    fun s => constantCoeff_X _
  have hr : ∀ s : Fin d, constantCoeff (X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) O) = 0 :=
    fun s => constantCoeff_X _
  unfold cob1 inL inR
  rw [map_sub, map_sub, ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst μ hμ,
    ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst _ hl, ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst _ hr]
  have e1 : ∑ s : Fin d, subst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) O)) (pderiv O s t) *
      pderiv O (Sum.inr j) (X (Sum.inl s)) = 0 :=
    Finset.sum_eq_zero fun s _ => by rw [pderiv_X_of_ne (by simp), mul_zero]
  have e2 : ∑ s : Fin d, subst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O)) (pderiv O s t) *
      pderiv O (Sum.inr j) (X (Sum.inr s)) =
      subst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O)) (pderiv O j t) := by
    rw [Finset.sum_eq_single j]
    · rw [pderiv_X_self, mul_one]
    · intro s _ hs; rw [pderiv_X_of_ne (by simpa using hs), mul_zero]
    · simp
  rw [e1, e2, sub_zero]

end GlobalTheory.Katz.SmallDeriv

namespace GlobalTheory.Katz.SmallDeriv

variable {O : Type} [CommRing O] {d : ℕ}

theorem yZero_subst (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : IsLaw μ) (g : MvPowerSeries (Fin d) O) :
    subst yZero (subst μ g) = g := by
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hμ.const) hasSubst_yZero]
  have : (fun s => subst (yZero (O := O) (d := d)) (μ s)) = fun i => X i := by
    have h := hμ.unit
    funext i
    have hi := congrFun h i
    simpa [op, at2, yZero] using hi
  rw [this, subst_X_self]

theorem yZero_inR (g : MvPowerSeries (Fin d) O) :
    subst yZero (inR g) = C (constantCoeff g) := by
  have hr : HasSubst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O)) :=
    hasSubst_of_constantCoeff_zero fun s => constantCoeff_X _
  unfold inR
  rw [subst_comp_subst_apply hr hasSubst_yZero]
  have : (fun s => subst (yZero (O := O) (d := d)) (X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) O)) = 0 := by
    funext s; rw [subst_X hasSubst_yZero]; rfl
  rw [this, subst_zero_eq_C_constantCoeff]
  simp [Algebra.algebraMap_self, map_id]

theorem linear_coeff_law (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : IsLaw μ) (s j : Fin d) :
    constantCoeff (pderiv O (Sum.inr j) (μ s)) = if s = j then 1 else 0 := by
  classical

  have hx : constantCoeff (pderiv O (Sum.inl j) (μ s)) = if s = j then 1 else 0 := by
    have h := congrFun hμ.unit s
    change subst yZero (μ s) = X s at h
    have h2 := congrArg (fun f => constantCoeff (pderiv O j f)) h
    rw [ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst _ yZero_const, map_sum] at h2
    simp only [map_mul, constantCoeff_subst_of yZero_const] at h2
    simp only [Fintype.sum_sum_type, yZero,
      Sum.elim_inl, Sum.elim_inr, map_zero, mul_zero, Finset.sum_const_zero, add_zero, pderiv_X, map_sum, map_mul] at h2
    simp only [Pi.single_apply, apply_ite, map_one, map_zero, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
    split_ifs at h2 ⊢ <;> exact h2
  have hsw : ∀ k : Fin d ⊕ Fin d, constantCoeff ((Sum.elim (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O))
      (fun i => X (Sum.inl i))) k) = 0 := by
    intro k; cases k <;> simp
  have h := hμ.comm s
  unfold swap at2 at h
  have h2 := congrArg (fun f => constantCoeff (pderiv O (Sum.inr j) f)) h
  rw [ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst _ hsw, map_sum] at h2
  simp only [map_mul, constantCoeff_subst_of hsw] at h2
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, pderiv_X, Pi.single_apply, Sum.inr.injEq,
    reduceCtorEq, if_false, map_zero, mul_zero, Finset.sum_const_zero, add_zero, apply_ite, map_one, mul_ite,
    mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  rw [← h2, hx]

end GlobalTheory.Katz.SmallDeriv

namespace GlobalTheory.Katz.SmallDeriv

theorem isLocalRing_of_integers {C : Type} [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O]
    [Algebra O C] (hv : v.Integers O) : IsLocalRing O := by
  haveI : Nontrivial O := (algebraMap O C).domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_contra h
  push_neg at h
  have h1 : v (algebraMap O C a) < 1 :=
    lt_of_le_of_ne (hv.map_le_one a) (fun e => h.1 (hv.isUnit_of_one' e))
  have h2 : v (algebraMap O C (1 - a)) < 1 :=
    lt_of_le_of_ne (hv.map_le_one _) (fun e => h.2 (hv.isUnit_of_one' e))
  have h3 := v.map_add (algebraMap O C a) (algebraMap O C (1 - a))
  have h4 : algebraMap O C a + algebraMap O C (1 - a) = 1 := by rw [← map_add]; simp
  rw [h4, v.map_one] at h3
  exact lt_irrefl _ (lt_of_le_of_lt h3 (max_lt h1 h2))

end GlobalTheory.Katz.SmallDeriv

open GlobalTheory.Katz.SmallDeriv in

theorem GlobalTheory.Katz.not_isUnit_coeff_of_coboundary_small : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ t : MvPowerSeries (Fin d) O, (∀ i, ¬IsUnit (lin t i)) → (∀ α : Fin d ⊕ Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α (cob1 μ t))) → ∀ α : Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α t) := by
  intro p hpr C _ _ _ v O _ _ hpO _ _ hv d μ hμ t hlin hcob α ⟨i, hi⟩
  classical
  haveI : IsLocalRing O := isLocalRing_of_integers v O hv
  let π := IsLocalRing.residue O
  have hmem : ∀ a : O, π a = 0 ↔ ¬IsUnit a := by
    intro a
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hp0 : (p : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast π, hmem]; exact hpO.out

  have hG : ∀ j, map π (pderiv O (Sum.inr j) (cob1 μ t)) = 0 := by
    intro j; ext n
    rw [coeff_map, coeff_pderiv, map_mul, coeff_zero]
    by_cases hn : p ∣ n (Sum.inr j) + 1
    · obtain ⟨m, hm⟩ := hn
      have e : π ((n (Sum.inr j) : O) + 1) = 0 := by
        have : ((n (Sum.inr j) : O) + 1) = ((n (Sum.inr j) + 1 : ℕ) : O) := by push_cast; ring
        rw [this, hm, Nat.cast_mul, map_mul, map_natCast, hp0, zero_mul]
      rw [e, mul_zero]
    · have := hcob (n + Finsupp.single (Sum.inr j) 1) ⟨Sum.inr j, by simpa using hn⟩
      rw [(hmem _).2 this, zero_mul]
  let N : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) (IsLocalRing.ResidueField O)) :=
    Matrix.of fun s j => map π (subst yZero (pderiv O (Sum.inr j) (μ s)))
  let w : Fin d → MvPowerSeries (Fin d) (IsLocalRing.ResidueField O) := fun s => map π (pderiv O s t)
  have hvec : Matrix.vecMul w N = 0 := by
    funext j
    have e := congrArg (fun F => map π (subst yZero F)) (pderiv_right_formalGroupLawCoboundaryOne μ hμ.const t j)
    rw [map_subst hasSubst_yZero, hG j, ← coe_substAlgHom (hasSubst_yZero.map π), map_zero,
      ← coe_substAlgHom hasSubst_yZero, map_sub, map_sum] at e
    simp only [map_mul, coe_substAlgHom, yZero_subst μ hμ, yZero_inR, constantCoeff_pderiv, map_sub, map_sum,
      map_C] at e
    have hl : π (coeff (Finsupp.single j 1) t) = 0 := (hmem _).2 (hlin j)
    rw [hl, map_zero, sub_zero] at e
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, N, w, Matrix.of_apply]
    exact e.symm
  have hN0 : (constantCoeff : MvPowerSeries (Fin d) (IsLocalRing.ResidueField O) →+* _).mapMatrix N = 1 := by
    ext s j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, N, Matrix.of_apply, constantCoeff_map,
      constantCoeff_subst_of yZero_const, linear_coeff_law μ hμ, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : IsUnit N.det := by
    rw [isUnit_iff_constantCoeff, RingHom.map_det, hN0, Matrix.det_one]
    exact isUnit_one
  have hw : w i = 0 := by
    have h1 := congrArg (fun u => Matrix.vecMul u N.adjugate) hvec
    simp only [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.zero_vecMul] at h1
    have h2 := congrFun h1 i
    simp only [Matrix.vecMul, dotProduct, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.zero_apply] at h2
    exact (hdet.mul_right_eq_zero).1 (by rw [mul_comm]; exact h2)
  have hαi : 1 ≤ α i := Nat.pos_of_ne_zero (fun h => hi (h ▸ dvd_zero p))
  have hsub : α - Finsupp.single i 1 + Finsupp.single i 1 = α :=
    tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hαi)
  have hc := congrArg (coeff (α - Finsupp.single i 1)) hw
  simp only [w] at hc
  rw [coeff_map, coeff_pderiv, coeff_zero, hsub, map_mul] at hc
  have hcast : (((α - Finsupp.single i 1 : Fin d →₀ ℕ) i : ℕ) : O) + 1 = ((α i : ℕ) : O) := by
    rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
    rw [← Nat.cast_add_one, Nat.sub_add_cancel hαi]
  rw [hcast, map_natCast] at hc
  have hne : ((α i : ℕ) : IsLocalRing.ResidueField O) ≠ 0 := by
    obtain ⟨u, u', h⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hpr.out).2 hi)
    have h' := congrArg (Int.cast : ℤ → IsLocalRing.ResidueField O) h
    push_cast at h'
    rw [hp0] at h'
    intro h0; rw [h0] at h'; simp at h'
  exact (hmem _).1 ((mul_eq_zero.1 hc).resolve_right hne)
end
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_isUnit_coeff_of_coboundary_small' : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ t : MvPowerSeries (Fin d) O, (∀ i, ¬IsUnit (lin t i)) → (∀ α : Fin d ⊕ Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α (cob1 μ t))) → ∀ α : Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α t) := by
  atlas_forward_decl GlobalTheory.Katz.not_isUnit_coeff_of_coboundary_small
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SmallSecondRoot

theorem charP_mvPowerSeries (σ k : Type) [Field k] (p : ℕ) [CharP k p] :
    CharP (MvPowerSeries σ k) p :=
  charP_of_injective_algebraMap (algebraMap k (MvPowerSeries σ k)).injective p

theorem coeff_pow_char_sum {σ k : Type} [DecidableEq σ] [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : MvPowerSeries σ k) (α : σ →₀ ℕ) :
    coeff α (f ^ p) = ∑ m ∈ Finset.Iic α, if α = p • m then coeff m f ^ p else 0 := by
  classical
  haveI := charP_mvPowerSeries σ k p
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set P : MvPowerSeries σ k := ∑ m ∈ Finset.Iic α, monomial m (coeff m f)
  set g := f - P
  have hg : ∀ m ≤ α, coeff m g = 0 := by
    intro m hm
    simp only [g, P, map_sub, map_sum, coeff_monomial]
    rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_Iic.2 hm) h
  have hmul : ∀ h : MvPowerSeries σ k, coeff α (h * g) = 0 := by
    intro h
    rw [coeff_mul]
    refine Finset.sum_eq_zero fun q hq => ?_
    have hq' := Finset.HasAntidiagonal.mem_antidiagonal.1 hq
    rw [hg q.2 (hq' ▸ le_add_self), mul_zero]
  have hf : f = P + g := by simp [g]
  have hgp : coeff α (g ^ p) = 0 := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hp0
    rw [hn, pow_succ]; exact hmul _
  rw [show f ^ p = (P + g) ^ p from congrArg (· ^ p) hf, add_pow_char, map_add, hgp, add_zero]
  simp only [P]
  rw [sum_pow_char, map_sum]
  simp only [monomial_pow, coeff_monomial]

theorem coeff_smul_pow_char {σ k : Type} [DecidableEq σ] [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : MvPowerSeries σ k) (β : σ →₀ ℕ) : coeff (p • β) (f ^ p) = coeff β f ^ p := by
  classical
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [coeff_pow_char_sum, Finset.sum_eq_single β]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg]
    intro hα
    exact hb (smul_right_injective _ hp0 hα).symm
  · intro hn
    exact absurd (Finset.mem_Iic.2 (le_smul_of_one_le_left zero_le (Nat.one_le_iff_ne_zero.2 hp0))) hn

theorem coeff_pow_char_of_not {σ k : Type} [DecidableEq σ] [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : MvPowerSeries σ k) (α : σ →₀ ℕ) (h : ¬∃ β, p • β = α) : coeff α (f ^ p) = 0 := by
  classical
  rw [coeff_pow_char_sum]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [if_neg]
  intro hα; exact h ⟨b, hα.symm⟩

end GlobalTheory.SmallSecondRoot

namespace GlobalTheory.SmallSecondRoot

theorem exists_integral_cob1_congr_of_frobenius_congr : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (c : MvPowerSeries (Fin d ⊕ Fin d) O) (t : MvPowerSeries (Fin d) O), (∀ α : Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α t)) → (∀ β : Fin d ⊕ Fin d →₀ ℕ, ¬IsUnit (coeff (p • β) (cob1 μ t) - coeff β c ^ p)) → ∃ u : MvPowerSeries (Fin d) O, ∀ α, ¬IsUnit (coeff α c - coeff α (cob1 μ u)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv d μ hμ c t ht hct
  classical
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hroot : ∀ a : O, ∃ r : O, r ^ p = a := by
    intro a
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O C a) (Nat.pos_of_ne_zero hp0)
    have h1 : v z ≤ 1 := by
      have : v z ^ p ≤ 1 := by rw [← map_pow, hz]; exact hv.map_le_one a
      exact (pow_le_one_iff_of_nonneg zero_le hp0).1 this
    obtain ⟨r, hr⟩ := hv.exists_of_le_one h1
    exact ⟨r, hv.hom_inj (by rw [map_pow, hr, hz])⟩
  choose rt hrt using hroot
  let u : MvPowerSeries (Fin d) O := fun β => rt (coeff (p • β) t)
  have hu : ∀ β, coeff β u = rt (coeff (p • β) t) := fun β => rfl
  refine ⟨u, fun α => ?_⟩
  let res := IsLocalRing.residue O
  have hres : ∀ x : O, ¬ IsUnit x ↔ res x = 0 := fun x => by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  haveI : CharP (IsLocalRing.ResidueField O) p :=
    (CharP.charP_iff_prime_eq_zero Fact.out).2 (by rw [← map_natCast res, ← hres]; exact Fact.out)
  have hμb : ∀ i, constantCoeff (map res (μ i)) = 0 := fun i => by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hμ.const i, map_zero]
  have ht' : map res t = (map res u) ^ p := by
    ext γ
    rw [coeff_map]
    by_cases h : ∃ β, p • β = γ
    · obtain ⟨β, rfl⟩ := h
      rw [coeff_smul_pow_char, coeff_map, hu, ← map_pow, hrt]
    · rw [coeff_pow_char_of_not _ _ _ h, ← hres]
      apply ht
      by_contra hall
      push_neg at hall
      refine h ⟨Finsupp.mapRange (· / p) (Nat.zero_div p) γ, ?_⟩
      ext i
      simp [Nat.mul_div_cancel' (hall i)]
  have hcob : map res (cob1 μ t) = (cob1 (fun i => map res (μ i)) (map res u)) ^ p := by
    haveI := charP_mvPowerSeries (Fin d ⊕ Fin d) (IsLocalRing.ResidueField O) p
    rw [SmallSecond.map_formalGroupLawCoboundaryOne_eq res μ hμ.const, ht']
    unfold cob1 inL inR
    rw [subst_pow (hasSubst_of_constantCoeff_zero hμb),
      subst_pow (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
      subst_pow (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _), sub_pow_char,
      sub_pow_char]
  have h1 := (hres _).1 (hct α)
  rw [map_sub, sub_eq_zero, ← coeff_map, hcob, coeff_smul_pow_char, map_pow] at h1
  have h3 : coeff α (cob1 (fun i => map res (μ i)) (map res u)) = res (coeff α c) :=
    frobenius_inj _ p h1
  rw [hres, map_sub, sub_eq_zero, ← h3, ← SmallSecond.map_formalGroupLawCoboundaryOne_eq res μ hμ.const, coeff_map]

end GlobalTheory.SmallSecondRoot
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_coboundaryOne_congr_frobenius : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (c : MvPowerSeries (Fin d ⊕ Fin d) O) (t : MvPowerSeries (Fin d) O), (∀ α : Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α t)) → (∀ β : Fin d ⊕ Fin d →₀ ℕ, ¬IsUnit (coeff (p • β) (cob1 μ t) - coeff β c ^ p)) → ∃ u : MvPowerSeries (Fin d) O, ∀ α, ¬IsUnit (coeff α c - coeff α (cob1 μ u)) := by
  atlas_forward_decl GlobalTheory.SmallSecondRoot.exists_integral_cob1_congr_of_frobenius_congr
end

section
section
namespace GlobalTheory

open Matrix

theorem exists_basis_of_blockLowerTriangular_inv (O M : Type) [CommRing O] [AddCommGroup M] [Module O M]
    (d k k' : ℕ) (lbs : Module.Basis (Fin k') O M)
    (P : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k') O) (P' : Matrix (Fin d ⊕ Fin k') (Fin d ⊕ Fin k) O)
    (h1 : P * P' = 1) (h2 : P' * P = 1) (hz : ∀ i j, P (Sum.inl i) (Sum.inr j) = 0) :
    ∃ lb : Module.Basis (Fin k) O M, ∀ j, lb j = ∑ j', P (Sum.inr j) (Sum.inr j') • lbs j' := by
  have hAA : P.toBlocks₁₁ * P'.toBlocks₁₁ = 1 := by
    ext i i'
    have := congrFun (congrFun h1 (Sum.inl i)) (Sum.inl i')
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, hz, Matrix.one_apply, Matrix.toBlocks₁₁] using this
  have hA'A : P'.toBlocks₁₁ * P.toBlocks₁₁ = 1 := mul_eq_one_comm.mp hAA
  have hAB : P.toBlocks₁₁ * P'.toBlocks₁₂ = 0 := by
    ext i j
    have := congrFun (congrFun h1 (Sum.inl i)) (Sum.inr j)
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, hz, Matrix.one_apply, Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂] using this
  have hB : P'.toBlocks₁₂ = 0 := by
    calc P'.toBlocks₁₂ = (P'.toBlocks₁₁ * P.toBlocks₁₁) * P'.toBlocks₁₂ := by rw [hA'A, Matrix.one_mul]
      _ = P'.toBlocks₁₁ * (P.toBlocks₁₁ * P'.toBlocks₁₂) := Matrix.mul_assoc _ _ _
      _ = 0 := by rw [hAB, Matrix.mul_zero]
  have hb : ∀ a j, P' (Sum.inl a) (Sum.inr j) = 0 := fun a j => by
    simpa [Matrix.toBlocks₁₂] using congrFun (congrFun hB a) j
  have hDD : P.toBlocks₂₂ * P'.toBlocks₂₂ = 1 := by
    ext j j2
    have := congrFun (congrFun h1 (Sum.inr j)) (Sum.inr j2)
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, hb, Matrix.one_apply, Matrix.toBlocks₂₂] using this
  have hD'D : P'.toBlocks₂₂ * P.toBlocks₂₂ = 1 := by
    ext j j2
    have := congrFun (congrFun h2 (Sum.inr j)) (Sum.inr j2)
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, hz, Matrix.one_apply, Matrix.toBlocks₂₂] using this
  set D := P.toBlocks₂₂ with hDdef
  set D' := P'.toBlocks₂₂
  let L : (Fin k → O) ≃ₗ[O] (Fin k' → O) :=
    LinearEquiv.ofLinear (Matrix.toLin' Dᵀ) (Matrix.toLin' D'ᵀ)
      (by rw [← Matrix.toLin'_mul, ← Matrix.transpose_mul, hD'D, Matrix.transpose_one, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, ← Matrix.transpose_mul, hDD, Matrix.transpose_one, Matrix.toLin'_one])
  refine ⟨Module.Basis.ofEquivFun (lbs.equivFun.trans L.symm), fun j => ?_⟩
  rw [Module.Basis.coe_ofEquivFun]
  simp only [LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm, Module.Basis.equivFun_symm_apply]
  refine Finset.sum_congr rfl fun j' _ => ?_
  congr 1
  simp [L, Matrix.mulVec, dotProduct, Pi.single_apply, hDdef, Matrix.toBlocks₂₂]

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_of_blockLowerTriangular_inv' : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (d k k' : ℕ) (lbs : Module.Basis (Fin k') O M) (P : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k') O) (P' : Matrix (Fin d ⊕ Fin k') (Fin d ⊕ Fin k) O), P * P' = 1 → P' * P = 1 → (∀ i j, P (Sum.inl i) (Sum.inr j) = 0) → ∃ lb : Module.Basis (Fin k) O M, ∀ j, lb j = ∑ j', P (Sum.inr j) (Sum.inr j') • lbs j' := by
  atlas_forward_decl GlobalTheory.exists_basis_of_blockLowerTriangular_inv
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

namespace GlobalTheory.BasisTrans

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type}

theorem in_zero : In (⊤ : Ideal B) (0 : MvPowerSeries σ Q) :=
  fun _ => ⟨0, trivial, by simp⟩

theorem in_add {g h : MvPowerSeries σ Q} (hg : In (⊤ : Ideal B) g) (hh : In (⊤ : Ideal B) h) :
    In (⊤ : Ideal B) (g + h) := fun α => by
  obtain ⟨a, -, ha⟩ := hg α
  obtain ⟨b, -, hb⟩ := hh α
  exact ⟨a + b, trivial, by rw [map_add, ha, hb, map_add]⟩

theorem in_smul (c : B) {g : MvPowerSeries σ Q} (hg : In (⊤ : Ideal B) g) :
    In (⊤ : Ideal B) (algebraMap B Q c • g) := fun α => by
  obtain ⟨a, -, ha⟩ := hg α
  exact ⟨c * a, trivial, by rw [coeff_smul, ha, map_mul]⟩

theorem in_sum {κ : Type} (s : Finset κ) (g : κ → MvPowerSeries σ Q)
    (hg : ∀ j ∈ s, In (⊤ : Ideal B) (g j)) : In (⊤ : Ideal B) (∑ j ∈ s, g j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using in_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact in_add (hg a (Finset.mem_insert_self _ _)) (ih fun j hj => hg j (Finset.mem_insert_of_mem hj))

theorem comb_one {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι → MvPowerSeries σ Q) (i : ι) :
    comb ((1 : Matrix ι ι B) i) e = e i := by
  simp [comb, Matrix.one_apply]

theorem comb_mul {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι → MvPowerSeries σ Q)
    (f : κ → MvPowerSeries σ Q) (P : ι → κ → B) (P' : κ → ι → B) (i : ι) :
    e i - comb ((Matrix.of P * Matrix.of P') i) e =
      (e i - comb (P i) f) + ∑ j, algebraMap B Q (P i j) • (f j - comb (P' j) e) := by
  simp only [comb, Matrix.mul_apply, Matrix.of_apply, smul_sub, Finset.sum_sub_distrib,
    Finset.smul_sum, smul_smul, ← map_mul, map_sum, Finset.sum_smul]
  rw [Finset.sum_comm (f := fun j k => algebraMap B Q (P i j * P' j k) • e k)]
  abel

theorem mul_eq_one {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) {ι κ : Type} [Fintype ι]
    [Fintype κ] [DecidableEq ι] (e : ι → MvPowerSeries (Fin d) Q) (f : κ → MvPowerSeries (Fin d) Q)
    (he : IsBasis μ e) (P : ι → κ → B) (P' : κ → ι → B)
    (h1 : ∀ i, In (⊤ : Ideal B) (e i - comb (P i) f))
    (h2 : ∀ j, In (⊤ : Ideal B) (f j - comb (P' j) e)) :
    Matrix.of P * Matrix.of P' = 1 := by
  funext i
  obtain ⟨b, -, hb⟩ := he.2 (e i) (he.1 i)
  have hA : In (⊤ : Ideal B) (e i - comb ((Matrix.of P * Matrix.of P') i) e) := by
    rw [comb_mul e f P P' i]
    exact in_add (h1 i) (in_sum _ _ fun j _ => in_smul _ (h2 j))
  have hB : In (⊤ : Ideal B) (e i - comb ((1 : Matrix ι ι B) i) e) := by
    rw [comb_one, sub_self]; exact in_zero
  exact (hb _ hA).trans (hb _ hB).symm

theorem trans_inverse : ∀ {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (e : ι → MvPowerSeries (Fin d) Q) (f : κ → MvPowerSeries (Fin d) Q), IsBasis μ e → IsBasis μ f → ∀ (P : ι → κ → B) (P' : κ → ι → B), (∀ i, In (⊤ : Ideal B) (e i - comb (P i) f)) → (∀ j, In (⊤ : Ideal B) (f j - comb (P' j) e)) → Matrix.of P * Matrix.of P' = 1 ∧ Matrix.of P' * Matrix.of P = 1 := by
  intro B Q _ _ _ d μ ι κ _ _ _ _ e f he hf P P' h1 h2
  exact ⟨mul_eq_one μ e f he P P' h1 h2, mul_eq_one μ f e hf P' P h2 h1⟩

end GlobalTheory.BasisTrans
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLogarithmBasis_transitionMatrices_inverse : ∀ {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (e : ι → MvPowerSeries (Fin d) Q) (f : κ → MvPowerSeries (Fin d) Q), IsBasis μ e → IsBasis μ f → ∀ (P : ι → κ → B) (P' : κ → ι → B), (∀ i, In (⊤ : Ideal B) (e i - comb (P i) f)) → (∀ j, In (⊤ : Ideal B) (f j - comb (P' j) e)) → Matrix.of P * Matrix.of P' = 1 ∧ Matrix.of P' * Matrix.of P = 1 := by
  atlas_forward_decl GlobalTheory.BasisTrans.trans_inverse
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

namespace GlobalTheory.TangentComb

theorem in_top_add_smul {O Q σ : Type} [CommRing O] [CommRing Q] [Algebra O Q]
    {f g : MvPowerSeries σ Q} (hf : In (⊤ : Ideal O) f) (hg : In (⊤ : Ideal O) g) (a : O) :
    In (⊤ : Ideal O) (f + algebraMap O Q a • g) := by
  intro α
  obtain ⟨b, -, hb⟩ := hf α
  obtain ⟨b', -, hb'⟩ := hg α
  refine ⟨b + a * b', trivial, ?_⟩
  rw [map_add, map_smul, hb, hb', map_add, map_mul, smul_eq_mul]

theorem ql_add_smul {O Q : Type} [CommRing O] [CommRing Q] [Algebra O Q] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {f g : MvPowerSeries (Fin d) Q} (hf : QL μ ⊤ f) (hg : QL μ ⊤ g) (a : O) :
    QL μ ⊤ (f + algebraMap O Q a • g) := by
  have hμ' : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hμ, map_zero]
  refine ⟨?_, fun i => ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, map_add, map_smul, coeff_zero_eq_constantCoeff_apply,
      coeff_zero_eq_constantCoeff_apply, hf.1, hg.1, smul_zero, add_zero]
  · obtain ⟨b, -, hb⟩ := hf.2.1 i
    obtain ⟨b', -, hb'⟩ := hg.2.1 i
    refine ⟨b + a * b', trivial, ?_⟩
    simp only [lin] at hb hb' ⊢
    rw [map_add, map_smul, hb, hb', map_add, map_mul, smul_eq_mul]
  · rw [formalCoboundary_add hμ', formalCoboundary_smul hμ']
    exact in_top_add_smul hf.2.2 hg.2.2 a

theorem ql_zero {O Q : Type} [CommRing O] [CommRing Q] [Algebra O Q] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0) :
    QL μ ⊤ (0 : MvPowerSeries (Fin d) Q) := by
  have hμ' : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hμ, map_zero]
  have h0 : cob1 (up Q μ) (0 : MvPowerSeries (Fin d) Q) = 0 := by
    have := formalCoboundary_smul hμ' (0 : Q) (0 : MvPowerSeries (Fin d) Q)
    rwa [zero_smul, zero_smul] at this
  refine ⟨map_zero _, fun i => ⟨0, trivial, ?_⟩, ?_⟩
  · simp [lin]
  · rw [h0]
    exact In.top_iff.2 ⟨0, map_zero _⟩

end GlobalTheory.TangentComb

open GlobalTheory.TangentComb in
theorem GlobalTheory.TangentComb.main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) {ι : Type} [Fintype ι] (e : ι → MvPowerSeries (Fin d) C), (∀ m, QL c.μ ⊤ (e m)) → ∀ (L : ι → G.dual.Lie), (∀ m, c.IsLie (e m) (L m)) → ∀ (g : MvPowerSeries (Fin d) C), QL c.μ ⊤ g → ∀ (a : ι → O), In (⊤ : Ideal O) (g - comb a e) → c.IsLie g (∑ m, a m • L m) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c ι _ e he L hL g hg a hint
  classical
  have hF : IsFrame p C (RingHom.id O) := GlobalTheory.T.isTorsionFreePDThickeningFrame_valuation_integers p C v O hv
  have lin := GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c C hF
  have hμ := c.isLaw.const

  have key : ∀ s : Finset ι, QL c.μ ⊤ (∑ m ∈ s, algebraMap O C (a m) • e m) ∧
      c.IsLie (∑ m ∈ s, algebraMap O C (a m) • e m) (∑ m ∈ s, a m • L m) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact ⟨ql_zero hμ, c.isLie_zero hF.inj⟩
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, add_comm, add_comm (a j • L j)]
      exact ⟨ql_add_smul hμ ih.1 (he j) (a j),
        (lin _ _ _ _ (a j) ih.2 (hL j)).1 ih.1 (he j)⟩
  obtain ⟨hQ, hI⟩ := key Finset.univ
  obtain ⟨l, hl, -⟩ := GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c C hF g hg
  have h1 := (lin g (comb a e) l (∑ m, a m • L m) (-1) hl hI).1 hg hQ
  have hser : g + algebraMap O C (-1) • comb a e = g - comb a e := by
    rw [map_neg, map_one, neg_one_smul, sub_eq_add_neg]
  rw [hser] at h1
  obtain ⟨s, hs⟩ := In.top_iff.1 hint
  have h0 := (lin _ (comb a e) _ (∑ m, a m • L m) 0 h1 hI).2.1 ⟨s, hs.symm⟩
  rw [neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h0
  exact h0 ▸ hl
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentVector_quasiLogarithm_of_congruent_combination : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) {ι : Type} [Fintype ι] (e : ι → MvPowerSeries (Fin d) C), (∀ m, QL c.μ ⊤ (e m)) → ∀ (L : ι → G.dual.Lie), (∀ m, c.IsLie (e m) (L m)) → ∀ (g : MvPowerSeries (Fin d) C), QL c.μ ⊤ g → ∀ (a : ι → O), In (⊤ : Ideal O) (g - comb a e) → c.IsLie g (∑ m, a m • L m) := by
  atlas_forward_decl GlobalTheory.TangentComb.main
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SmallSecondTangent

theorem tangent_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ Θ : F.Q →+* C, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O C (F.θ b)) → ∃ lb : Module.Basis (Fin k) O G.dual.Lie, ∀ j, c.IsLie (map Θ (e (Sum.inr j))) (lb j) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hlift hμ k e he hadapt Θ hΘ
  have hF : IsFrame p C (RingHom.id O) := GlobalTheory.FrameIntegers.isFrame_integers p C v O hv
  have hμeq : (fun i => map F.θ (μ' i)) = c.μ := funext hμ
  obtain ⟨k', es, lbs, hbs, -, hcobs, hlies⟩ := GlobalTheory.T.exists_adapted_quasiLog_basis_pDivGroup_lieDual p C v O hv G d c C hF

  have hlift1 : ∀ m, ∃ f : MvPowerSeries (Fin d) F.Q, QL μ' ⊤ f ∧ map Θ f = es m := by
    intro m
    have hq : QL (fun i => map F.θ (μ' i)) ⊤ (es m) := hμeq ▸ hbs.1 m
    choose b _ hb using hq.2.1
    choose w hw using fun i => F.frame.surj (b i)
    obtain ⟨f, hf, hf', -⟩ := GlobalTheory.QLog.KLift.lift_quasiLog p F.B O F.Q F.θ F.frame d μ' hlift C hF
      Θ hΘ (es m) w hq (fun i => by rw [hb, hw])
    exact ⟨f, hf, hf'⟩
  choose f hfq hfm using hlift1
  have hfb : IsBasis μ' f := by
    refine GlobalTheory.basis_lift p F.B O F.Q F.θ F.frame d μ' hlift C hF Θ hΘ _ f hfq ?_
      (GlobalTheory.BChain.reflTransGen_isStep p C v O hv ε hε F)
    have : (fun i => map Θ (f i)) = es := funext hfm
    rw [this, hμeq]; exact hbs

  choose P hP using fun i => (hfb.2 (e i) (he.1 i)).exists
  choose P' hP' using fun j => (he.2 (f j) (hfq j)).exists
  obtain ⟨h1, h2⟩ := GlobalTheory.T.quasiLogarithmBasis_transitionMatrices_inverse μ' e f he hfb P P' hP hP'

  let Ls : Fin d ⊕ Fin k' → G.dual.Lie := Sum.elim 0 lbs
  have hLs : ∀ m, c.IsLie (es m) (Ls m) := by
    rintro (i | j)
    · obtain ⟨l, hl, -⟩ := GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c C hF (es (Sum.inl i)) (hbs.1 _)
      have := (GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c C hF _ _ l l 0 hl hl).2.2 (hcobs i)
      subst this; exact hl
    · exact hlies j
  have hμc : ∀ i, constantCoeff (μ' i) = 0 := hlift.const
  have hg : ∀ i, QL c.μ ⊤ (map Θ (e i)) := fun i => by
    rw [← hμeq]; exact GlobalTheory.SmallSecond.ql_map hΘ μ' hμc (he.1 i)
  have hrow : ∀ i, c.IsLie (map Θ (e i)) (∑ m, F.θ (P i m) • Ls m) := by
    intro i
    refine GlobalTheory.T.tangentVector_quasiLogarithm_of_congruent_combination p C v O hv G d c es (hbs.1) Ls hLs _ (hg i) _ ?_
    intro α
    obtain ⟨b, -, hb⟩ := hP i α
    refine ⟨F.θ b, trivial, ?_⟩
    have : map Θ (e i) - comb (fun m => F.θ (P i m)) es = map Θ (e i - comb (P i) f) := by
      rw [map_sub, GlobalTheory.SmallSecond.map_comb hΘ, funext hfm]
    rw [this, coeff_map, hb, hΘ]

  have hzero : ∀ i j, F.θ (P (Sum.inl i) (Sum.inr j)) = 0 := by
    intro i
    have hc : cob1 (up C c.μ) (map Θ (e (Sum.inl i))) = 0 := by
      rw [← hμeq]; exact GlobalTheory.SmallSecond.formalGroupLawCoboundaryOne_map_eq_zero hΘ μ' hμc (hadapt i).1
    have h0 := (GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c C hF _ _ _ _ 0 (hrow (Sum.inl i)) (hrow (Sum.inl i))).2.2 hc
    simp only [Fintype.sum_sum_type, Ls, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, smul_zero,
      Finset.sum_const_zero, zero_add] at h0
    exact (Fintype.linearIndependent_iff.1 lbs.linearIndependent) _ h0
  obtain ⟨lb, hlb⟩ := GlobalTheory.T.exists_basis_of_blockLowerTriangular_inv' O G.dual.Lie d k k' lbs ((Matrix.of P).map F.θ)
    ((Matrix.of P').map F.θ) (by rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]) hzero
  refine ⟨lb, fun j => ?_⟩
  have := hrow (Sum.inr j)
  simp only [Fintype.sum_sum_type, Ls, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, smul_zero,
    Finset.sum_const_zero, zero_add] at this
  rw [hlb]; exact this

end GlobalTheory.SmallSecondTangent
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLogarithm_secondBlock_tangent_basis_dual_lie : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ Θ : F.Q →+* C, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O C (F.θ b)) → ∃ lb : Module.Basis (Fin k) O G.dual.Lie, ∀ j, c.IsLie (map Θ (e (Sum.inr j))) (lb j) := by
  atlas_forward_decl GlobalTheory.SmallSecondTangent.tangent_basis
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SmallSecond

theorem small_second : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → ∀ b : Fin k → F.B, (∀ l, ¬IsUnit (F.θ (U.mulVec (fun j => F.σ ((Sum.elim (fun _ => 0) b : Fin d ⊕ Fin k → F.B) j)) l))) → ∀ j, ¬IsUnit (F.θ (b j)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hμ' hc k e he hA U hU b hW j
  have hC : IsFrame p C (RingHom.id O) := GlobalTheory.FrameIntegers.isFrame_integers p C v O hv
  obtain ⟨Θ, hΘ⟩ := frame_fraction_map p F.B O F.Q F.θ F.frame C hC
  have hcμ : (fun i => map F.θ (μ' i)) = c.μ := funext hc
  have hconst : ∀ i, constantCoeff (μ' i) = 0 := hμ'.const

  have hQL : ∀ i, QL c.μ ⊤ (map Θ (e i)) := fun i => hcμ ▸ ql_map hΘ μ' hconst (he.1 i)
  have hlog : ∀ i, cob1 (up C c.μ) (map Θ (e (Sum.inl i))) = 0 := fun i =>
    hcμ ▸ formalGroupLawCoboundaryOne_map_eq_zero hΘ μ' hconst (hA i).1
  obtain ⟨lb, hlb⟩ := GlobalTheory.T.quasiLogarithm_secondBlock_tangent_basis_dual_lie p C v O hv ε hε F G d c μ' hμ' hc k e he hA Θ hΘ

  have hT := GlobalTheory.T.frobenius_linearCombination_zero_left_ainfFrame p O ε F d k e U (fun i => (hU i).1) b
  have hC1 := GlobalTheory.T.coboundary_frobenius_commute_mod_p_quasiLog p O ε F d μ' hμ' (Fin d ⊕ Fin k) e he.1 (Sum.elim (fun _ => 0) b)
  obtain ⟨F₁, t, hF₁, hlin, hpβ, hα⟩ := GlobalTheory.T.frobenius_congruence_combination_over_integers p C v O hv ε F d c.μ μ' hμ' hc k e he.1 _ b hW hT hC1
  have ht := GlobalTheory.T.not_isUnit_coeff_of_coboundary_small' p C v O hv d c.μ c.isLaw t hlin hα
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_integral_coboundaryOne_congr_frobenius p C v O hv d c.μ c.isLaw (map F.θ F₁) t ht
    (fun β => by rw [coeff_map]; exact hpβ β)
  have key : cob1 (up C c.μ) (comb (Sum.elim 0 fun j => F.θ (b j)) fun i => map Θ (e i)) =
      map (algebraMap O C) (map F.θ F₁) := by
    have h1 : (Sum.elim 0 fun j => F.θ (b j) : Fin d ⊕ Fin k → O) =
        fun i => F.θ ((Sum.elim (fun _ => 0) b : Fin d ⊕ Fin k → F.B) i) := by
      funext i; rcases i with i | i <;> simp
    rw [h1, ← map_comb hΘ, ← hcμ, ← map_formalGroupLawCoboundaryOne_square hΘ μ' hconst, ← hF₁]
    ext α; simp [coeff_map, hΘ]
  refine GlobalTheory.T.tangent_coords_nonunit_alt p C v O hv G d c C hC k (fun i => map Θ (e i)) lb hQL hlb hlog
    (fun j => F.θ (b j)) u (fun α => ⟨_, hu α, ?_⟩) j
  rw [key, ← map_sub, coeff_map, map_sub]

end GlobalTheory.SmallSecond
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_mod_maximal_of_frobenius_image_small : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → ∀ b : Fin k → F.B, (∀ l, ¬IsUnit (F.θ (U.mulVec (fun j => F.σ ((Sum.elim (fun _ => 0) b : Fin d ⊕ Fin k → F.B) j)) l))) → ∀ j, ¬IsUnit (F.θ (b j)) := by
  atlas_forward_decl GlobalTheory.SmallSecond.small_second
end
