import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffsInIdealOfPowerSeriesIffImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCoboundaryRepresentativeCocycleRules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartEvalSquareProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvSubstNatMultiplePrimePowConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefectCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveModPrimeEqQuasiLogarithmDefect

section
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem dual_eq_smul_of_forall_dvd :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (a : O), (∀ x : O, a * x = 0 → x = 0) →
      ∀ l : Module.Dual O M, (∀ w, a ∣ l w) → ∃ l' : Module.Dual O M, l = a • l' := by
  intro O M _ _ _ a ha l hl
  have cancel : ∀ x y : O, a * x = a * y → x = y := by
    intro x y hxy
    have := ha (x - y) (by rw [mul_sub, hxy, sub_self])
    exact sub_eq_zero.mp this
  let c : M → O := fun w => Classical.choose (hl w)
  have hc : ∀ w, l w = a * c w := fun w => Classical.choose_spec (hl w)
  refine ⟨{ toFun := c, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    apply cancel
    rw [mul_add, ← hc, ← hc, ← hc, map_add]
  · intro r x
    apply cancel
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [← hc, map_smul, hc, smul_eq_mul]
    ring
  · ext w
    simp only [LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
    exact hc w

end GlobalTheory
end

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_eq_smul_of_forall_dvd' : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (a : O), (∀ x : O, a * x = 0 → x = 0) → ∀ l : Module.Dual O M, (∀ w, a ∣ l w) → ∃ l' : Module.Dual O M, l = a • l' := by
  atlas_forward_decl GlobalTheory.dual_eq_smul_of_forall_dvd
end

section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalChart_evalSquare_properties : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ n f, c.ev₂ n (inL f) = c.ev n f ⊗ₜ[O] 1 ∧ c.ev₂ n (inR f) = 1 ⊗ₜ[O] c.ev n f ∧ c.ev₂ n (subst c.μ f) = Coalgebra.comul (R := O) (c.ev n f) ∧ c.ev₂ n (cob1 c.μ f) = cobOne O (G.A n) (c.ev n f) := by
  first | exact @GlobalTheory.QLog.Chart.ev₂_eval | exact GlobalTheory.QLog.Chart.ev₂_eval | (intros; apply GlobalTheory.QLog.Chart.ev₂_eval <;> assumption)
end

section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem cobOne_ev_defect_dvd : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E), QL c.μ ⊤ f → ∀ (n : ℕ) (s : MvPowerSeries (Fin d) O), map (algebraMap O E) s = defect c.μ (p ^ n) f → ∃ z, cobOne O (G.A n) (c.ev n s) = (p : O) ^ n • z := by
  intro p _ O E _ _ _ hF G d c f hf n s hs
  haveI : IsAdicComplete (Ideal.span {(p : O)}) O := hF.complete
  obtain ⟨hf0, -, hfc⟩ := hf
  obtain ⟨κ, -, hκ⟩ := ((series_in_ideal_iff_image O E (Fin d ⊕ Fin d) ⊤ _).1).1 hfc
  obtain ⟨-, hκ0, hrest⟩ := GlobalTheory.T.integral_coboundary_representative_cocycle_rules O E d c.μ c.isLaw hF.inj f κ hκ
  have hcob := (hrest (p ^ n) s hs).1
  refine ⟨c.ev₂ n κ, ?_⟩
  rw [← (GlobalTheory.T.formalChart_evalSquare_properties p O G d c n s).2.2.2, hcob, map_sub, map_smul,
    (GlobalTheory.T.ev_subst_natMultiple_prime_pow_constant p O G d c n).2.1 κ, hκ0 hf0, map_zero, sub_zero, Nat.cast_pow]

end GlobalTheory.QLog
end

section
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

theorem exists_unique_dual_of_compatible_mod_pow :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (a : O)
      [IsAdicComplete (Ideal.span {a}) O] (u : ∀ n : ℕ, M →ₗ[O] O ⧸ Ideal.span {a ^ n}),
      (∀ n w (x : O), u (n + 1) w = Ideal.Quotient.mk _ x → u n w = Ideal.Quotient.mk _ x) →
      ∃! l : Module.Dual O M, ∀ n w, Ideal.Quotient.mk _ (l w) = u n w := by
  intro O M _ _ _ a _ u hu

  have sep : ∀ y : O, (∀ n : ℕ, y ∈ Ideal.span {a ^ n}) → y = 0 := by
    intro y hy
    refine IsHausdorff.haus' (I := Ideal.span {a}) y fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact hy n
  have key : ∀ w : M, ∃! y : O, ∀ n, Ideal.Quotient.mk (Ideal.span {a ^ n}) y = u n w := by
    intro w
    choose x hx using fun n => Ideal.Quotient.mk_surjective (u n w)
    have step : ∀ n, x n - x (n + 1) ∈ Ideal.span {a ^ n} := by
      intro n
      exact Ideal.Quotient.eq.mp ((hx n).trans (hu n w (x (n + 1)) (hx (n + 1)).symm))
    have cauchy : ∀ m n, m ≤ n → x m - x n ∈ Ideal.span {a ^ m} := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ k hmk ih =>
        have h2 : x k - x (k + 1) ∈ Ideal.span {a ^ m} :=
          (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow a hmk)) (step k)
        have := Ideal.add_mem _ ih h2
        simpa using this
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {a}) x (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
      exact cauchy m n hmn)
    refine ⟨L, fun n => ?_, fun y hy => ?_⟩
    · have h := hL n
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] at h
      rw [← hx n]
      exact Ideal.Quotient.eq.mpr (by simpa using (Ideal.span {a ^ n}).neg_mem h)
    · refine sub_eq_zero.mp (sep _ fun n => ?_)
      have h := hL n
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] at h
      exact Ideal.Quotient.eq.mp ((hy n).trans (hx n).symm) |> fun h' => by
        simpa using Ideal.add_mem _ h' h
  choose f hf huniq using key
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, ?_, ?_⟩
  · intro w w'
    refine (huniq (w + w') _ fun n => ?_).symm
    rw [map_add, map_add, hf, hf]
  · intro c w
    refine (huniq (c • w) _ fun n => ?_).symm
    rw [RingHom.id_apply, smul_eq_mul, map_mul, map_smul, ← hf w n, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq]
  · exact fun n w => hf w n
  · intro l hl
    exact LinearMap.ext fun w => huniq w (l w) fun n => hl n w

end GlobalTheory.PDiv
end

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_dual_of_compatible_mod_pow_of_adicComplete : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (a : O) [IsAdicComplete (Ideal.span {a}) O] (u : ∀ n : ℕ, M →ₗ[O] O ⧸ Ideal.span {a ^ n}), (∀ n w (x : O), u (n + 1) w = Ideal.Quotient.mk _ x → u n w = Ideal.Quotient.mk _ x) → ∃! l : Module.Dual O M, ∀ n w, Ideal.Quotient.mk _ (l w) = u n w := by
  atlas_forward_decl GlobalTheory.PDiv.exists_unique_dual_of_compatible_mod_pow
end

section
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

noncomputable section

namespace GlobalTheory

namespace PDiv

open Coalgebra Bialgebra

theorem exists_tangent_of_cobOne_eq_smul (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A]
    [Module.Finite O A] [Module.Projective O A] [Coalgebra.IsCocomm O A] (a : O) (b : A)
    (z : A ⊗[O] A) (h : cobOne O A b = a • z) :
    ∃ u : Cot O (CartierDual O A) →ₗ[O] O ⧸ Ideal.span {a},
      ∀ φ : CartierDual O A, u (dUnit O φ) = Ideal.Quotient.mk _ (φ b) := by
  let D : CartierDual O A →ₗ[O] O ⧸ Ideal.span {a} :=
    (Ideal.Quotient.mkₐ O (Ideal.span {a})).toLinearMap ∘ₗ CartierDual.evalAt O A b
  have hcomul : comul b = b ⊗ₜ 1 + 1 ⊗ₜ b + a • z := by
    rw [← h, cobOne_apply]; abel
  have hD : ∀ φ ψ : CartierDual O A, D (φ * ψ) =
      counitAlgHom O (CartierDual O A) φ • D ψ + counitAlgHom O (CartierDual O A) ψ • D φ := by
    intro φ ψ
    have e : (φ * ψ) b = φ b * ψ 1 + φ 1 * ψ b + a * CartierDual.pair O A A (φ ⊗ₜ ψ) z := by
      rw [CartierDual.mul_apply, hcomul, map_add, map_add, map_smul]
      simp
    have ha : Ideal.Quotient.mk (Ideal.span {a}) a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    simp only [D, LinearMap.comp_apply, CartierDual.evalAt_apply, AlgHom.toLinearMap_apply,
      Ideal.Quotient.mkₐ_eq_mk, e, map_add, map_mul, ha, zero_mul, add_zero, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq]
    rw [show counitAlgHom O (CartierDual O A) φ = φ 1 from rfl,
      show counitAlgHom O (CartierDual O A) ψ = ψ 1 from rfl]
    ring
  exact ⟨AugCot.lift _ D hD, fun φ => AugCot.lift_d _ D hD φ⟩

end PDiv

end GlobalTheory
end
end

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartierDual_tangent_of_coboundaryOne_eq_smul : ∀ (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [Module.Finite O A] [Module.Projective O A] [Coalgebra.IsCocomm O A] (a : O) (b : A) (z : A ⊗[O] A), cobOne O A b = a • z → ∃ u : Cot O (CartierDual O A) →ₗ[O] O ⧸ Ideal.span {a}, ∀ φ : CartierDual O A, u (dUnit O φ) = Ideal.Quotient.mk _ (φ b) := by
  atlas_forward_decl GlobalTheory.PDiv.exists_tangent_of_cobOne_eq_smul
end

section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.LieOfAdditive

theorem existsUnique_lie_of_additive : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (b : ∀ n, G.A n), (∀ n, ∃ z, cobOne O (G.A n) (b n) = (p : O) ^ n • z) → (∀ n, ∃ z, b (n + 1) = G.mulP n (b n) + (p : O) ^ n • z) → ∃! l : G.dual.Lie, ∀ (n : ℕ) (w : G.dual.omega) (φ : CartierDual O (G.A n)), dUnit O φ = w.1 n → (p : O) ^ n ∣ l w - φ (b n) := by
  intro p O _ _ G b hb hc
  have hu : ∀ n, ∃ u : Cot O (CartierDual O (G.A n)) →ₗ[O] O ⧸ Ideal.span {((p : O)) ^ n},
      ∀ φ : CartierDual O (G.A n), u (dUnit O φ) = Ideal.Quotient.mk _ (φ (b n)) := fun n => by
    obtain ⟨z, hz⟩ := hb n
    exact GlobalTheory.T.exists_cartierDual_tangent_of_coboundaryOne_eq_smul O (G.A n) ((p : O) ^ n) (b n) z hz
  choose u hu using hu
  let U : ∀ n : ℕ, G.dual.omega →ₗ[O] O ⧸ Ideal.span {((p : O)) ^ n} := fun n =>
    (u n).comp ((LinearMap.proj n).comp G.dual.omegaSub.subtype)
  have hU : ∀ n (w : G.dual.omega) (φ : CartierDual O (G.A n)), dUnit O φ = w.1 n →
      U n w = Ideal.Quotient.mk _ (φ (b n)) := by
    intro n w φ h
    show u n (w.1 n) = _
    rw [← h, hu]
  have key : ∀ n (w : G.dual.omega) (x : O), U (n + 1) w = Ideal.Quotient.mk _ x →
      U n w = Ideal.Quotient.mk _ x := by
    intro n w x hx
    obtain ⟨φ, hφ⟩ := AugCot.d_surjective _ (w.1 (n + 1))
    have h1 : dUnit O (CartierDual.map (G.mulP n) φ) = w.1 n := by
      rw [← w.2 n, ← hφ]; exact (cotMap_d _ _).symm
    rw [hU n w _ h1, CartierDual.map_apply]
    rw [hU (n + 1) w φ hφ] at hx
    obtain ⟨z, hz⟩ := hc n
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at hx ⊢
    rw [hz, map_add, map_smul, smul_eq_mul] at hx
    obtain ⟨k, hk⟩ := hx
    exact ⟨(p : O) * k - φ z, by linear_combination hk⟩
  obtain ⟨l, hl, huniq⟩ := GlobalTheory.T.existsUnique_dual_of_compatible_mod_pow_of_adicComplete O G.dual.omega (p : O) U key
  refine ⟨l, fun n w φ h => ?_, fun l' hl' => huniq l' fun n w => ?_⟩
  · have := (hl n w).trans (hU n w φ h)
    rwa [Ideal.Quotient.eq, Ideal.mem_span_singleton] at this
  · obtain ⟨φ, hφ⟩ := AugCot.d_surjective _ (w.1 n)
    rw [hU n w φ hφ, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact hl' n w φ hφ

end GlobalTheory.LieOfAdditive
end

section
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem QLog.Chart.existsUnique_isLie : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E), QL c.μ ⊤ f → ∃! l : G.dual.Lie, c.IsLie f l := by
  intro p _ O E _ _ _ hF G d c f hf
  haveI : IsAdicComplete (Ideal.span {(p : O)}) O := hF.complete
  have hinj : Function.Injective (MvPowerSeries.map (σ := Fin d) (algebraMap O E)) := by
    intro s t h
    ext α
    have := congrArg (MvPowerSeries.coeff α) h
    simp only [MvPowerSeries.coeff_map] at this
    exact hF.inj this
  obtain ⟨hex, hcomp⟩ := GlobalTheory.QLog.defect_compat p O E hF G d c f hf
  choose s hs _ using fun n : ℕ => hex (p ^ n)
  have hadd := GlobalTheory.QLog.cobOne_ev_defect_dvd p O E hF G d c f hf
  obtain ⟨l, hl, huniq⟩ := GlobalTheory.LieOfAdditive.existsUnique_lie_of_additive p O G (fun n => c.ev n (s n))
    (fun n => hadd n (s n) (hs n)) (fun n => hcomp n (s n) (s (n + 1)) (hs n) (hs (n + 1)))
  refine ⟨l, ⟨fun n => In.top_iff.2 ⟨s n, hs n⟩, ?_⟩, ?_⟩
  · intro n w φ t hφ ht
    have : t = s n := hinj (ht.trans (hs n).symm)
    subst this
    exact hl n w φ hφ
  · intro l' hl'
    exact huniq l' fun n w φ hφ => hl'.2 n w φ (s n) hφ (hs n)

end GlobalTheory
end

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_isLie_of_isFrame_of_QL : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E), QL c.μ ⊤ f → ∃! l : G.dual.Lie, c.IsLie f l := by
  atlas_forward_decl GlobalTheory.QLog.Chart.existsUnique_isLie
end

section
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem tensor_projective_dvd_of_coord_dvd :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (N : Type) [AddCommGroup N] [Module O N] [Module.Projective O M] [Module.Projective O N] (a : O) (z : M ⊗[O] N), (∀ (φ : Module.Dual O M) (ψ : Module.Dual O N), a ∣ TensorProduct.dualDistrib O M N (φ ⊗ₜ ψ) z) → ∃ y, z = a • y := by
  intro O M _ _ _ N _ _ _ _ a z h
  obtain ⟨s, hs⟩ := (Module.Projective.out : ∃ s : M →ₗ[O] M →₀ O,
    Function.LeftInverse (Finsupp.linearCombination O id) s)
  obtain ⟨s', hs'⟩ := (Module.Projective.out : ∃ s : N →ₗ[O] N →₀ O,
    Function.LeftInverse (Finsupp.linearCombination O id) s)
  have hf : ∀ (w : M ⊗[O] N) (p : M × N), finsuppTensorFinsupp' O M N (TensorProduct.map s s' w) p =
      TensorProduct.dualDistrib O M N ((Finsupp.lapply p.1 ∘ₗ s) ⊗ₜ (Finsupp.lapply p.2 ∘ₗ s')) w := by
    intro w ⟨i, j⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [finsuppTensorFinsupp'_apply_apply, dualDistrib_apply]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  set f := finsuppTensorFinsupp' O M N (TensorProduct.map s s' z) with hfdef
  have hdiv : ∀ p, a ∣ f p := fun p => by rw [hfdef, hf]; exact h _ _
  choose c hc using hdiv
  let g : M × N →₀ O := ∑ p ∈ f.support, Finsupp.single p (c p)
  have hg : f = a • g := by
    simp only [g, Finset.smul_sum, Finsupp.smul_single, smul_eq_mul, ← hc]
    exact (Finsupp.sum_single f).symm
  have hid : (Finsupp.linearCombination O id : (M →₀ O) →ₗ[O] M) ∘ₗ s = LinearMap.id :=
    LinearMap.ext hs
  have hid' : (Finsupp.linearCombination O id : (N →₀ O) →ₗ[O] N) ∘ₗ s' = LinearMap.id :=
    LinearMap.ext hs'
  refine ⟨TensorProduct.map (Finsupp.linearCombination O id) (Finsupp.linearCombination O id)
    ((finsuppTensorFinsupp' O M N).symm g), ?_⟩
  rw [← map_smul, ← map_smul, ← hg, hfdef, LinearEquiv.symm_apply_apply, ← LinearMap.comp_apply,
    ← TensorProduct.map_comp, hid, hid', TensorProduct.map_id, LinearMap.id_apply]

end GlobalTheory
end

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_smul_of_dvd_dualDistrib : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (N : Type) [AddCommGroup N] [Module O N] [Module.Projective O M] [Module.Projective O N] (a : O) (z : M ⊗[O] N), (∀ (φ : Module.Dual O M) (ψ : Module.Dual O N), a ∣ TensorProduct.dualDistrib O M N (φ ⊗ₜ ψ) z) → ∃ y, z = a • y := by
  atlas_forward_decl GlobalTheory.tensor_projective_dvd_of_coord_dvd
end

section
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem dual_quotient_form_eq_eval :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] [Module.Finite O M]
      [Module.Projective O M] (I : Ideal O) (u : Module.Dual O M →ₗ[O] O ⧸ I),
      ∃ b : M, ∀ φ, u φ = Ideal.Quotient.mk I (φ b) := by
  intro O M _ _ _ _ _ I u
  obtain ⟨v, hv⟩ := Module.projective_lifting_property (Submodule.mkQ I) u
    (Submodule.mkQ_surjective I)
  refine ⟨(Module.evalEquiv O M).symm v, fun φ => ?_⟩
  have h1 : φ ((Module.evalEquiv O M).symm v) = v φ := by
    have := congrArg (fun w : Module.Dual O (Module.Dual O M) => w φ)
      ((Module.evalEquiv O M).apply_symm_apply v)
    simpa using this
  rw [h1, ← hv]
  rfl

end GlobalTheory
end

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_point_dual_quotient_form_eq_eval : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] [Module.Finite O M] [Module.Projective O M] (I : Ideal O) (u : Module.Dual O M →ₗ[O] O ⧸ I), ∃ b : M, ∀ φ, u φ = Ideal.Quotient.mk I (φ b) := by
  atlas_forward_decl GlobalTheory.dual_quotient_form_eq_eval
end

section
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

private theorem dualDistrib_eq_mul'_map {O M N : Type} [CommRing O] [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (φ : Module.Dual O M) (ψ : Module.Dual O N) (t : M ⊗[O] N) :
    dualDistrib O M N (φ ⊗ₜ ψ) t = LinearMap.mul' O O (TensorProduct.map φ ψ t) := by
  induction t with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m n => simp [dualDistrib_apply]

theorem cartierDual_tangent_mod :
    ∀ (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [Module.Finite O A] [Module.Projective O A] [Coalgebra.IsCocomm O A] (a : O) (u : Cot O (CartierDual O A) →ₗ[O] O ⧸ Ideal.span {a}), ∃ (b : A) (z : A ⊗[O] A), cobOne O A b = a • z ∧ ∀ φ : CartierDual O A, u (dUnit O φ) = Ideal.Quotient.mk _ (φ b) := by
  intro O A _ _ _ _ _ _ a u
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_point_dual_quotient_form_eq_eval O A (Ideal.span {a})
    (u ∘ₗ AugCot.d (Bialgebra.counitAlgHom O (CartierDual O A)) ∘ₗ
      (CartierDual.toDual O A).symm.toLinearMap)
  have hb' : ∀ φ : CartierDual O A, u (dUnit O φ) = Ideal.Quotient.mk _ (φ b) := fun φ => hb φ.ofConv
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_eq_smul_of_dvd_dualDistrib O A A a (cobOne O A b) (fun φ ψ => by
    have hm := hb' (WithConv.toConv φ * WithConv.toConv ψ)
    rw [dUnit, AugCot.d_mul, map_add, map_smul, map_smul, ← dUnit, ← dUnit, hb', hb'] at hm
    simp only [Bialgebra.counitAlgHom_apply, CartierDual.counit_apply] at hm
    have hc : (WithConv.toConv φ * WithConv.toConv ψ).ofConv b =
        LinearMap.mul' O O (TensorProduct.map φ ψ (CoalgebraStruct.comul b)) := rfl
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, dualDistrib_eq_mul'_map,
      cobOne_apply]
    simp only [map_sub, TensorProduct.map_tmul, LinearMap.mul'_apply]
    rw [← hc, ← hm]
    simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul]
    ring)
  exact ⟨b, y, hy, hb'⟩

end GlobalTheory
end

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartierDual_tangent_mod_eq_eval_additive : ∀ (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [Module.Finite O A] [Module.Projective O A] [Coalgebra.IsCocomm O A] (a : O) (u : Cot O (CartierDual O A) →ₗ[O] O ⧸ Ideal.span {a}), ∃ (b : A) (z : A ⊗[O] A), cobOne O A b = a • z ∧ ∀ φ : CartierDual O A, u (dUnit O φ) = Ideal.Quotient.mk _ (φ b) := by
  atlas_forward_decl GlobalTheory.cartierDual_tangent_mod
end

section
section
noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem PDivGroup.dual_lie_exists_eval_mod_pow : ∀ (p : ℕ) (O : Type) [CommRing O]
    (G : PDivGroup p O) (l : G.dual.Lie) (n : ℕ), ∃ (b : G.A n) (z : G.A n ⊗[O] G.A n),
    cobOne O (G.A n) b = (p : O) ^ n • z ∧ ∀ (w : G.dual.omega) (φ : CartierDual O (G.A n)),
    dUnit O φ = w.1 n → (p : O) ^ n ∣ l w - φ b := by
  intro p O _ G l n
  let I : Ideal O := Ideal.span {(p : O) ^ n}
  let N : Submodule O G.dual.omega := Ideal.span {(p : O)} ^ n • ⊤
  let m : G.dual.omega →ₗ[O] O ⧸ I := (Ideal.Quotient.mkₐ O I).toLinearMap ∘ₗ l
  have hN : N ≤ LinearMap.ker m := by
    intro x hx
    have hx' : x ∈ (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O G.dual.omega) := hx
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at hx'
    obtain ⟨v, -, rfl⟩ := hx'
    rw [LinearMap.mem_ker]
    change Ideal.Quotient.mk I (l ((p : O) ^ n • v)) = 0
    rw [map_smul, smul_eq_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  let u : Cot O (CartierDual O (G.A n)) →ₗ[O] O ⧸ I :=
    N.liftQ m hN ∘ₗ (G.dual.omegaQuotEquiv n).symm.toLinearMap
  have hu : ∀ w : G.dual.omega, u (w.1 n) = Ideal.Quotient.mk I (l w) := by
    intro w
    have h := (G.dual.omegaQuotEquiv_mk n w)
    change N.liftQ m hN ((G.dual.omegaQuotEquiv n).symm (w.1 n)) = _
    rw [← h, LinearEquiv.symm_apply_apply]
    rfl
  obtain ⟨b, z, hb, hφ⟩ := GlobalTheory.T.cartierDual_tangent_mod_eq_eval_additive O (G.A n) ((p : O) ^ n) u
  refine ⟨b, z, hb, fun w φ hφw => ?_⟩
  have h1 := hφ φ
  rw [hφw, hu, Ideal.Quotient.eq] at h1
  exact Ideal.mem_span_singleton.1 h1

end GlobalTheory
end
end

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_lie_exists_additive_eval_mod_prime_pow : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (l : G.dual.Lie) (n : ℕ), ∃ (b : G.A n) (z : G.A n ⊗[O] G.A n), cobOne O (G.A n) b = (p : O) ^ n • z ∧ ∀ (w : G.dual.omega) (φ : CartierDual O (G.A n)), dUnit O φ = w.1 n → (p : O) ^ n ∣ l w - φ b := by
  atlas_forward_decl GlobalTheory.PDivGroup.dual_lie_exists_eval_mod_pow
end

section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem lie_surj_mod_p : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E],
    IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d),
    ∀ l : G.dual.Lie, ∃ (f : MvPowerSeries (Fin d) E) (l' l'' : G.dual.Lie),
      QL c.μ ⊤ f ∧ c.IsLie f l' ∧ l = l' + (p : O) • l'' := by
  intro p _ O E _ _ _ hF G d c l
  obtain ⟨b, z, hbz, hl⟩ := GlobalTheory.T.dual_lie_exists_additive_eval_mod_prime_pow p O G l 1
  rw [pow_one] at hbz
  obtain ⟨f, s, y, hf, hs, hy⟩ := GlobalTheory.T.additive_mod_prime_eq_quasiLogarithm_defect p O E hF G d c b z hbz
  obtain ⟨l', hl', -⟩ := GlobalTheory.T.existsUnique_isLie_of_isFrame_of_QL p O E hF G d c f hf
  have hdiv : ∀ w : G.dual.omega, (p : O) ∣ (l - l') w := by
    intro w
    obtain ⟨φ, hφ⟩ := AugCot.d_surjective _ (w.1 1)
    have h1 := hl w φ hφ
    have h2 := hl'.2 1 w φ s hφ (by rw [pow_one]; exact hs)
    rw [pow_one] at h1 h2
    rw [hy, map_add, map_smul, smul_eq_mul] at h2
    have h3 : (p : O) ∣ l' w - φ b := by
      have := dvd_add h2 (dvd_mul_right (p : O) (φ y))
      rwa [show l' w - (φ b + (p : O) * φ y) + (p : O) * φ y = l' w - φ b by ring] at this
    have := dvd_sub h1 h3
    rwa [show l w - φ b - (l' w - φ b) = (l - l') w by simp] at this
  obtain ⟨l'', hl''⟩ := GlobalTheory.T.dual_eq_smul_of_forall_dvd' O G.dual.omega (p : O) (fun x hx => hF.sat x hx) (l - l') hdiv
  exact ⟨f, l', l'', hf, hl', by rw [← hl'']; abel⟩

end GlobalTheory.QLog
end

section
section
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem exists_isLie_add_smul : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ l : G.dual.Lie, ∃ (f : MvPowerSeries (Fin d) E) (l' l'' : G.dual.Lie), QL c.μ ⊤ f ∧ c.IsLie f l' ∧ l = l' + (p : O) • l'' := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c E _ _ hE l
  exact lie_surj_mod_p p O E hE G d c l

end GlobalTheory.QLog
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quasiLogarithm_lie_add_p_smul : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ l : G.dual.Lie, ∃ (f : MvPowerSeries (Fin d) E) (l' l'' : G.dual.Lie), QL c.μ ⊤ f ∧ c.IsLie f l' ∧ l = l' + (p : O) • l'' := by
  atlas_forward_decl GlobalTheory.QLog.exists_isLie_add_smul
end
