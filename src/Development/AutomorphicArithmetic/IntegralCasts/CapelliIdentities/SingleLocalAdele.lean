import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FourierTransformBijective
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SymmetricShiftIsUnit
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.StandardAdditiveCharacter
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzFunctionGeneration

noncomputable section

namespace UpperTheory.Reformulated.B.SingleLocalAdele

open GlobalTheory.WeilM Matrix

section Local





variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [Invertible (2 : K)]
  {ψ : AddChar K ℂ} {κ : Type} [Fintype κ] [DecidableEq κ]



end Local

section Global

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private def sL (v : Pl F) : Fv F v →ₗ[F] AF F := (LinearMap.inr F (Ainf F) (Af F)).comp (singleFin v)

private theorem eval_single_local (v : Pl F) (a : Fv F v) : evFin F v (sL v a) = a := evalV_singleFin_self v a

private theorem mul_s (v : Pl F) (u : AF F) (a : Fv F v) : u * sL v a = sL v (evFin F v u * a) := by
  refine Prod.ext ((mul_zero _).trans rfl) (af_ext fun w => ?_)
  change evalV F w (u.2 * singleFin v a) = evalV F w (singleFin v (evFin F v u * a))
  rw [map_mul]
  by_cases h : w = v
  · subst h; rw [evalV_singleFin_self, evalV_singleFin_self]; rfl
  · rw [evalV_singleFin_ne h, evalV_singleFin_ne h, mul_zero]

private theorem sL_one_mul_eq_sL_evFin (v : Pl F) (u : AF F) : sL v 1 * u = sL v (evFin F v u) := by
  rw [mul_comm, mul_s, mul_one]

private theorem at_iff {M : Type} [AddCommGroup M] [Module (AF F) M] (v : Pl F) (z : M) :
    At (evFin F v) z ↔ sL v 1 • z = z := by
  refine ⟨fun h => ?_, fun h u hu => ?_⟩
  · have := h (1 - sL v 1) (by rw [map_sub, map_one, eval_single_local, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  · rw [← h, smul_smul, mul_s, hu, zero_mul, map_zero, zero_smul]


private def psiK (ψ : AddChar (AF F) ℂ) (v : Pl F) : AddChar (Fv F v) ℂ := ψ.compAddMonoidHom (sL v).toAddMonoidHom

private theorem psi_at (ψ : AddChar (AF F) ℂ) (v : Pl F) {a : AF F} (h : sL v 1 * a = a) :
    ψ a = psiK ψ v (evFin F v a) := by
  rw [sL_one_mul_eq_sL_evFin] at h
  exact (congrArg ψ h).symm


private theorem exists_schwartz (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ f : SchwartzMap V ℂ, f 0 = 1 := by
  let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport fun x => (b x : ℂ) := b.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) rfl
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun x => (b x : ℂ) := Complex.ofRealCLM.contDiff.comp b.contDiff
  refine ⟨h1.toSchwartzMap h2, ?_⟩
  change ((b 0 : ℝ) : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one), Complex.ofReal_one]

private def evp {κ : Type} (v : Pl F) (w : (κ → AF F) × (κ → AF F)) : (κ → Fv F v) × (κ → Fv F v) :=
  (fun i => evFin F v (w.1 i), fun i => evFin F v (w.2 i))

private theorem ev_dot {κ : Type} [Fintype κ] (v : Pl F) (a b : κ → AF F) :
    evFin F v (a ⬝ᵥ b) = (fun i => evFin F v (a i)) ⬝ᵥ fun i => evFin F v (b i) := by
  simp only [dotProduct, map_sum, map_mul]

open Classical in
private theorem acts_eq {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (v : Pl F) [Invertible (2 : Fv F v)]
    {w : (κ → AF F) × (κ → AF F)} (hw : sL v 1 • w = w) {φ φ₁ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB _)
    (h : Acts (evFin F v) (schr ψ w) φ φ₁) : φ₁ = schr (psiK ψ v) (evp v w) φ := by
  obtain ⟨f, hf⟩ := exists_schwartz (κ → mixedEmbedding.mixedSpace F)
  let S : Set (κ → Af F) := {z | ∀ i u, u ≠ v → z i u ∈ u.adicCompletionIntegers F}
  let r : (κ → AF F) → ℂ := fun x => f (fun i => evI F (x i)) * S.indicator 1 fun i => (x i).2
  have hr : ∀ x z : κ → AF F, sL v 1 • z = z → r (x + z) = r x := fun x z hz => by
    have h0 : ∀ i, z i = sL v (evFin F v (z i)) := fun i => (congrFun hz i).symm.trans (sL_one_mul_eq_sL_evFin v _)
    have h1 : (fun i => evI F ((x + z) i)) = fun i => evI F (x i) := funext fun i => by
      have : (z i).1 = 0 := by rw [h0]; rfl
      change InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + (z i).1) = _
      rw [this, add_zero]; rfl
    have h2 : (fun i => ((x + z) i).2) ∈ S ↔ (fun i => (x i).2) ∈ S := by
      refine forall_congr' fun i => forall_congr' fun u => forall_congr' fun hu => ?_
      have : evalV F u (z i).2 = 0 := by rw [h0]; exact evalV_singleFin_ne hu _
      change evalV F u ((x i).2 + (z i).2) ∈ _ ↔ evalV F u (x i).2 ∈ _
      rw [map_add, this, add_zero]
    simp only [r, h1, Set.indicator, h2, Pi.one_apply]
  have hg := UpperTheory.schwartz_function_generation F (fun u => (locField u).toLocallyCompactSpace) κ v φ hφ.1 hφ.2 _ fun _ => rfl
  have hR : Rest (evFin F v) φ r := ⟨fun x z hz => hr x z ((at_iff v z).1 hz),
    Submodule.subset_span ⟨f, _, hg, funext fun x => mul_left_comm _ _ _⟩⟩
  have hr0 : r 0 = 1 := by
    have h1 : (fun i => evI F ((0 : κ → AF F) i)) = 0 := funext fun i => map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    have h2 : (fun i => ((0 : κ → AF F) i).2) ∈ S := fun i u _ => zero_mem _
    simp only [r, h1, hf, Set.indicator_of_mem h2, Pi.one_apply, mul_one]
  funext X
  let x : κ → AF F := fun i => sL v (X i)
  have hx : sL v 1 • x = x := funext fun i => by
    change sL v 1 * sL v (X i) = sL v (X i)
    rw [sL_one_mul_eq_sL_evFin, eval_single_local]
  have hw1 : sL v 1 • w.1 = w.1 := congrArg Prod.fst hw
  have hw2 : sL v 1 • w.2 = w.2 := congrArg Prod.snd hw
  have hx1 : r x = 1 := by rw [← zero_add x, hr _ _ hx, hr0]
  have hX : (fun i => evFin F v (x i)) = X := funext fun i => eval_single_local v _
  have h2 : evFin F v (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
    refine (invOf_eq_right_inv ?_).symm
    rw [← map_ofNat (evFin F v) 2, ← map_mul, mul_invOf_self, map_one]
  have := congrFun (h r hR) x
  simp only [tens, schr] at this
  rw [hr _ _ hw1, hx1, hX, mul_one, mul_one, psi_at ψ v (by
    rw [mul_add, mul_left_comm, ← smul_eq_mul (sL v 1), ← smul_eq_mul (sL v 1), ← dotProduct_smul, ← dotProduct_smul,
      hw2]), map_add, map_mul, ev_dot, ev_dot, hX, h2] at this
  rw [← this]
  simp only [schr, evp, Pi.add_apply, map_add]
  congr 2
  funext i
  exact congrArg (· + _) (eval_single_local v _)



private theorem rT_smul (v : Pl F) (a : Fv F v) (y : Fv F v ⊗[F] E) :
    LinearMap.rTensor E (sL v) (a • y) = sL v a • LinearMap.rTensor E (sL v) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul b e =>
    refine congrArg (· ⊗ₜ[F] e) (?_ : sL v (a * b) = sL v a * sL v b)
    rw [mul_s, eval_single_local]


variable {n d : ℕ}


private def liftM (h : IsCMExt F E σ) {v : Pl F} (t : E →ₐ[F] Fv F v)
    (p : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) : Matrix (Fin n) (Fin d) (AE F E) :=
  Matrix.of fun i j => LinearMap.rTensor E (sL v) ((splitAlgEquiv h t).symm (p.1 (i, j), p.2 (i, j)))

variable (h : IsCMExt F E σ) {v : Pl F} (t : E →ₐ[F] Fv F v)







end Global

section Main

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}


end Main

end UpperTheory.Reformulated.B.SingleLocalAdele

end

