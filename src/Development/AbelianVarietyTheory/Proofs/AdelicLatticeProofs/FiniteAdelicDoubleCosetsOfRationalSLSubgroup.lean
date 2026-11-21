import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EvalComplexPolyEqZeroOnRatZariskiClosure
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatZariskiClosurePointsIsGroup
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GaloisStableSubmoduleLeSpanRational
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAutStableSLMatrixGroupImageBlockDiagPartStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatMemRatZariskiClosurePoints
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.BlockDiagPartOfRatIdempotentOneAndMulOfTriangulaStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPolynomialSectionBlockDiagonalRational
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsFiniteAdeleLikePairElementary
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassFinitenessCompletelyReducible

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.RatClosure

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem subset_pts (Γ : Set (Matrix ι ι ℂ)) : Γ ⊆ pts Γ ℂ := fun g hg _ hf => hf g hg

omit [Fintype ι] [DecidableEq ι] in
theorem vanI_pts (Γ : Set (Matrix ι ι ℂ)) : vanI (pts Γ ℂ) = vanI Γ := by
  ext f
  exact ⟨fun h g hg => h g (subset_pts Γ hg), fun h g hg => hg f h⟩

omit [Fintype ι] [DecidableEq ι] in
theorem ev_map_aut (σ : ℂ ≃+* ℂ) (f : MvPolynomial (ι × ι) ℚ) (g : Matrix ι ι ℂ) :
    ev f (g.map σ) = σ (ev f g) := by
  unfold ev
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.aeval_X, Matrix.map_apply]

theorem exists_poly_of_dual (φ : Module.Dual ℂ (Matrix ι ι ℂ)) :
    ∃ f : MvPolynomial (ι × ι) ℂ, ∀ g, evC f g = φ g := by
  refine ⟨∑ ij : ι × ι, MvPolynomial.C (φ (Matrix.single ij.1 ij.2 1)) * MvPolynomial.X ij, fun g => ?_⟩
  conv_rhs => rw [Matrix.matrix_eq_sum_single g]
  simp only [evC, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : Matrix.single i j (g i j) = g i j • Matrix.single i j (1 : ℂ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this, map_smul, smul_eq_mul, mul_comm]

theorem ratClosure : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → IsQGroup (pts Γ ℂ) ∧ vanI (pts Γ ℂ) = vanI Γ ∧ Submodule.span ℂ (pts Γ ℂ) = Submodule.span ℂ Γ := by
  intro ι _ _ Γ h
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.ratZariskiClosurePoints_isGroup ι Γ h ℂ
  refine ⟨⟨⟨h1, h2, h3, h4, ?_⟩, ?_⟩, vanI_pts Γ, ?_⟩
  · intro σ g hg f hf
    rw [ev_map_aut, hg f hf, map_zero]
  · intro g hg f hf
    exact hg f (by rw [vanI_pts]; exact hf)
  · refine le_antisymm (Submodule.span_le.2 fun y hy => ?_) (Submodule.span_mono (subset_pts Γ))
    refine (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (Submodule.span ℂ Γ) y).1 fun φ hφ => ?_
    obtain ⟨f, hf⟩ := exists_poly_of_dual φ
    rw [← hf]
    refine GlobalTheory.T.evalComplexPoly_eq_zero_on_ratZariskiClosure ι Γ h.aut_mem f (fun g hg => ?_) y hy
    rw [hf]
    exact (Submodule.mem_dualAnnihilator φ).1 hφ g (Submodule.subset_span hg)

end GlobalTheory.ClassFin.RatClosure
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratZariskiClosure_of_autStable_SL_group : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → IsQGroup (pts Γ ℂ) ∧ vanI (pts Γ ℂ) = vanI Γ ∧ Submodule.span ℂ (pts Γ ℂ) = Submodule.span ℂ Γ := by
  atlas_forward_decl GlobalTheory.ClassFin.RatClosure.ratClosure
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_mem_mul_eq_zero_of_isNilpotent {R : Type*} [Ring R] (J : Ideal R) [J.IsTwoSided]
    (hJ : IsNilpotent J) (h0 : J ≠ ⊥) : ∃ a ∈ J, a ≠ 0 ∧ ∀ b ∈ J, b * a = 0 := by
  obtain ⟨n, hn⟩ := hJ
  by_contra hcon
  push Not at hcon
  have key : ∀ k : ℕ, J ^ (k + 1) ≠ ⊥ := by
    intro k
    induction k with
    | zero => simpa [Submodule.pow_one] using h0
    | succ k ih =>
      obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ih
      obtain ⟨b, hb, hba⟩ := hcon a (Ideal.pow_le_self (Nat.succ_ne_zero k) ha) ha0
      intro h
      apply hba
      have : b * a ∈ J ^ (k + 1 + 1) := by
        rw [Ideal.IsTwoSided.pow_succ]
        exact Ideal.mul_mem_mul hb ha
      rw [h] at this
      simpa using this
  apply key n
  rw [Submodule.pow_succ, hn]
  simp

theorem map_mem_jacobson_of_surjective {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (hf : Function.Surjective f) {b : R} (hb : b ∈ Ring.jacobson R) : f b ∈ Ring.jacobson S := by
  have : RingHomSurjective f := ⟨hf⟩
  exact Ring.le_comap_jacobson (f := f) hb

noncomputable def spanAlg {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Set (Matrix ι ι ℂ)} (h : IsPre Γ) :
    Subalgebra ℂ (Matrix ι ι ℂ) :=
  (Submodule.span ℂ Γ).toSubalgebra (Submodule.subset_span h.one_mem) (by
    intro x y hx hy
    have h1 := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact h.mul_mem a ha b hb)

theorem map_mem_spanAlg {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Set (Matrix ι ι ℂ)} (h : IsPre Γ)
    (σ : ℂ ≃+* ℂ) {x : Matrix ι ι ℂ} (hx : x ∈ spanAlg h) : x.map σ ∈ spanAlg h := by
  change x ∈ Submodule.span ℂ Γ at hx
  change Matrix.map x (⇑σ : ℂ → ℂ) ∈ Submodule.span ℂ Γ
  induction hx using Submodule.span_induction with
  | mem g hg => exact Submodule.subset_span (h.aut_mem σ g hg)
  | zero =>
    have e : Matrix.map (0 : Matrix ι ι ℂ) (⇑σ : ℂ → ℂ) = 0 := by
      ext i j; simp
    rw [e]; exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
    have e : Matrix.map (a + b) (⇑σ : ℂ → ℂ) = Matrix.map a (⇑σ : ℂ → ℂ) + Matrix.map b (⇑σ : ℂ → ℂ) := by
      ext i j; simp
    rw [e]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    have e : Matrix.map (c • a) (⇑σ : ℂ → ℂ) = σ c • Matrix.map a (⇑σ : ℂ → ℂ) := by
      ext i j; simp
    rw [e]; exact Submodule.smul_mem _ _ ha

noncomputable def spanAlgMap {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Set (Matrix ι ι ℂ)} (h : IsPre Γ)
    (σ : ℂ ≃+* ℂ) : spanAlg h →+* spanAlg h :=
  RingHom.codRestrict ((σ : ℂ →+* ℂ).mapMatrix.comp (spanAlg h).val.toRingHom) (spanAlg h)
    (fun x => map_mem_spanAlg h σ x.2)

theorem spanAlgMap_surjective {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Set (Matrix ι ι ℂ)} (h : IsPre Γ)
    (σ : ℂ ≃+* ℂ) : Function.Surjective (spanAlgMap h σ) := by
  intro y
  refine ⟨⟨y.1.map σ.symm, map_mem_spanAlg h σ.symm y.2⟩, ?_⟩
  apply Subtype.ext
  ext i j
  simp [spanAlgMap]

theorem ss_of_isSemisimpleRing {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Set (Matrix ι ι ℂ)} (h : IsPre Γ)
    [IsSemisimpleRing (spanAlg h)] : SS Γ := by
  intro W hW
  have hW' : ∀ x ∈ Submodule.span ℂ Γ, ∀ v ∈ W, x *ᵥ v ∈ W := by
    intro x hx v hv
    induction hx using Submodule.span_induction with
    | mem x hx => exact hW x hx v hv
    | zero => simp
    | add x y _ _ hx hy => rw [add_mulVec]; exact W.add_mem hx hy
    | smul c x _ hx => rw [smul_mulVec]; exact W.smul_mem _ hx
  let U : Submodule (spanAlg h) (ι → ℂ) :=
    { W.toAddSubmonoid with smul_mem' := fun c v hv => hW' c.1 c.2 v hv }
  obtain ⟨U', hU⟩ := exists_isCompl U
  have hsm : ∀ (x : Matrix ι ι ℂ), x ∈ spanAlg h → ∀ v ∈ U', x *ᵥ v ∈ U' :=
    fun x hx v hv => U'.smul_mem ⟨x, hx⟩ hv
  let W' : Submodule ℂ (ι → ℂ) :=
    { U'.toAddSubmonoid with
      smul_mem' := fun c v hv => by
        have := hsm (c • 1) ((spanAlg h).smul_mem (spanAlg h).one_mem c) v hv
        rwa [smul_mulVec, one_mulVec] at this }
  refine ⟨W', fun g hg v hv => hsm g (Submodule.subset_span hg) v hv, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    exact Submodule.disjoint_def.1 hU.disjoint x hx hx'
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    have : x ∈ U ⊔ U' := by rw [hU.sup_eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 this
    exact Submodule.add_mem_sup hy hz

theorem exists_socle_radical_of_not_ss :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → ¬ SS Γ → ∃ W : Submodule ℂ (ι → ℂ), (∀ g ∈ Γ, ∀ v ∈ W, g *ᵥ v ∈ W) ∧ (∀ σ : ℂ ≃+* ℂ, ∀ v ∈ W, (fun i => σ (v i)) ∈ W) ∧ ∃ a ∈ Submodule.span ℂ Γ, a ≠ 0 ∧ (∀ v, a *ᵥ v ∈ W) ∧ ∀ v ∈ W, a *ᵥ v = 0 := by
  intro ι _ _ Γ h hss
  have : IsArtinianRing (spanAlg h) := IsArtinianRing.of_finite ℂ _
  have h0 : Ring.jacobson (spanAlg h) ≠ ⊥ := by
    intro h0
    have := IsArtinianRing.isSemisimpleRing_iff_jacobson.2 h0
    exact hss (ss_of_isSemisimpleRing h)
  obtain ⟨a, ha, ha0, hba⟩ := exists_mem_mul_eq_zero_of_isNilpotent (Ring.jacobson (spanAlg h))
    IsSemiprimaryRing.isNilpotent h0
  let W : Submodule ℂ (ι → ℂ) :=
    { carrier := {v | ∀ b ∈ Ring.jacobson (spanAlg h), b.1 *ᵥ v = 0}
      add_mem' := fun {x y} hx hy b hb => by rw [mulVec_add, hx b hb, hy b hb, add_zero]
      zero_mem' := fun b _ => mulVec_zero _
      smul_mem' := fun c v hv b hb => by rw [mulVec_smul, hv b hb, smul_zero] }
  refine ⟨W, ?_, ?_, a.1, a.2, fun h1 => ha0 (Subtype.ext h1), ?_, fun v hv => hv a ha⟩
  · intro g hg v hv b hb
    have hg' : g ∈ spanAlg h := Submodule.subset_span hg
    have h1 : b * (⟨g, hg'⟩ : spanAlg h) ∈ Ring.jacobson (spanAlg h) := Ideal.mul_mem_right _ _ hb
    have h2 := hv _ h1
    rw [MulMemClass.coe_mul, ← mulVec_mulVec] at h2
    exact h2
  · intro σ v hv b hb
    have h1 : spanAlgMap h σ.symm b ∈ Ring.jacobson (spanAlg h) :=
      map_mem_jacobson_of_surjective _ (spanAlgMap_surjective h σ.symm) hb
    have h2 := hv _ h1
    funext i
    have h3 := congrArg σ (congrFun h2 i)
    simpa [spanAlgMap, mulVec, dotProduct, map_sum] using h3
  · intro v b hb
    rw [mulVec_mulVec]
    have := congrArg Subtype.val (hba b hb)
    change b.1 * a.1 = 0 at this
    rw [this, zero_mulVec]

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_subspace_not_semisimple : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → ¬ SS Γ → ∃ W : Submodule ℂ (ι → ℂ), (∀ g ∈ Γ, ∀ v ∈ W, g *ᵥ v ∈ W) ∧ (∀ σ : ℂ ≃+* ℂ, ∀ v ∈ W, (fun i => σ (v i)) ∈ W) ∧ ∃ a ∈ Submodule.span ℂ Γ, a ≠ 0 ∧ (∀ v, a *ᵥ v ∈ W) ∧ ∀ v ∈ W, a *ᵥ v = 0 := by
  atlas_forward_decl GlobalTheory.ClassFin.exists_socle_radical_of_not_ss
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_rat_idempotent_of_stable (ι : Type) [Fintype ι] [DecidableEq ι]
    (W : Submodule ℂ (ι → ℂ))
    (hW : ∀ σ : ℂ ≃+* ℂ, ∀ v ∈ W, (fun i => σ (v i)) ∈ W) :
    ∃ e : Matrix ι ι ℚ, e * e = e ∧ ∀ v, v ∈ W ↔ e.map (algebraMap ℚ ℂ) *ᵥ v = v := by
  classical

  obtain ⟨Wq, hWq⟩ : ∃ Wq : Submodule ℚ (ι → ℚ),
      ∀ q, q ∈ Wq ↔ (fun i => algebraMap ℚ ℂ (q i)) ∈ W := by
    refine ⟨{ carrier := {q | (fun i => algebraMap ℚ ℂ (q i)) ∈ W}
              add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, fun q => Iff.rfl⟩
    · intro a b ha hb
      have h : (fun i => algebraMap ℚ ℂ ((a + b) i))
          = (fun i => algebraMap ℚ ℂ (a i)) + (fun i => algebraMap ℚ ℂ (b i)) := by
        ext i; simp
      show (fun i => algebraMap ℚ ℂ ((a + b) i)) ∈ W
      rw [h]; exact W.add_mem ha hb
    · show (fun i => algebraMap ℚ ℂ ((0 : ι → ℚ) i)) ∈ W
      have h : (fun i => algebraMap ℚ ℂ ((0 : ι → ℚ) i)) = 0 := by ext i; simp
      rw [h]; exact W.zero_mem
    · intro c q hq
      have h : (fun i => algebraMap ℚ ℂ ((c • q) i))
          = algebraMap ℚ ℂ c • (fun i => algebraMap ℚ ℂ (q i)) := by
        ext i; simp
      show (fun i => algebraMap ℚ ℂ ((c • q) i)) ∈ W
      rw [h]; exact W.smul_mem _ hq

  obtain ⟨C, hC⟩ := Submodule.exists_isCompl Wq
  obtain ⟨f, hf1, hf2⟩ : ∃ f : (ι → ℚ) →ₗ[ℚ] (ι → ℚ), (∀ q, f q ∈ Wq) ∧ (∀ q ∈ Wq, f q = q) :=
    ⟨Wq.subtype ∘ₗ Wq.projectionOnto C hC, fun q => (Wq.projectionOnto C hC q).2,
      fun q hq => congrArg Subtype.val (Submodule.projectionOnto_apply_left hC ⟨q, hq⟩)⟩
  have hff : f ∘ₗ f = f := LinearMap.ext fun q => hf2 _ (hf1 q)

  have hstable := GlobalTheory.T.galoisStable_submodule_le_span_rational (ι → ℂ) ι (Pi.basisFun ℂ ι) W
    (fun σ w hw => ⟨fun i => σ (w i), hW σ w hw, fun k => by simp⟩)
  refine ⟨LinearMap.toMatrix' f, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hff]

  have hA : ∀ q : ι → ℚ, (LinearMap.toMatrix' f).map (algebraMap ℚ ℂ) *ᵥ
      (fun i => algebraMap ℚ ℂ (q i)) = fun i => algebraMap ℚ ℂ (f q i) := by
    intro q
    ext i
    rw [← LinearMap.toMatrix'_mulVec f q]
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

  have hB : ∀ v : ι → ℂ, (LinearMap.toMatrix' f).map (algebraMap ℚ ℂ) *ᵥ v ∈ W := by
    intro v
    have hcol : ∀ j, (fun i => algebraMap ℚ ℂ (LinearMap.toMatrix' f i j)) ∈ W := by
      intro j
      simp only [LinearMap.toMatrix'_apply]
      exact (hWq _).1 (hf1 _)
    have h : (LinearMap.toMatrix' f).map (algebraMap ℚ ℂ) *ᵥ v
        = ∑ j, v j • (fun i => algebraMap ℚ ℂ (LinearMap.toMatrix' f i j)) := by
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [h]
    exact W.sum_mem fun j _ => W.smul_mem _ (hcol j)
  intro v
  constructor
  · intro hv
    have hspan := hstable hv
    clear hv
    induction hspan using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨hwW, hq⟩ := hw
      choose q hq using hq
      have hw : w = fun i => algebraMap ℚ ℂ (q i) := by
        ext k
        rw [← Pi.basisFun_repr ℂ ι w k, hq k]
        exact (eq_ratCast (algebraMap ℚ ℂ) (q k)).symm
      have hqW : q ∈ Wq := (hWq q).2 (by rw [← hw]; exact hwW)
      rw [hw, hA, hf2 q hqW]
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy]
    | smul c x _ hx => rw [Matrix.mulVec_smul, hx]
  · intro hv
    rw [← hv]
    exact hB v

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rat_idempotent_of_autStable_subspace : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Submodule ℂ (ι → ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ v ∈ W, (fun i => σ (v i)) ∈ W) → ∃ e : Matrix ι ι ℚ, e * e = e ∧ ∀ v, v ∈ W ↔ e.map (algebraMap ℚ ℂ) *ᵥ v = v := by
  atlas_forward_decl GlobalTheory.ClassFin.exists_rat_idempotent_of_stable
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_rat_idempotent_blk_eq_zero : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → ¬ SS Γ → ∃ e : Matrix ι ι ℚ, e * e = e ∧ (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) ∧ ∃ a ∈ Submodule.span ℂ Γ, a ≠ 0 ∧ blk e a = 0 := by
  intro ι _ _ Γ hΓ hss
  obtain ⟨W, hWinv, hWσ, a, ha_span, ha0, ha_into, ha_kill⟩ := GlobalTheory.T.invariant_subspace_not_semisimple ι Γ hΓ hss
  obtain ⟨e, hee, hW⟩ := GlobalTheory.T.exists_rat_idempotent_of_autStable_subspace ι W hWσ

  have hEE : e.map (algebraMap ℚ ℂ) * e.map (algebraMap ℚ ℂ) = e.map (algebraMap ℚ ℂ) := by
    rw [← Matrix.map_mul, hee]
  have hEmem : ∀ v, e.map (algebraMap ℚ ℂ) *ᵥ v ∈ W := fun v => by
    rw [hW, Matrix.mulVec_mulVec, hEE]
  have hfix : ∀ w ∈ W, e.map (algebraMap ℚ ℂ) *ᵥ w = w := fun w hw => (hW w).1 hw
  refine ⟨e, hee, ?_, a, ha_span, ha0, ?_⟩
  ·
    intro g hg
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      hfix _ (hWinv g hg _ (hEmem v)), sub_self, Matrix.zero_mulVec]
  ·
    rw [Matrix.ext_iff_mulVec]
    intro v
    unfold blk
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha_kill _ (hEmem v),
      Matrix.mulVec_zero, zero_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.sub_mulVec, Matrix.one_mulVec, hfix _ (ha_into _), sub_self, Matrix.zero_mulVec]

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rat_idempotent_blockDiagPart_kills_span : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → ¬ SS Γ → ∃ e : Matrix ι ι ℚ, e * e = e ∧ (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) ∧ ∃ a ∈ Submodule.span ℂ Γ, a ≠ 0 ∧ blk e a = 0 := by
  atlas_forward_decl GlobalTheory.ClassFin.exists_rat_idempotent_blk_eq_zero
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem finrank_span_blk_image_lt :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ) (a : Matrix ι ι ℂ), a ∈ Submodule.span ℂ Γ → a ≠ 0 → blk e a = 0 → Module.finrank ℂ (Submodule.span ℂ (blk e '' Γ)) < Module.finrank ℂ (Submodule.span ℂ Γ) := by
  intro ι _ _ Γ e a ha ha0 hblk

  let L : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ :=
    { toFun := fun x => blk e x
      map_add' := fun x y => by
        simp only [blk, Matrix.mul_add, Matrix.add_mul]
        abel
      map_smul' := fun c x => by
        simp only [blk, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, smul_add] }
  have himg : Submodule.span ℂ (blk e '' Γ) = (Submodule.span ℂ Γ).map L := by
    rw [Submodule.map_span]
    rfl
  rw [himg]

  set S := Submodule.span ℂ Γ with hS
  let f := L.domRestrict S
  have hrange : LinearMap.range f = S.map L := LinearMap.range_domRestrict S L
  have hker : (⟨a, ha⟩ : S) ∈ LinearMap.ker f := by
    simp only [LinearMap.mem_ker, f, LinearMap.domRestrict_apply]
    exact hblk
  have hne : LinearMap.ker f ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at hker
    exact ha0 (congrArg Subtype.val hker)
  have hpos : 0 < Module.finrank ℂ (LinearMap.ker f) :=
    Nat.pos_of_ne_zero fun h => hne (Submodule.finrank_eq_zero.mp h)
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange] at hrn
  omega

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_span_blockDiagPart_image_lt : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ) (a : Matrix ι ι ℂ), a ∈ Submodule.span ℂ Γ → a ≠ 0 → blk e a = 0 → Module.finrank ℂ (Submodule.span ℂ (blk e '' Γ)) < Module.finrank ℂ (Submodule.span ℂ Γ) := by
  atlas_forward_decl GlobalTheory.ClassFin.finrank_span_blk_image_lt
end

section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem adjugate_entry_mem_subring {ι : Type} [Fintype ι] [DecidableEq ι] {R : Type} [CommRing R]
    (R₀ : Subring R) (A : Matrix ι ι R) (hA : ∀ i j, A i j ∈ R₀) (i j : ι) : A.adjugate i j ∈ R₀ := by
  let B : Matrix ι ι R₀ := Matrix.of fun i j => ⟨A i j, hA i j⟩
  have hB : A = R₀.subtype.mapMatrix B := by
    ext i j; rfl
  rw [hB, ← RingHom.map_adjugate]
  exact (B.adjugate i j).2

end GlobalTheory.ClassFin
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

variable {ι : Type} [Fintype ι] [DecidableEq ι]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma exists_nat_mul_ev_mem {R : Type} [CommRing R] [Algebra ℚ R]
    (R₀ : Subring R) (f : MvPolynomial (ι × ι) ℚ) : ∃ N : ℕ, 0 < N ∧
      ∀ u : Matrix ι ι R, (∀ i j, u i j ∈ R₀) → (N : R) * _root_.GlobalTheory.ClassFin.ev f u ∈ R₀ := by
  induction f using MvPolynomial.induction_on with
  | C q =>
    refine ⟨q.den, q.pos, fun u _ => ?_⟩
    have h : (q.den : R) * _root_.GlobalTheory.ClassFin.ev (MvPolynomial.C q) u = (q.num : R) := by
      simp only [_root_.GlobalTheory.ClassFin.ev, MvPolynomial.aeval_C]
      rw [← map_natCast (algebraMap ℚ R), ← map_mul,
        show (q.den : ℚ) * q = q.num by rw [mul_comm, Rat.mul_den_eq_num], map_intCast]
    rw [h]
    exact intCast_mem R₀ _
  | add f g hf hg =>
    obtain ⟨N₁, hN₁, h₁⟩ := hf
    obtain ⟨N₂, hN₂, h₂⟩ := hg
    refine ⟨N₁ * N₂, Nat.mul_pos hN₁ hN₂, fun u hu => ?_⟩
    have h : ((N₁ * N₂ : ℕ) : R) * _root_.GlobalTheory.ClassFin.ev (f + g) u =
        (N₂ : R) * ((N₁ : R) * _root_.GlobalTheory.ClassFin.ev f u) +
          (N₁ : R) * ((N₂ : R) * _root_.GlobalTheory.ClassFin.ev g u) := by
      simp only [_root_.GlobalTheory.ClassFin.ev, map_add]
      push_cast
      ring
    rw [h]
    exact R₀.add_mem (R₀.mul_mem (natCast_mem R₀ _) (h₁ u hu))
      (R₀.mul_mem (natCast_mem R₀ _) (h₂ u hu))
  | mul_X f n hf =>
    obtain ⟨N, hN, h⟩ := hf
    refine ⟨N, hN, fun u hu => ?_⟩
    have h' : (N : R) * _root_.GlobalTheory.ClassFin.ev (f * MvPolynomial.X n) u =
        ((N : R) * _root_.GlobalTheory.ClassFin.ev f u) * u n.1 n.2 := by
      simp only [_root_.GlobalTheory.ClassFin.ev, map_mul, MvPolynomial.aeval_X]
      ring
    rw [h']
    exact R₀.mul_mem (h u hu) (hu _ _)

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma exists_nat_mul_ev_section_mem {R : Type} [CommRing R] [Algebra ℚ R]
    (R₀ : Subring R) (b : ι → ι → MvPolynomial (ι × ι) ℚ) : ∃ N : ℕ, 0 < N ∧
      ∀ u : Matrix ι ι R, (∀ i j, u i j ∈ R₀) →
        ∀ i j, (N : R) * _root_.GlobalTheory.ClassFin.ev (b i j) u ∈ R₀ := by
  choose N hN h using fun p : ι × ι => exists_nat_mul_ev_mem R₀ (b p.1 p.2)
  refine ⟨∏ p, N p, Finset.prod_pos fun p _ => hN p, fun u hu i j => ?_⟩
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ (i, j))
  have h' : ((N (i, j) * m : ℕ) : R) * _root_.GlobalTheory.ClassFin.ev (b i j) u =
      (m : R) * ((N (i, j) : R) * _root_.GlobalTheory.ClassFin.ev (b i j) u) := by
    push_cast
    ring
  rw [hm, h']
  exact R₀.mul_mem (natCast_mem R₀ m) (h (i, j) u hu)

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma exists_nat_mul_rat_eq_int {κ : Type} [Fintype κ] (q : κ → ℚ) :
    ∃ M : ℕ, 0 < M ∧ ∀ k, ∃ z : ℤ, (M : ℚ) * q k = z := by
  refine ⟨∏ k, (q k).den, Finset.prod_pos fun k _ => (q k).pos, fun k => ?_⟩
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun k => (q k).den) (Finset.mem_univ k)
  refine ⟨m * (q k).num, ?_⟩
  rw [hm]
  push_cast
  calc ((q k).den : ℚ) * m * q k = m * (q k * (q k).den) := by ring
    _ = m * (q k).num := by rw [Rat.mul_den_eq_num]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma exists_nat_mul_linExt_mem {R : Type} [CommRing R] [Algebra ℚ R]
    (R₀ : Subring R) (c : ι × ι → ι × ι → ℚ) : ∃ K : ℕ, 0 < K ∧
      ∀ A : Matrix ι ι R, (∀ i j, A i j ∈ R₀) →
        ∀ i j, (K : R) * _root_.GlobalTheory.ClassFin.linExt c A i j ∈ R₀ := by
  obtain ⟨K, hK, hz⟩ := exists_nat_mul_rat_eq_int (fun p : (ι × ι) × (ι × ι) => c p.1 p.2)
  refine ⟨K, hK, fun A hA i j => ?_⟩
  simp only [_root_.GlobalTheory.ClassFin.linExt, Matrix.of_apply]
  rw [Finset.mul_sum]
  refine R₀.sum_mem fun kl _ => ?_
  obtain ⟨z, hz'⟩ := hz ((i, j), kl)
  have hz'' : (K : ℚ) * c (i, j) kl = z := hz'
  rw [← mul_assoc, ← map_natCast (algebraMap ℚ R) K, ← map_mul, hz'', map_intCast]
  exact R₀.mul_mem (intCast_mem R₀ z) (hA _ _)

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma matrix_mul_mem_subring_of_mem {R : Type} [CommRing R] (R₀ : Subring R) {A B : Matrix ι ι R}
    (hA : ∀ i j, A i j ∈ R₀) (hB : ∀ i j, B i j ∈ R₀) : ∀ i j, (A * B) i j ∈ R₀ :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact R₀.sum_mem fun k _ => R₀.mul_mem (hA i k) (hB k j)

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma exists_finset_integral_classes {R : Type} [CommRing R] [Algebra ℚ R]
    (R₀ : Subring R) (S : Set (Matrix ι ι R)) (hone : 1 ∈ S)
    (hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) (hadj : ∀ x ∈ S, x.adjugate ∈ S)
    (hdet : ∀ x ∈ S, x.det = 1)
    (hi : ∀ M : ℕ, 0 < M → ∀ r ∈ R₀, ∃ z : ℤ, ∃ a ∈ R₀, r = (z : R) + (M : R) * a)
    (hunit : ∀ N : ℕ, 0 < N → IsUnit (N : R)) (N : ℕ) (hN : 0 < N) :
    ∃ F : Finset (Matrix ι ι R), (∀ t ∈ F, t ∈ S) ∧ ∀ w ∈ S, (∀ i j, (N : R) * w i j ∈ R₀) →
      ∃ t ∈ F, ∃ p ∈ S, (∀ i j, p i j ∈ R₀) ∧ w = t * p := by
  classical
  obtain ⟨d, hd⟩ : ∃ d, d = Fintype.card ι - 1 := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = N * N ^ d := ⟨_, rfl⟩
  have hL0 : 0 < L := hL ▸ Nat.mul_pos hN (pow_pos hN d)
  haveI : NeZero L := ⟨hL0.ne'⟩
  have hLR : (L : R) = (N : R) * (N : R) ^ d := by rw [hL]; push_cast; ring
  let Cls : (ι → ι → ZMod L) → Matrix ι ι R → Prop := fun c w => w ∈ S ∧
    ∀ i j, ∃ z : ℤ, ∃ a ∈ R₀, (z : ZMod L) = c i j ∧ (N : R) * w i j = z + (L : R) * a
  refine ⟨Finset.univ.image (fun c => if h : ∃ w, Cls c w then h.choose else 1), ?_, ?_⟩
  · intro t ht
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 ht
    split_ifs with h
    · exact h.choose_spec.1
    · exact hone
  · intro w hw hwN
    choose z a ha hza using fun i j => hi L hL0 _ (hwN i j)
    have hc : ∃ w', Cls (fun i j => (z i j : ZMod L)) w' :=
      ⟨w, hw, fun i j => ⟨z i j, a i j, ha i j, rfl, hza i j⟩⟩
    refine ⟨hc.choose, Finset.mem_image.2 ⟨_, Finset.mem_univ _, dif_pos hc⟩, ?_⟩
    obtain ⟨htS, ht⟩ := hc.choose_spec
    obtain ⟨t, htdef⟩ : ∃ t, t = hc.choose := ⟨_, rfl⟩
    rw [← htdef] at htS ht ⊢
    have hD : ∀ i j, ∃ D ∈ R₀, w i j = t i j + (N : R) ^ d * D := by
      intro i j
      obtain ⟨z', a', ha', hz', hza'⟩ := ht i j
      obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub z' (z i j) L).1 hz'
      have hk' : ((z i j : ℤ) : R) - (z' : R) = (L : R) * k := by
        have h := congrArg (Int.cast : ℤ → R) hk
        push_cast at h
        exact h
      refine ⟨k + a i j - a', R₀.sub_mem (R₀.add_mem (intCast_mem R₀ k) (ha i j)) ha', ?_⟩
      apply (hunit N hN).mul_left_cancel
      rw [mul_add, hza i j, hza']
      linear_combination hk' + ((k : R) + a i j - a') * hLR
    choose D hDm hDeq using hD
    have hw' : w = t + (N : R) ^ d • Matrix.of D := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      exact hDeq i j
    have htN : ∀ i j, ((N : R) • t) i j ∈ R₀ := fun i j => by
      obtain ⟨z', a', ha', -, hza'⟩ := ht i j
      rw [Matrix.smul_apply, smul_eq_mul, hza']
      exact R₀.add_mem (intCast_mem R₀ z') (R₀.mul_mem (natCast_mem R₀ L) ha')
    have hp : t.adjugate * w = 1 + ((N : R) • t).adjugate * Matrix.of D := by
      rw [hw', Matrix.mul_add, Matrix.adjugate_mul, hdet t htS, one_smul, Matrix.adjugate_smul,
        ← hd, Matrix.mul_smul, Matrix.smul_mul]
    refine ⟨t.adjugate * w, hmul _ (hadj _ htS) _ hw, fun i j => ?_, ?_⟩
    · rw [hp, Matrix.add_apply]
      refine R₀.add_mem ?_ (matrix_mul_mem_subring_of_mem R₀ (_root_.GlobalTheory.ClassFin.adjugate_entry_mem_subring R₀ _ htN) hDm i j)
      rw [Matrix.one_apply]
      split_ifs
      · exact R₀.one_mem
      · exact R₀.zero_mem
    · rw [← Matrix.mul_assoc, Matrix.mul_adjugate, hdet t htS, one_smul, Matrix.one_mul]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma idempotent_block_mul_of_upper {A : Type*} [Ring A] (E x y : A) (hE : E * E = E)
    (hx : (1 - E) * x * E = 0) (hy : (1 - E) * y * E = 0) :
    E * (x * y) * E + (1 - E) * (x * y) * (1 - E) =
      (E * x * E + (1 - E) * x * (1 - E)) * (E * y * E + (1 - E) * y * (1 - E)) := by
  have h0 : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hE, sub_self]
  have h0' : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  have h1 : (1 - E) - (1 - E) * (1 - E) = 0 := by
    have h : (1 - E) * (1 - E) = 1 - E := by rw [sub_mul, one_mul, h0, sub_zero]
    rw [h, sub_self]
  have h2 : E - E * E = 0 := by rw [hE, sub_self]
  rw [← sub_eq_zero]
  have key : E * (x * y) * E + (1 - E) * (x * y) * (1 - E) -
      (E * x * E + (1 - E) * x * (1 - E)) * (E * y * E + (1 - E) * y * (1 - E)) =
      E * x * ((1 - E) * y * E) + ((1 - E) * x * E) * y * (1 - E) + E * x * (E - E * E) * y * E
        + (1 - E) * x * ((1 - E) - (1 - E) * (1 - E)) * y * (1 - E)
        - E * x * (E * (1 - E)) * y * (1 - E) - (1 - E) * x * ((1 - E) * E) * y * E := by
    noncomm_ring
  rw [key, hy, hx, h2, h1, h0, h0']
  simp

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma blk_mul_of_upper {R : Type} [CommRing R] [Algebra ℚ R] (e : Matrix ι ι ℚ)
    (he : e * e = e) (x y : Matrix ι ι R)
    (hx : (1 - e.map (algebraMap ℚ R)) * x * e.map (algebraMap ℚ R) = 0)
    (hy : (1 - e.map (algebraMap ℚ R)) * y * e.map (algebraMap ℚ R) = 0) :
    _root_.GlobalTheory.ClassFin.blk e (x * y) =
      _root_.GlobalTheory.ClassFin.blk e x * _root_.GlobalTheory.ClassFin.blk e y :=
  idempotent_block_mul_of_upper _ x y (by rw [← Matrix.map_mul, he]) hx hy

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma idempotent_block_one {A : Type*} [Ring A] (E : A) (hE : E * E = E) :
    E * 1 * E + (1 - E) * 1 * (1 - E) = 1 := by
  have h : E * 1 * E + (1 - E) * 1 * (1 - E) = 1 + 2 * (E * E - E) := by noncomm_ring
  rw [h, hE, sub_self, mul_zero, add_zero]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma blk_one_of_idempotent {R : Type} [CommRing R] [Algebra ℚ R] (e : Matrix ι ι ℚ)
    (he : e * e = e) : _root_.GlobalTheory.ClassFin.blk e (1 : Matrix ι ι R) = 1 :=
  idempotent_block_one _ (by rw [← Matrix.map_mul, he])

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma blk_map_algebraMap_eq_map_blk {R : Type} [CommRing R] [Algebra ℚ R] (e g : Matrix ι ι ℚ) :
    _root_.GlobalTheory.ClassFin.blk e (g.map (algebraMap ℚ R)) =
      (_root_.GlobalTheory.ClassFin.blk e g).map (algebraMap ℚ R) := by
  unfold _root_.GlobalTheory.ClassFin.blk
  simp [Matrix.map_mul, Matrix.map_add, Matrix.map_sub, Matrix.map_one]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma linExt_add {R : Type} [CommRing R] [Algebra ℚ R] (c : ι × ι → ι × ι → ℚ)
    (X Y : Matrix ι ι R) : _root_.GlobalTheory.ClassFin.linExt c (X + Y) =
      _root_.GlobalTheory.ClassFin.linExt c X + _root_.GlobalTheory.ClassFin.linExt c Y := by
  ext i j
  simp only [_root_.GlobalTheory.ClassFin.linExt, Matrix.of_apply, Matrix.add_apply, mul_add,
    Finset.sum_add_distrib]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma linExt_smul {R : Type} [CommRing R] [Algebra ℚ R] (c : ι × ι → ι × ι → ℚ)
    (k : R) (X : Matrix ι ι R) : _root_.GlobalTheory.ClassFin.linExt c (k • X) =
      k • _root_.GlobalTheory.ClassFin.linExt c X := by
  ext i j
  simp only [_root_.GlobalTheory.ClassFin.linExt, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma linExt_map_algebraMap {R : Type} [CommRing R] [Algebra ℚ R] (c : ι × ι → ι × ι → ℚ)
    (X : Matrix ι ι ℚ) : (_root_.GlobalTheory.ClassFin.linExt c X).map (algebraMap ℚ R) =
      _root_.GlobalTheory.ClassFin.linExt c (X.map (algebraMap ℚ R)) := by
  ext i j
  simp [_root_.GlobalTheory.ClassFin.linExt, map_sum, map_mul]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in

theorem _root_.GlobalTheory.ClassFin.cf_of_cf_blk_image : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), _root_.GlobalTheory.ClassFin.IsQGroup Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → _root_.GlobalTheory.ClassFin.AdelicPair R R₀ → _root_.GlobalTheory.ClassFin.CF (_root_.GlobalTheory.ClassFin.blk e '' Γ) R R₀ → _root_.GlobalTheory.ClassFin.CF Γ R R₀ := by
  intro ι _ _ Γ e R _ _ R₀ hΓ he hblock hR hCF
  classical
  obtain ⟨hone, hmul, hadj, hdet⟩ :=
    _root_.GlobalTheory.ClassFin.pts_group ι Γ hΓ.toIsPre R
  obtain ⟨-, hmulq, -, -⟩ := _root_.GlobalTheory.ClassFin.pts_group ι Γ hΓ.toIsPre ℚ
  obtain ⟨c, b, hsec⟩ := _root_.GlobalTheory.ClassFin.PolySection.exists_section ι Γ e hΓ he hblock
  obtain ⟨hU, hcc, hker, htri, hσ⟩ := hsec R
  obtain ⟨hUq, -, -, -, hσq⟩ := hsec ℚ
  obtain ⟨hi, hii, -⟩ := _root_.GlobalTheory.ClassFin.adelicPair_elementary R R₀ hR
  have hunit : ∀ N : ℕ, 0 < N → IsUnit (N : R) := fun N hN => by
    have h := (isUnit_iff_ne_zero.2 (by positivity : (N : ℚ) ≠ 0)).map (algebraMap ℚ R)
    rwa [map_natCast] at h
  obtain ⟨N, hN, hNb⟩ := exists_nat_mul_ev_section_mem (R := R) R₀ b
  obtain ⟨Kc, hKc, hcK⟩ := exists_nat_mul_linExt_mem (R := R) R₀ c
  obtain ⟨F, hFS, hF⟩ :=
    exists_finset_integral_classes R₀ _ hone hmul hadj hdet hi hunit N hN
  obtain ⟨TQ, hTQ, hTQd⟩ := hCF
  let σ : Matrix ι ι R → Matrix ι ι R := fun y => Matrix.of fun i j => _root_.GlobalTheory.ClassFin.ev (b i j) y
  refine ⟨(TQ ×ˢ F).image (fun p => σ p.1 * p.2), ?_, ?_⟩
  · intro s hs
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hs
    rw [Finset.mem_product] at hp
    exact hmul _ (hσ _ (hTQ _ hp.1)).1 _ (hFS _ hp.2)
  intro x hx
  have hinvl : ∀ a ∈ _root_.GlobalTheory.ClassFin.pts Γ R, a.adjugate * a = 1 := fun a ha => by
    rw [Matrix.adjugate_mul, hdet a ha, one_smul]
  have hinvr : ∀ a ∈ _root_.GlobalTheory.ClassFin.pts Γ R, a * a.adjugate = 1 := fun a ha => by
    rw [Matrix.mul_adjugate, hdet a ha, one_smul]
  have hbm : ∀ a ∈ _root_.GlobalTheory.ClassFin.pts Γ R, ∀ a' ∈ _root_.GlobalTheory.ClassFin.pts Γ R,
      _root_.GlobalTheory.ClassFin.blk e (a * a') =
        _root_.GlobalTheory.ClassFin.blk e a * _root_.GlobalTheory.ClassFin.blk e a' :=
    fun a ha a' ha' => blk_mul_of_upper e he a a' (htri a ha).1 (htri a' ha').1
  have hbinv : ∀ a ∈ _root_.GlobalTheory.ClassFin.pts Γ R,
      _root_.GlobalTheory.ClassFin.blk e a.adjugate * _root_.GlobalTheory.ClassFin.blk e a = 1 :=
    fun a ha => by rw [← hbm _ (hadj a ha) _ ha, hinvl a ha, blk_one_of_idempotent e he]
  have hbinv' : ∀ a ∈ _root_.GlobalTheory.ClassFin.pts Γ R,
      _root_.GlobalTheory.ClassFin.blk e a * _root_.GlobalTheory.ClassFin.blk e a.adjugate = 1 :=
    fun a ha => by rw [← hbm _ ha _ (hadj a ha), hinvr a ha, blk_one_of_idempotent e he]
  obtain ⟨γQ, hγQ, s, hs, u, hu, huint, hy⟩ := hTQd _ (htri x hx).2
  obtain ⟨γ', hγ'def⟩ : ∃ γ' : Matrix ι ι ℚ, γ' = Matrix.of fun i j =>
    _root_.GlobalTheory.ClassFin.ev (b i j) γQ := ⟨_, rfl⟩
  obtain ⟨hγ'P, hγ'b⟩ := hσq γQ hγQ
  rw [← hγ'def] at hγ'P hγ'b
  have hγR : γ'.map (algebraMap ℚ R) ∈ _root_.GlobalTheory.ClassFin.pts Γ R :=
    (_root_.GlobalTheory.ClassFin.RatPts.rat_mem_pts ι Γ).2 R _ hγ'P
  have hγRb : _root_.GlobalTheory.ClassFin.blk e (γ'.map (algebraMap ℚ R)) =
      γQ.map (algebraMap ℚ R) := by rw [blk_map_algebraMap_eq_map_blk, hγ'b]
  obtain ⟨hsP, hsb⟩ : σ s ∈ _root_.GlobalTheory.ClassFin.pts Γ R ∧ _root_.GlobalTheory.ClassFin.blk e (σ s) = s :=
    hσ s (hTQ s hs)
  obtain ⟨huP, hub⟩ : σ u ∈ _root_.GlobalTheory.ClassFin.pts Γ R ∧ _root_.GlobalTheory.ClassFin.blk e (σ u) = u :=
    hσ u hu
  obtain ⟨g, hgdef⟩ : ∃ g, g = γ'.map (algebraMap ℚ R) * σ s := ⟨_, rfl⟩
  have hgP : g ∈ _root_.GlobalTheory.ClassFin.pts Γ R := hgdef ▸ hmul _ hγR _ hsP
  have hgb : _root_.GlobalTheory.ClassFin.blk e g = γQ.map (algebraMap ℚ R) * s := by
    rw [hgdef, hbm _ hγR _ hsP, hγRb, hsb]
  obtain ⟨r, hrdef⟩ : ∃ r, r = g.adjugate * x := ⟨_, rfl⟩
  have hrP : r ∈ _root_.GlobalTheory.ClassFin.pts Γ R := hrdef ▸ hmul _ (hadj _ hgP) _ hx
  have hrb : _root_.GlobalTheory.ClassFin.blk e r = u := by
    rw [hrdef, hbm _ (hadj _ hgP) _ hx, hy, ← hgb, ← Matrix.mul_assoc, hbinv g hgP, Matrix.one_mul]
  obtain ⟨n, hndef⟩ : ∃ n, n = r * (σ u).adjugate := ⟨_, rfl⟩
  have hnP : n ∈ _root_.GlobalTheory.ClassFin.pts Γ R := hndef ▸ hmul _ hrP _ (hadj _ huP)
  have hnb : _root_.GlobalTheory.ClassFin.blk e n = 1 := by
    have h := hbinv' _ huP
    rw [hub] at h
    rw [hndef, hbm _ hrP _ (hadj _ huP), hrb]
    exact h
  obtain ⟨m, hmdef⟩ : ∃ m, m = σ s * n * (σ s).adjugate := ⟨_, rfl⟩
  have hmP : m ∈ _root_.GlobalTheory.ClassFin.pts Γ R := hmdef ▸ hmul _ (hmul _ hsP _ hnP) _ (hadj _ hsP)
  have hmb : _root_.GlobalTheory.ClassFin.blk e m = 1 := by
    rw [hmdef, hbm _ (hmul _ hsP _ hnP) _ (hadj _ hsP), hbm _ hsP _ hnP, hnb, Matrix.mul_one,
      hbinv' _ hsP]
  obtain ⟨Y, hY⟩ := hker m hmP hmb
  obtain ⟨K1, hK1, hK1s⟩ := hii (ι × ι) (fun p => σ s p.1 p.2)
  obtain ⟨K2, hK2, hK2s⟩ := hii (ι × ι) (fun p => (σ s).adjugate p.1 p.2)
  have hM : 0 < K2 * Kc * K1 := Nat.mul_pos (Nat.mul_pos hK2 hKc) hK1
  choose q a ha hqa using fun i j => hR.approx (K2 * Kc * K1) hM (Y i j)
  have hYsplit : Y = (Matrix.of q).map (algebraMap ℚ R) + ((K2 * Kc * K1 : ℕ) : R) • Matrix.of a := by
    ext i j
    simp only [Matrix.add_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    exact hqa i j
  obtain ⟨A, hAdef⟩ : ∃ A, A = _root_.GlobalTheory.ClassFin.linExt c ((Matrix.of q).map (algebraMap ℚ R)) :=
    ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ C, C = _root_.GlobalTheory.ClassFin.linExt c (Matrix.of a) := ⟨_, rfl⟩
  have hm : m = (1 + A) * (1 + ((K2 * Kc * K1 : ℕ) : R) • C) := by
    rw [hY, hYsplit, linExt_add, linExt_smul, ← hAdef, ← hCdef, mul_add, mul_one, add_mul,
      one_mul, Matrix.mul_smul, hAdef, hCdef, hcc, smul_zero, add_zero, add_assoc]
  obtain ⟨γ, hγdef⟩ : ∃ γ, γ = γ' * (1 + _root_.GlobalTheory.ClassFin.linExt c (Matrix.of q)) := ⟨_, rfl⟩
  have hγ : γ ∈ _root_.GlobalTheory.ClassFin.pts Γ ℚ := hγdef ▸ hmulq _ hγ'P _ (hUq _)
  have hγmap : γ.map (algebraMap ℚ R) = γ'.map (algebraMap ℚ R) * (1 + A) := by
    rw [hγdef, Matrix.map_mul, hAdef, ← linExt_map_algebraMap, Matrix.map_add _ (map_add _),
      Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨v, hvdef⟩ : ∃ v, v = (σ s).adjugate * (1 + ((K2 * Kc * K1 : ℕ) : R) • C) * σ s :=
    ⟨_, rfl⟩
  have hvP : v ∈ _root_.GlobalTheory.ClassFin.pts Γ R := by
    have h1 : 1 + ((K2 * Kc * K1 : ℕ) : R) • C ∈ _root_.GlobalTheory.ClassFin.pts Γ R := by
      rw [hCdef, ← linExt_smul]
      exact hU _
    exact hvdef ▸ hmul _ (hmul _ (hadj _ hsP) _ h1) _ hsP
  have hvint : ∀ i j, v i j ∈ R₀ := by
    have hv : v = 1 + ((K2 : R) • (σ s).adjugate) * ((Kc : R) • C) * ((K1 : R) • σ s) := by
      rw [hvdef, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hinvl _ hsP]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      congr 2
      push_cast
      ring
    have hCint : ∀ i j, ((Kc : R) • C) i j ∈ R₀ := fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul, hCdef]
      exact hcK _ ha i j
    have h2 : ∀ i j, ((K2 : R) • (σ s).adjugate) i j ∈ R₀ := fun i j => hK2s (i, j)
    have h3 : ∀ i j, ((K1 : R) • σ s) i j ∈ R₀ := fun i j => hK1s (i, j)
    intro i j
    rw [hv, Matrix.add_apply]
    refine R₀.add_mem ?_ (matrix_mul_mem_subring_of_mem R₀ (matrix_mul_mem_subring_of_mem R₀ h2 hCint) h3 i j)
    rw [Matrix.one_apply]
    split_ifs
    · exact R₀.one_mem
    · exact R₀.zero_mem
  have hp0P : v * σ u ∈ _root_.GlobalTheory.ClassFin.pts Γ R := hmul _ hvP _ huP
  have hp0N : ∀ i j, (N : R) * (v * σ u) i j ∈ R₀ := fun i j => by
    rw [← smul_eq_mul, ← Matrix.smul_apply, ← Matrix.mul_smul]
    exact matrix_mul_mem_subring_of_mem R₀ hvint (fun i j => hNb u huint i j) i j
  obtain ⟨t, ht, p, hpP, hpint, hp0⟩ := hF _ hp0P hp0N
  refine ⟨γ, hγ, σ s * t, Finset.mem_image.2 ⟨(s, t), Finset.mem_product.2 ⟨hs, ht⟩, rfl⟩,
    p, hpP, hpint, ?_⟩
  have e1 : x = g * r := by rw [hrdef, ← Matrix.mul_assoc, hinvr g hgP, Matrix.one_mul]
  have e2 : r = n * σ u := by rw [hndef, Matrix.mul_assoc, hinvl _ huP, Matrix.mul_one]
  have e3 : σ s * n = m * σ s := by
    rw [hmdef, Matrix.mul_assoc (σ s * n), hinvl _ hsP, Matrix.mul_one]
  have e4 : (1 + ((K2 * Kc * K1 : ℕ) : R) • C) * σ s = σ s * v := by
    rw [hvdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hinvr _ hsP, Matrix.one_mul]
  rw [hγmap]
  simp only [Matrix.mul_assoc]
  rw [← hp0, e1, e2, hgdef]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (σ s) n, e3, hm]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (1 + ((K2 * Kc * K1 : ℕ) : R) • C) (σ s), e4]
  simp only [Matrix.mul_assoc]

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasFiniteAdelicDoubleCosets_of_blockDiagPart_image : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → AdelicPair R R₀ → CF (blk e '' Γ) R R₀ → CF Γ R R₀ := by
  atlas_forward_decl GlobalTheory.ClassFin.cf_of_cf_blk_image
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem cf_congr_of_vanI_eq {ι : Type} [Fintype ι] [DecidableEq ι] {Γ Δ : Set (Matrix ι ι ℂ)}
    (h : vanI Γ = vanI Δ) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R) :
    CF Γ R R₀ ↔ CF Δ R R₀ := by

  have key : ∀ (S : Type) [CommRing S] [Algebra ℚ S], pts Γ S = pts Δ S := by
    intro S _ _
    simp only [pts, h]
  simp only [CF, key]

theorem cf_of_isQGroup : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → AdelicPair R R₀ → CF Γ R R₀ := by
  intro ι _ _

  suffices H : ∀ n : ℕ, ∀ (Γ : Set (Matrix ι ι ℂ)), Module.finrank ℂ (Submodule.span ℂ Γ) = n →
      ∀ (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → AdelicPair R R₀ → CF Γ R R₀ by
    intro Γ R _ _ R₀ hQ hA
    exact H _ Γ rfl R R₀ hQ hA
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Γ hn R _ _ R₀ hQ hA
    by_cases hS : SS Γ
    · exact GlobalTheory.T.classFiniteness_completelyReducible ι Γ R R₀ hQ hS hA
    · obtain ⟨e, he, hup, a, ha, ha0, hblk⟩ := GlobalTheory.T.exists_rat_idempotent_blockDiagPart_kills_span ι Γ hQ.toIsPre hS

      have hPre : IsPre (blk e '' Γ) := GlobalTheory.T.isAutStableSLMatrixGroup_image_blockDiagPart ι Γ e hQ.toIsPre he hup
      obtain ⟨hQ', hvan, hspan⟩ := GlobalTheory.T.ratZariskiClosure_of_autStable_SL_group ι (blk e '' Γ) hPre
      have hlt := GlobalTheory.T.finrank_span_blockDiagPart_image_lt ι Γ e a ha ha0 hblk
      have hcl : CF (pts (blk e '' Γ) ℂ) R R₀ :=
        ih _ (by rw [← hn, hspan]; exact hlt) _ rfl R R₀ hQ' hA
      have hblkCF : CF (blk e '' Γ) R R₀ := (cf_congr_of_vanI_eq hvan R R₀).mp hcl
      exact GlobalTheory.T.hasFiniteAdelicDoubleCosets_of_blockDiagPart_image ι Γ e R R₀ hQ he hup hA hblkCF

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelicDoubleCosets_of_rational_SL_subgroup : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → AdelicPair R R₀ → CF Γ R R₀ := by
  atlas_forward_decl GlobalTheory.ClassFin.cf_of_isQGroup
end
