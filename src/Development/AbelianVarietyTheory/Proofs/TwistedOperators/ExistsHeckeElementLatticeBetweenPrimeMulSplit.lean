import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeSelfDualTraceForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneSubIdempotentSmulMemCompletionPrimeMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceHeckeDoubleCosetCardGaussBinom
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelativeLatticeVolumeOfDetValuation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitDeterminantCongruentElement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruence
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_sub_idempotent_smul_mem_completion_prime_mul : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (n : ℕ) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)),
    Formalism.L2.NTheta.IsIdemAt e P → ∀ y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)),
      (1 - finPart D e) • y ∈ GlobalTheory.AdLat.hat D.host.F ((P.asIdeal • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) := by
  first | exact @GlobalTheory.ComplOffPlace.one_sub_smul_mem | exact GlobalTheory.ComplOffPlace.one_sub_smul_mem | (intros; apply GlobalTheory.ComplOffPlace.one_sub_smul_mem <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField
open IsDedekindDomain Formalism.L2.NTheta
open scoped Matrix

namespace GlobalTheory.HatLocalChart

open scoped TensorProduct

theorem smul_mem_hat (D : D7) {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    {a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (ha : a ∈ intAE D)
    {y : Fin n → GlobalTheory.AdLat.RA D.host.F D.host.E} (hy : y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E))) :
    a • y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) := by
  induction ha using AddSubgroup.closure_induction with
  | mem a' ha' =>
    obtain ⟨b, hb, x, rfl⟩ := ha'
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨c, hc, w, hw, rfl⟩ := hz
      apply AddSubgroup.subset_closure
      refine ⟨b * c, fun v => ?_, x • w, L.smul_mem x hw, ?_⟩
      · have hbv := hb v
        simp only [Formalism.MainNotions.StandardLattice.intAf, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV, Set.mem_setOf_eq] at hbv
        exact mul_mem hbv (hc v)
      · funext i
        simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul]
        rfl
    | zero => rw [smul_zero]; exact zero_mem _
    | add y₁ y₂ _ _ h₁ h₂ => rw [smul_add]; exact add_mem h₁ h₂
    | neg y _ h => rw [smul_neg]; exact neg_mem h
  | zero => rw [zero_smul]; exact zero_mem _
  | add a₁ a₂ _ _ h₁ h₂ => rw [add_smul]; exact add_mem h₁ h₂
  | neg a _ h => rw [neg_smul]; exact neg_mem h

set_option maxHeartbeats 1000000 in

theorem exists_chart : ∀ (D : D7) (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (π : GlobalTheory.SplitPlace.RF D →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v → AE D) (n : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), e * e = e →
    (∀ a, π (finPart D (s a)) = a) → (∀ x, finPart D (s (π x)) = finPart D e * x) →
    (∀ x, finPart D e * x ∈ intAE D ↔ π x ∈ Formalism.UG.Ov D.host.F v) →
    L.FG → Submodule.span D.host.E (L : Set (Fin n → D.host.E)) = ⊤ →
    ∃ C : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v), ∀ y : Fin n → GlobalTheory.SplitPlace.RF D,
      finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) ↔
        ∀ i, ((C⁻¹ : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1 *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v := by
  intro D e v π s n L he h1 h2 h3 hfg hspan
  have hπ1 : π (finPart D e) = 1 := by
    have h := h2 1
    rw [map_one, mul_one] at h
    rw [← h, h1 1]
  have heint : finPart D e ∈ intAE D := by
    have h := (h3 1).2 (by rw [map_one]; exact one_mem _)
    rwa [mul_one] at h
  have hπint : ∀ x ∈ intAE D, π x ∈ Formalism.UG.Ov D.host.F v := fun x hx =>
    (h3 x).1 (GlobalTheory.SplitLatBasis.mul_mem_intAE D heint hx)
  have hone : ∀ w : HeightOneSpectrum (𝓞 D.host.F),
      (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) w ∈ w.adicCompletionIntegers D.host.F :=
    fun w => one_mem (w.adicCompletionIntegers D.host.F)
  obtain ⟨g, hg⟩ := hfg
  let O := v.adicCompletionIntegers D.host.F
  let gen : ↥(g : Set (Fin n → D.host.E)) → Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E :=
    fun j i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (j : Fin n → D.host.E) i
  let N : Submodule O (Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) :=
    Submodule.span O (Set.range fun j i => π (gen j i))

  have hL : ∀ a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F, (∀ w, a w ∈ w.adicCompletionIntegers D.host.F) →
      ∀ x ∈ L, (fun i => π (a ⊗ₜ[D.host.F] x i)) ∈ N := by
    intro a ha x hx
    have haE : a ⊗ₜ[D.host.F] (1 : D.host.E) ∈ intAE D :=
      AddSubgroup.subset_closure ⟨a, fun w => ha w, 1, by simp⟩
    rw [← hg] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      have hx' : (fun i => π (a ⊗ₜ[D.host.F] x i)) =
          (⟨π (a ⊗ₜ[D.host.F] (1 : D.host.E)), hπint _ haE⟩ : O) • (fun i => π (gen ⟨x, hx⟩ i)) := by
        funext i
        show π (a ⊗ₜ[D.host.F] x i) = π (a ⊗ₜ[D.host.F] (1 : D.host.E)) * π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x i)
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hx']
      exact N.smul_mem _ (Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩)
    | zero =>
      convert N.zero_mem using 1
      funext i
      simp
    | add x y _ _ hx hy =>
      convert N.add_mem hx hy using 1
      funext i
      simp [TensorProduct.tmul_add]
    | smul c x _ hx =>
      have hc : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E) ∈ intAE D :=
        AddSubgroup.subset_closure ⟨1, hone, c, rfl⟩
      convert N.smul_mem (⟨π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)), hπint _ hc⟩ : O) hx using 1
      funext i
      show π (a ⊗ₜ[D.host.F] ((c : D.host.E) * x i)) = π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) * π (a ⊗ₜ[D.host.F] x i)
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hz : ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)), (fun i => π (z i)) ∈ N := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      exact hL a ha x hx
    | zero =>
      convert N.zero_mem using 1
      funext i
      simp
    | add z₁ z₂ _ _ h₁ h₂ =>
      convert N.add_mem h₁ h₂ using 1
      funext i
      simp
    | neg z _ h =>
      convert N.neg_mem h using 1
      funext i
      simp
  have hgen : ∀ j, gen j ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) := fun j =>
    AddSubgroup.subset_closure ⟨1, hone, j, hg ▸ Submodule.subset_span j.2, rfl⟩
  have hiff : ∀ y : Fin n → GlobalTheory.SplitPlace.RF D,
      finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) ↔ (fun j => π (y j)) ∈ N := by
    intro y
    constructor
    · intro hy
      convert hz _ hy using 1
      funext j
      show π (y j) = π (finPart D e * y j)
      rw [map_mul, hπ1, one_mul]
    · intro hy
      have hs := GlobalTheory.SplitLatBasis.section_mem O π (fun a => finPart D (s a)) (finPart D e) (intAE D)
        (GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E))) h1 h2 (fun x hx => (h3 x).2 hx)
        (fun a ha y hy => smul_mem_hat D L ha hy) gen hgen _ hy
      convert hs using 1
      funext j
      exact (h2 (y j)).symm
  have hfin : N.FG := Submodule.fg_span (Set.finite_range _)
  have htop : Submodule.span (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)
      (N : Set (Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)) = ⊤ := by
    set S := Submodule.span (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) (N : Set (Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v))
    have hΦ : ∀ x ∈ Submodule.span D.host.E (L : Set (Fin n → D.host.E)),
        (fun i => π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x i)) ∈ S := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (hL 1 hone x hx)
      | zero =>
        convert S.zero_mem using 1
        funext i
        simp
      | add x y _ _ hx hy =>
        convert S.add_mem hx hy using 1
        funext i
        simp [TensorProduct.tmul_add]
      | smul c x _ hx =>
        convert S.smul_mem (π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] c)) hx using 1
        funext i
        show π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (c * x i)) = π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] c) * π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x i)
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [Submodule.eq_top_iff']
    intro w
    rw [pi_eq_sum_univ w]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    convert hΦ (fun j => if i = j then 1 else 0) (by rw [hspan]; trivial) using 1
    funext j
    split_ifs
    · rw [← Algebra.TensorProduct.one_def, map_one]
    · rw [TensorProduct.tmul_zero, map_zero]
  haveI : Submodule.IsLattice (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) N := ⟨hfin, htop⟩
  obtain ⟨B, hB⟩ := GlobalTheory.SplitLatBasis.exists_matrix_of_isLattice (R := O) N
  refine ⟨B, fun y => (hiff y).trans ((hB _).trans (forall_congr' fun i => ?_))⟩
  constructor
  · rintro ⟨r, hr⟩
    rw [← hr]
    exact r.2
  · intro h
    exact ⟨⟨_, h⟩, rfl⟩

end GlobalTheory.HatLocalChart
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField
open IsDedekindDomain Formalism.L2.NTheta
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_matrix_chart_split_idempotent_completion : ∀ (D : D7) (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (π : GlobalTheory.SplitPlace.RF D →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v → AE D) (n : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), e * e = e →
    (∀ a, π (finPart D (s a)) = a) → (∀ x, finPart D (s (π x)) = finPart D e * x) →
    (∀ x, finPart D e * x ∈ intAE D ↔ π x ∈ Formalism.UG.Ov D.host.F v) →
    L.FG → Submodule.span D.host.E (L : Set (Fin n → D.host.E)) = ⊤ →
    ∃ C : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v), ∀ y : Fin n → GlobalTheory.SplitPlace.RF D,
      finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) ↔
        ∀ i, ((C⁻¹ : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1 *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v := by
  atlas_forward_decl GlobalTheory.HatLocalChart.exists_chart
end
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField
open IsDedekindDomain Formalism.L2.NTheta
open scoped Matrix

open scoped TensorProduct

namespace GlobalTheory.EPartChart

open IsDedekindDomain Formalism.L2.NTheta

theorem int_smul_mem_hat (D : D7) {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    {a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (ha : a ∈ intAE D)
    {y : Fin n → GlobalTheory.AdLat.RA D.host.F D.host.E} (hy : y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E))) :
    a • y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) := by
  induction ha using AddSubgroup.closure_induction generalizing y with
  | mem w hw =>
    obtain ⟨b, hb, x, rfl⟩ := hw
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨c, hc, m, hm, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨b * c, fun v => ?_, x • m, L.smul_mem x hm, ?_⟩
      · exact mul_mem (hb v) (hc v)
      · funext i
        simp [Algebra.TensorProduct.tmul_mul_tmul]
        rfl
    | zero => rw [smul_zero]; exact zero_mem _
    | add z z' _ _ h h' => rw [smul_add]; exact add_mem h h'
    | neg z _ h => rw [smul_neg]; exact neg_mem h
  | zero => rw [zero_smul]; exact zero_mem _
  | add a b _ _ h h' => rw [add_smul]; exact add_mem (h hy) (h' hy)
  | neg a _ h => rw [neg_smul]; exact neg_mem (h hy)

theorem mem_Ov_iff {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :
    t ∈ Formalism.UG.Ov F v ↔ Valued.v t ≤ 1 := Iff.rfl

theorem exists_local_gen {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} (φ : E →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)
    (hφ : ∀ o : 𝓞 E, φ (o : E) ∈ Formalism.UG.Ov F v) (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) :
    ∃ α ∈ I, α ≠ 0 ∧ ∀ a ∈ I, φ a * (φ α)⁻¹ ∈ Formalism.UG.Ov F v := by
  classical
  obtain ⟨S, hS⟩ := FractionalIdeal.fg_of_isNoetherianRing le_rfl I
  have hSI : ∀ a ∈ S, a ∈ I := fun a ha => by
    rw [← FractionalIdeal.mem_coe, ← hS]; exact Submodule.subset_span ha
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hI
    rw [← FractionalIdeal.coeToSubmodule_inj, ← hS, Finset.coe_empty, Submodule.span_empty]
    simp
  obtain ⟨α, hαS, hmax⟩ := Finset.exists_max_image S (fun a => Valued.v (φ a)) hne
  have hα0 : α ≠ 0 := by
    rintro rfl
    apply hI
    rw [← FractionalIdeal.coeToSubmodule_inj, ← hS, FractionalIdeal.coe_zero, eq_bot_iff, Submodule.span_le]
    intro a ha
    have h1 := hmax a ha
    rw [map_zero, Valuation.map_zero, le_zero_iff, Valuation.zero_iff, map_eq_zero_iff φ φ.injective] at h1
    simp [h1]
  refine ⟨α, hSI α hαS, hα0, fun a ha => ?_⟩
  rw [← FractionalIdeal.mem_coe, ← hS] at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    rw [mem_Ov_iff, Valuation.map_mul, map_inv₀]
    exact mul_inv_le_one_of_le₀ (hmax a ha) zero_le'
  | zero => rw [map_zero, zero_mul]; exact zero_mem _
  | add a b _ _ h h' => rw [map_add, add_mul]; exact add_mem h h'
  | smul o a _ h =>
    rw [Algebra.smul_def, map_mul, mul_assoc]
    exact mul_mem (hφ o) h

theorem tmul_vec_mul {D : D7} {n : ℕ} (b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (a : D.host.E) (c : Fin n → D.host.E) :
    (fun i => b ⊗ₜ[D.host.F] (a • c) i) = finPart D (incA D a) • (fun i => b ⊗ₜ[D.host.F] c i) := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  change _ = ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] a) * _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem smul_hat_latG_one {D : D7} (V : HSp D) {c : GlobalTheory.SplitPlace.RF D}
    (hc : ∀ a ∈ D.host.AA, c * finPart D (incA D a) ∈ intAE D) :
    ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (latG V 1 : Set (Fin V.rank → D.host.E)),
      c • z ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
  obtain ⟨-, -, -, -, -, h6c⟩ := GlobalTheory.Member.latG_lattice_and_completion D V 1
  have hoi : ∀ o : 𝓞 D.host.E, finPart D (incA D (o : D.host.E)) ∈ intAE D := fun o =>
    AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, o, rfl⟩
  intro z hz
  unfold GlobalTheory.AdLat.hat at hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, x, hx, rfl⟩ := hz
    rw [SetLike.mem_coe, h6c] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, c', hc', rfl⟩ := hx
      rw [tmul_vec_mul, smul_smul]
      exact int_smul_mem_hat D _ (hc a ha) (AddSubgroup.subset_closure ⟨b, hb, c', hc', rfl⟩)
    | zero =>
      have : (fun i => b ⊗ₜ[D.host.F] (0 : Fin V.rank → D.host.E) i) = 0 := by
        funext i; simp
      rw [this, smul_zero]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : (fun i => b ⊗ₜ[D.host.F] (x + y) i) =
          (fun i => b ⊗ₜ[D.host.F] x i) + (fun i => b ⊗ₜ[D.host.F] y i) := by
        funext i; simp [TensorProduct.tmul_add]
      rw [this, smul_add]; exact add_mem hx hy
    | smul o x _ hx =>
      have : (fun i => b ⊗ₜ[D.host.F] (o • x) i) = (fun i => b ⊗ₜ[D.host.F] ((o : D.host.E) • x) i) := rfl
      rw [this, tmul_vec_mul, smul_comm]
      exact int_smul_mem_hat D _ (hoi o) hx
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem smul_hat_latC {D : D7} (V : HSp D) {α : D.host.E} (hα : α ∈ D.host.AA)
    {z : Fin V.rank → GlobalTheory.SplitPlace.RF D}
    (hz : z ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))) :
    finPart D (incA D α) • z ∈ GlobalTheory.AdLat.hat D.host.F (latG V 1 : Set (Fin V.rank → D.host.E)) := by
  obtain ⟨-, -, -, -, -, h6c⟩ := GlobalTheory.Member.latG_lattice_and_completion D V 1
  have hs : ∀ x ∈ (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)),
      α • x ∈ (latG V 1 : Set (Fin V.rank → D.host.E)) := by
    intro x hx
    rw [SetLike.mem_coe, h6c]
    exact Submodule.subset_span ⟨α, hα, x, hx, rfl⟩
  exact GlobalTheory.AdLat.Scale.smul_mem_hat hs hz

theorem mem_latGHat_iff {D : D7} (V : HSp D) (x : GA D V) (ef : GlobalTheory.SplitPlace.RF D) (y : Fin V.rank → GlobalTheory.SplitPlace.RF D) :
    ef • y ∈ latGHat V x ↔
      ef • (GlobalTheory.SplitPlace.fm V x⁻¹ *ᵥ y) ∈ GlobalTheory.AdLat.hat D.host.F (latG V 1 : Set (Fin V.rank → D.host.E)) := by
  obtain ⟨-, -, -, h4x, -, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V x
  rw [← SetLike.mem_coe, h4x]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have : ef • (GlobalTheory.SplitPlace.fm V x⁻¹ *ᵥ y) = z := by
      rw [← Matrix.mulVec_smul, ← hzy]
      exact GlobalTheory.SplitPlace.fm_inv_vec V x z
    rwa [this]
  · intro h
    refine ⟨_, h, ?_⟩
    change GlobalTheory.SplitPlace.fm V x *ᵥ _ = _
    rw [Matrix.mulVec_smul, GlobalTheory.SplitPlace.fm_vec_inv]

end GlobalTheory.EPartChart

namespace GlobalTheory.EPartChart

open IsDedekindDomain Formalism.L2.NTheta

theorem chart_coord {D : D7} {V : HSp D} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (π : GlobalTheory.SplitPlace.RF D →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) (B : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v))
    (τ : GlobalTheory.SplitPlace.RF D) (x : GA D V) (y : Fin V.rank → GlobalTheory.SplitPlace.RF D) :
    (B⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1 *ᵥ (fun j => π ((τ • GlobalTheory.SplitPlace.fm V x⁻¹ *ᵥ y) j)) =
      (π τ • ((GlobalTheory.SplitPlace.comp V π B x⁻¹).1 * (B⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1)) *ᵥ
        fun j => π (y j) := by
  rw [GlobalTheory.SplitPlace.map_mulVec (π := π) (GlobalTheory.SplitPlace.fm V x⁻¹) τ y]
  have hM : (GlobalTheory.SplitPlace.comp V π B x⁻¹).1 * (B⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1 =
      (B⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1 * (GlobalTheory.SplitPlace.fm V x⁻¹).map π := by
    rw [GlobalTheory.SplitPlace.comp_val, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [hM, Matrix.smul_mulVec, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec]

theorem smul_eq_idem {R : Type} [CommRing R] {n : ℕ} (e τ : R) (he : e * e = e) (w : Fin n → R) :
    e • (τ • w) = (e * τ) • (e • w) := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination (-(τ * w i)) * he

theorem smul_eq_inv {R : Type} [CommRing R] {n : ℕ} (a τ e : R) (h : a * τ = 1) (w : Fin n → R) :
    e • w = a • (e • (τ • w)) := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination (-(e * w i)) * h

set_option maxHeartbeats 1000000 in

theorem latGHat_chart : ∀ (D : D7) (V : HSp D) (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (π : GlobalTheory.SplitPlace.RF D →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v → AE D)
    (B : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)), e * e = e →
    (∀ a, π (finPart D (s a)) = a) → (∀ x, finPart D (s (π x)) = finPart D e * x) →
    (∀ x, finPart D e * x ∈ intAE D ↔ π x ∈ Formalism.UG.Ov D.host.F v) →
    (∀ y : Fin V.rank → GlobalTheory.SplitPlace.RF D, (fun i => finPart D e * y i) ∈ LamHat V ↔
      ∀ i, ((B⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1 *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v) →
    ∃ t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v, t ≠ 0 ∧ ∀ (x : GA D V) (y : Fin V.rank → GlobalTheory.SplitPlace.RF D),
      finPart D e • y ∈ latGHat V x ↔
        ∀ i, ((t • ((GlobalTheory.SplitPlace.comp V π B x⁻¹).1 * (B⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1)) *ᵥ
          fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v := by
  intro D V e v π s B he h2 h3 h4 hB
  have hee : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he]
  have hei : finPart D e ∈ intAE D := GlobalTheory.SplitPlace.idem_mem he
  have hoi : ∀ o : 𝓞 D.host.E, finPart D (incA D (o : D.host.E)) ∈ intAE D := fun o =>
    AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, o, rfl⟩
  have hφo : ∀ o : 𝓞 D.host.E, ((π.comp (finPart D)).comp (incA D)) (o : D.host.E) ∈ Formalism.UG.Ov D.host.F v :=
    fun o => (h4 _).1 (GlobalTheory.HeckeConj.mul_mem_intAE D hei (hoi o))
  obtain ⟨α, hαA, hα0, hαg⟩ := exists_local_gen ((π.comp (finPart D)).comp (incA D)) hφo D.host.AA
    (AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D)
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = finPart D (incA D α⁻¹) := ⟨_, rfl⟩
  have hατ : finPart D (incA D α) * τ = 1 := by
    rw [hτ, ← map_mul, ← map_mul, mul_inv_cancel₀ hα0, map_one, map_one]
  have hsc : ∀ a ∈ D.host.AA, finPart D e * τ * finPart D (incA D a) ∈ intAE D := by
    intro a ha
    rw [mul_assoc]
    refine (h4 _).2 ?_
    have e1 : τ * finPart D (incA D a) = finPart D (incA D (a * α⁻¹)) := by
      rw [hτ, ← map_mul, ← map_mul, mul_comm]
    rw [e1]
    have h : ((π.comp (finPart D)).comp (incA D)) (a * α⁻¹) ∈ Formalism.UG.Ov D.host.F v := by
      rw [map_mul, map_inv₀]; exact hαg a ha
    exact h
  have key : ∀ w : Fin V.rank → GlobalTheory.SplitPlace.RF D,
      finPart D e • w ∈ GlobalTheory.AdLat.hat D.host.F (latG V 1 : Set (Fin V.rank → D.host.E)) ↔
        finPart D e • (τ • w) ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
    intro w
    constructor
    · intro h
      rw [smul_eq_idem _ τ hee w]
      exact smul_hat_latG_one V hsc _ h
    · intro h
      rw [smul_eq_inv _ τ (finPart D e) hατ w]
      exact smul_hat_latC V hαA h
  refine ⟨π τ, right_ne_zero_of_mul_eq_one (a := π (finPart D (incA D α))) (by rw [← map_mul, hατ, map_one]),
    fun x y => ?_⟩
  rw [mem_latGHat_iff, key, ← SetLike.mem_coe, ← GlobalTheory.LatDual.lamHat_eq_hat V, SetLike.mem_coe]
  refine (hB (τ • GlobalTheory.SplitPlace.fm V x⁻¹ *ᵥ y)).trans ?_
  rw [chart_coord]

end GlobalTheory.EPartChart
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField
open IsDedekindDomain Formalism.L2.NTheta
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_part_completed_lattice_local_chart : ∀ (D : D7) (V : HSp D) (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (π : GlobalTheory.SplitPlace.RF D →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v → AE D)
    (B : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)), e * e = e →
    (∀ a, π (finPart D (s a)) = a) → (∀ x, finPart D (s (π x)) = finPart D e * x) →
    (∀ x, finPart D e * x ∈ intAE D ↔ π x ∈ Formalism.UG.Ov D.host.F v) →
    (∀ y : Fin V.rank → GlobalTheory.SplitPlace.RF D, (fun i => finPart D e * y i) ∈ LamHat V ↔
      ∀ i, ((B⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1 *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v) →
    ∃ t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v, t ≠ 0 ∧ ∀ (x : GA D V) (y : Fin V.rank → GlobalTheory.SplitPlace.RF D),
      finPart D e • y ∈ latGHat V x ↔
        ∀ i, ((t • ((GlobalTheory.SplitPlace.comp V π B x⁻¹).1 * (B⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1)) *ᵥ
          fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v := by
  atlas_forward_decl GlobalTheory.EPartChart.latGHat_chart
end
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField
open IsDedekindDomain Formalism.L2.NTheta
open scoped Matrix

namespace GlobalTheory.HeckeLocMatrix

open Formalism.L2.Theta
open scoped TensorProduct

theorem relIndex_eq_index_of_reading {G H : Type} [AddCommGroup G] [AddCommGroup H] {Λ M : AddSubgroup G}
    (Ψ : Λ →+ H) (R : AddSubgroup H) (hmem : ∀ x : Λ, (x : G) ∈ M ↔ Ψ x ∈ R)
    (hsurj : ∀ b : H, ∃ x : Λ, b - Ψ x ∈ R) : M.relIndex Λ = R.index := by
  have h1 : M.addSubgroupOf Λ = R.comap Ψ := by
    ext x
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap, hmem]
  have h2 : Ψ.range ⊔ R = ⊤ := by
    rw [eq_top_iff]
    intro b _
    obtain ⟨x, hx⟩ := hsurj b
    have : b = Ψ x + (b - Ψ x) := by abel
    rw [this]
    exact add_mem (AddSubgroup.mem_sup_left ⟨x, rfl⟩) (AddSubgroup.mem_sup_right hx)
  rw [AddSubgroup.relIndex, h1, AddSubgroup.index_comap, ← AddSubgroup.relIndex_sup_right, h2,
    AddSubgroup.relIndex_top_right]

theorem mulVec_mem {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) (v.adicCompletion F)} (hA : ∀ i j, A i j ∈ Formalism.UG.Ov F v)
    {c : Fin n → v.adicCompletion F} (hc : ∀ j, c j ∈ Formalism.UG.Ov F v) (i : Fin n) :
    (A *ᵥ c) i ∈ Formalism.UG.Ov F v :=
  sum_mem fun j _ => mul_mem (hA i j) (hc j)

def intMat {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}
    (Z : GL (Fin n) (v.adicCompletion F)) (hZ : ∀ i j, Z.1 i j ∈ Formalism.UG.Ov F v) :
    Matrix (Fin n) (Fin n) (Formalism.UG.Ov F v) :=
  Matrix.of fun i j => ⟨Z.1 i j, hZ i j⟩

theorem intMat_map {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}
    (Z : GL (Fin n) (v.adicCompletion F)) (hZ : ∀ i j, Z.1 i j ∈ Formalism.UG.Ov F v) :
    (intMat Z hZ).map (Formalism.UG.Ov F v).subtype = Z.1 := by
  ext i j; rfl

theorem mem_range_iff {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}
    (Z : GL (Fin n) (v.adicCompletion F)) (hZ : ∀ i j, Z.1 i j ∈ Formalism.UG.Ov F v) (b : Fin n → Formalism.UG.Ov F v) :
    b ∈ LinearMap.range (Matrix.toLin' (intMat Z hZ)) ↔
      ∀ i, ((Z⁻¹).1 *ᵥ fun j => (b j : v.adicCompletion F)) i ∈ Formalism.UG.Ov F v := by
  have key : ∀ c : Fin n → Formalism.UG.Ov F v, (fun i => ((intMat Z hZ *ᵥ c) i : v.adicCompletion F)) =
      Z.1 *ᵥ fun j => (c j : v.adicCompletion F) := by
    intro c
    funext i
    have := RingHom.map_mulVec (Formalism.UG.Ov F v).subtype (intMat Z hZ) c i
    rw [intMat_map] at this
    exact this
  constructor
  · rintro ⟨c, rfl⟩ i
    rw [Matrix.toLin'_apply, key, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact (c i).2
  · intro h
    refine ⟨fun i => ⟨_, h i⟩, ?_⟩
    rw [Matrix.toLin'_apply]
    funext i
    apply Subtype.ext
    have := congrFun (key fun i => ⟨_, h i⟩) i
    rw [this]
    change (Z.1 *ᵥ ((Z⁻¹).1 *ᵥ fun j => (b j : v.adicCompletion F))) i = b i
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

theorem exists_index_pow {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}
    (Z : GL (Fin n) (v.adicCompletion F)) (hZ : ∀ i j, Z.1 i j ∈ Formalism.UG.Ov F v) {w : v.adicCompletion F}
    (hw : Formalism.UG.IsUnifV F v w) :
    ∃ m : ℕ, Valued.v Z.1.det = Valued.v w ^ m ∧
      (LinearMap.range (Matrix.toLin' (intMat Z hZ))).toAddSubgroup.index =
        Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) ^ m := by
  have hwO := (GlobalTheory.SplitPlace.unif_facts hw).2
  have hirr := Formalism.IndefR.Fin.HCount.irreducible_of_unif F v ⟨w, hwO⟩ hw
  have hdet : (((intMat Z hZ).det : Formalism.UG.Ov F v) : v.adicCompletion F) = Z.1.det := by
    have := RingHom.map_det (Formalism.UG.Ov F v).subtype (intMat Z hZ)
    rw [RingHom.mapMatrix_apply, intMat_map] at this
    exact this
  have hne : (intMat Z hZ).det ≠ 0 := by
    intro h
    rw [h] at hdet
    exact (Matrix.isUnits_det_units Z).ne_zero (by rw [← hdet]; rfl)
  have hinj : Function.Injective (Matrix.toLin' (intMat Z hZ)) := by
    rw [← LinearMap.ker_eq_bot, Matrix.ker_toLin'_eq_bot_iff]
    intro c hc
    exact Matrix.eq_zero_of_mulVec_eq_zero hne hc
  obtain ⟨m, ⟨u, hu⟩, hc⟩ := GlobalTheory.HL.LatDet.card_coker (Pi.basisFun (Formalism.UG.Ov F v) (Fin n)) hirr _ hinj
  rw [LinearMap.det_toLin'] at hu
  refine ⟨m, ?_, ?_⟩
  · have h1 := congrArg (fun x : Formalism.UG.Ov F v => Valued.v (x : v.adicCompletion F)) hu
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, hdet, map_mul, map_pow] at h1
    have ha : Valued.v (((u : Formalism.UG.Ov F v)) : v.adicCompletion F) ≤ 1 := (u : Formalism.UG.Ov F v).2
    have hb : Valued.v (((u⁻¹ : (Formalism.UG.Ov F v)ˣ) : Formalism.UG.Ov F v) : v.adicCompletion F) ≤ 1 :=
      ((u⁻¹ : (Formalism.UG.Ov F v)ˣ) : Formalism.UG.Ov F v).2
    have hm : (((u : Formalism.UG.Ov F v)) : v.adicCompletion F) *
        (((u⁻¹ : (Formalism.UG.Ov F v)ˣ) : Formalism.UG.Ov F v) : v.adicCompletion F) = 1 := by
      rw [← MulMemClass.coe_mul, Units.mul_inv]; rfl
    have hv := congrArg Valued.v hm
    rw [map_mul, map_one] at hv
    have hu1 : Valued.v (((u : Formalism.UG.Ov F v)) : v.adicCompletion F) = 1 :=
      le_antisymm ha (by rw [← hv]; exact mul_le_of_le_one_right' hb)
    rw [hu1, mul_one] at h1
    exact h1
  · rw [← hirr.maximalIdeal_eq] at hc
    exact hc

theorem smul_mem_hat (D : D7) {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    {a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (ha : a ∈ intAE D)
    {y : Fin n → GlobalTheory.AdLat.RA D.host.F D.host.E} (hy : y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E))) :
    a • y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) := by
  induction ha using AddSubgroup.closure_induction generalizing y with
  | mem w hw =>
    obtain ⟨b, hb, x, rfl⟩ := hw
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨c, hc, m, hm, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨b * c, fun v => ?_, x • m, L.smul_mem x hm, ?_⟩
      · exact mul_mem (hb v) (hc v)
      · funext i
        simp [Algebra.TensorProduct.tmul_mul_tmul]
        rfl
    | zero => rw [smul_zero]; exact zero_mem _
    | add z z' _ _ h h' => rw [smul_add]; exact add_mem h h'
    | neg z _ h => rw [smul_neg]; exact neg_mem h
  | zero => rw [zero_smul]; exact zero_mem _
  | add a b _ _ h h' => rw [add_smul]; exact add_mem (h hy) (h' hy)
  | neg a _ h => rw [neg_smul]; exact neg_mem (h hy)

theorem span_smul_top {D : D7} {n : ℕ} (P : Formalism.L2.DIV.Pl D.host.E) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hL : Submodule.span D.host.E (L : Set (Fin n → D.host.E)) = ⊤) :
    Submodule.span D.host.E ((P.asIdeal • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = ⊤ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  have hx0' : ((x : D.host.E)) ≠ 0 := fun h => hx0 (RingOfIntegers.ext h)
  rw [eq_top_iff, ← hL, Submodule.span_le]
  intro w hw
  have hm : x • w ∈ (P.asIdeal • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) := Submodule.smul_mem_smul hx hw
  have : w = (x : D.host.E)⁻¹ • (x • w) := by
    rw [← algebraMap_smul D.host.E x w]
    rw [smul_smul, inv_mul_cancel₀ (by simpa using hx0'), one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

theorem mem_iff_ePart (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) {n : ℕ}
    (Λ M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (he : IsIdemAt e P) (hfg : Λ.FG)
    (hsp : Submodule.span D.host.E (Λ : Set (Fin n → D.host.E)) = ⊤)
    (hPM : P.asIdeal • Λ ≤ M) (hMΛ : M ≤ Λ) (x : Fin n → D.host.E) (hx : x ∈ Λ) :
    x ∈ M ↔ finPart D e • (GlobalTheory.AdLat.fv D.host.F x : Fin n → GlobalTheory.SplitPlace.RF D) ∈
      GlobalTheory.AdLat.hat D.host.F (M : Set (Fin n → D.host.E)) := by
  have hMfg : M.FG := by
    have hN : IsNoetherian (𝓞 D.host.E) Λ := isNoetherian_of_fg_of_noetherian _ hfg
    have hc := (IsNoetherian.noetherian (M.comap Λ.subtype)).map Λ.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hMΛ] at hc
  have hMsp : Submodule.span D.host.E (M : Set (Fin n → D.host.E)) = ⊤ :=
    eq_top_iff.2 ((span_smul_top P _ hsp).symm.le.trans (Submodule.span_mono hPM))
  have hrat := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E n M hMfg hMsp).1
  have hint : finPart D e ∈ intAE D := GlobalTheory.SplitPlace.idem_mem he.1.1
  constructor
  · intro hm
    exact smul_mem_hat D M hint ((hrat x).2 hm)
  · intro h
    refine (hrat x).1 ?_
    have hΛ : GlobalTheory.AdLat.fv D.host.F x ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) :=
      ((GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E n Λ hfg hsp).1 x).2 hx
    have hmono : GlobalTheory.AdLat.hat D.host.F ((P.asIdeal • Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
        Set (Fin n → D.host.E)) ≤ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin n → D.host.E)) := by
      refine AddSubgroup.closure_mono ?_
      rintro _ ⟨a, ha, y, hy, rfl⟩
      exact ⟨a, ha, y, hPM hy, rfl⟩
    have h3 := hmono (GlobalTheory.ComplOffPlace.one_sub_smul_mem D P e n Λ he _ hΛ)
    have hsplit : GlobalTheory.AdLat.fv D.host.F x = finPart D e • (GlobalTheory.AdLat.fv D.host.F x : Fin n → GlobalTheory.SplitPlace.RF D) +
        (1 - finPart D e) • (GlobalTheory.AdLat.fv D.host.F x : Fin n → GlobalTheory.SplitPlace.RF D) := by
      rw [← add_smul, add_sub_cancel, one_smul]
    rw [hsplit]
    exact add_mem h h3

set_option maxHeartbeats 10000000 in

theorem exists_local_matrix : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (k n : ℕ)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (π : GlobalTheory.SplitPlace.RF D →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)
    (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v → AE D)
    (Λ M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)
    (T C : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)),
    IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    (∀ x, s (π (finPart D x)) = e * x) → (∀ a, π (finPart D (s a)) = a) →
    (∀ x, finPart D (s (π x)) = finPart D e * x) →
    (∀ x, finPart D e * x ∈ intAE D ↔ π x ∈ Formalism.UG.Ov D.host.F v) →
    (∀ x : D.host.F, π (finPart D (incA D (algebraMap D.host.F D.host.E x))) =
      algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) x) →
    Λ.FG → Submodule.span D.host.E (Λ : Set (Fin n → D.host.E)) = ⊤ →
    P.asIdeal • Λ ≤ M → M ≤ Λ → M.toAddSubgroup.relIndex Λ.toAddSubgroup = Ideal.absNorm P.asIdeal ^ k →
    t ≠ 0 →
    (∀ y : Fin n → GlobalTheory.SplitPlace.RF D, finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) ↔
      ∀ i, ((t • T.1) *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v) →
    (∀ y : Fin n → GlobalTheory.SplitPlace.RF D, finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin n → D.host.E)) ↔
      ∀ i, ((C⁻¹ : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1 *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v) →
    ∃ Z : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v), (∀ i j, Z.1 i j ∈ Formalism.UG.Ov D.host.F v) ∧
      (∀ i j, π (finPart D (incA D (ϖ : D.host.E))) * (Z⁻¹).1 i j ∈ Formalism.UG.Ov D.host.F v) ∧
      Valued.v Z.1.det = Valued.v (π (finPart D (incA D (ϖ : D.host.E)))) ^ k ∧
      ∀ y : Fin n → GlobalTheory.SplitPlace.RF D, (finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin n → D.host.E)) ↔
        ∀ i, (((Z⁻¹).1 * (t • T.1)) *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v) := by
  intro D P e ϖ k n v π s Λ M t T C he h1 h2 hs1 hs2 hs3 h4 h5 hΛfg hΛsp hPM hMΛ hidx ht hΛ hM
  set w := π (finPart D (incA D (ϖ : D.host.E))) with hw
  have hu := GlobalTheory.SplitPlace.isUnif he h4 h5 ϖ h1 h2
  obtain ⟨hw0, hwO⟩ := GlobalTheory.SplitPlace.unif_facts hu
  have hπe : π (finPart D e) = 1 := by
    have := congrArg π (hs3 1)
    rwa [hs2, mul_one, map_one, eq_comm] at this
  have hmono : GlobalTheory.AdLat.hat D.host.F (M : Set (Fin n → D.host.E)) ≤ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) := by
    refine AddSubgroup.closure_mono ?_
    rintro _ ⟨a, ha, x, hx, rfl⟩
    exact ⟨a, ha, x, hMΛ hx, rfl⟩
  let Z : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) :=
    ⟨t • T.1 * C.1, t⁻¹ • (C⁻¹).1 * (T⁻¹).1, by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [inv_mul_cancel₀ ht, one_smul, mul_assoc, ← mul_assoc C.1, Units.mul_inv, one_mul, Units.mul_inv], by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [mul_inv_cancel₀ ht, one_smul, mul_assoc, ← mul_assoc (T⁻¹).1, Units.inv_mul, one_mul, Units.inv_mul]⟩
  have hZ : Z.1 = t • T.1 * C.1 := rfl
  have hZi : (Z⁻¹).1 = t⁻¹ • (C⁻¹).1 * (T⁻¹).1 := rfl
  have hZC : (Z⁻¹).1 * (t • T.1) = (C⁻¹).1 := by
    rw [hZi]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [mul_inv_cancel₀ ht, one_smul, mul_assoc, Units.inv_mul, mul_one]
  have hsec : ∀ u : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v, (fun j => π ((fun i => finPart D (s (u i))) j)) = u := by
    intro u; funext j; exact hs2 _
  have hZint : ∀ i j, Z.1 i j ∈ Formalism.UG.Ov D.host.F v := by
    intro i j
    have hy := (hM (fun i => finPart D (s ((C.1 *ᵥ Pi.single j 1) i)))).2 (by
      intro l
      rw [hsec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      rcases eq_or_ne l j with rfl | hl
      · simp only [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne hl]; exact zero_mem _)
    have := (hΛ _).1 (hmono hy) i
    rwa [hsec, Matrix.mulVec_mulVec, ← hZ, Matrix.mulVec_single_one] at this

  have hwZ : ∀ i j, w * (Z⁻¹).1 i j ∈ Formalism.UG.Ov D.host.F v := by
    intro i j
    obtain ⟨u, hu⟩ : ∃ u, u = (t⁻¹ • (T⁻¹).1) *ᵥ (Pi.single j 1 : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) := ⟨_, rfl⟩
    have hTu : (t • T.1) *ᵥ u = Pi.single j 1 := by
      rw [hu, Matrix.mulVec_mulVec]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ ht, mul_inv_cancel₀ ht, one_smul,
        Units.mul_inv, Matrix.one_mulVec]
    have hy := (hΛ (fun i => finPart D (s (u i)))).2 (by
      intro l
      rw [hsec, hTu]
      rcases eq_or_ne l j with rfl | hl
      · simp only [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne hl]; exact zero_mem _)
    have hz := GlobalTheory.AdLat.Scale.smul_mem_hat (F := D.host.F) (L := (Λ : Set (Fin n → D.host.E)))
      (L' := (M : Set (Fin n → D.host.E))) (a := (ϖ : D.host.E)) (fun x hx => by
        have := hPM (Submodule.smul_mem_smul h1 hx)
        have e : (ϖ : D.host.E) • x = ϖ • x := algebraMap_smul D.host.E ϖ x
        rw [SetLike.mem_coe, e]
        exact this) hy
    have hz' : finPart D e • (fun i => finPart D (incA D (ϖ : D.host.E)) * finPart D (s (u i))) ∈
        GlobalTheory.AdLat.hat D.host.F (M : Set (Fin n → D.host.E)) := by
      convert hz using 1
      funext l
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [mul_left_comm]
      rfl
    have e2 : (fun l => π (finPart D (incA D (ϖ : D.host.E)) * finPart D (s (u l)))) = w • u := by
      funext l
      exact (map_mul π _ _).trans (congrArg (fun z => π (finPart D (incA D (ϖ : D.host.E))) * z) (hs2 (u l)))
    have h6 := (hM _).1 hz' i
    beta_reduce at h6
    rw [e2, Matrix.mulVec_smul, hu, Matrix.mulVec_mulVec] at h6
    have e4 : (C⁻¹).1 * (t⁻¹ • (T⁻¹).1) = t⁻¹ • (C⁻¹).1 * (T⁻¹).1 := by
      simp only [Matrix.smul_mul, Matrix.mul_smul]
    have e3 : (Z⁻¹).1 i j = (((C⁻¹).1 * (t⁻¹ • (T⁻¹).1)) *ᵥ (Pi.single j (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v))) i := by
      rw [e4, ← hZi, Matrix.mulVec_single_one]
      rfl
    rw [Pi.smul_apply, smul_eq_mul, ← e3] at h6
    exact h6
  refine ⟨Z, hZint, hwZ, ?_, fun y => by rw [hZC]; exact hM y⟩

  have hint : finPart D e ∈ intAE D := GlobalTheory.SplitPlace.idem_mem he.1.1
  have happ := GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E n Λ hΛfg hΛsp
  obtain ⟨m, hm, hidx'⟩ := exists_index_pow Z hZint hu
  suffices hkm : m = k by rw [hm, hkm]
  let φ : D.host.E →+* v.adicCompletion D.host.F := (π.comp (finPart D)).comp (incA D)
  have hP : ∀ x : 𝓞 D.host.E, x ∈ P.asIdeal ↔ Valued.v (φ x) < 1 := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hx0 : Valued.v (φ x) ≠ 0 := by
        rw [Valuation.ne_zero_iff, map_ne_zero]
        exact fun h => hx (Subtype.ext h)
      rw [he.2 x hx, map_mul, h4]
      show ¬ Valued.v (φ (x : D.host.E)⁻¹) ≤ 1 ↔ _
      rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 hx0)]
  have hq : Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers D.host.F)) = Ideal.absNorm P.asIdeal :=
    GlobalTheory.SplitUnif.card_residueField v φ P h5 hP
  have hfvΛ : ∀ x ∈ Λ, ∀ i, ((t • T.1) *ᵥ fun j => π ((GlobalTheory.AdLat.fv D.host.F x : Fin n → GlobalTheory.SplitPlace.RF D) j)) i ∈
      Formalism.UG.Ov D.host.F v :=
    fun x hx => (hΛ _).1 (smul_mem_hat D Λ hint ((happ.1 x).2 hx))
  have hfv0 : (fun j => π ((GlobalTheory.AdLat.fv D.host.F (0 : Fin n → D.host.E) : Fin n → GlobalTheory.SplitPlace.RF D) j)) = 0 := by
    funext j
    simp only [GlobalTheory.AdLat.fv, Pi.zero_apply, TensorProduct.tmul_zero, map_zero]
  have hfvadd : ∀ x y : Fin n → D.host.E,
      (fun j => π ((GlobalTheory.AdLat.fv D.host.F (x + y) : Fin n → GlobalTheory.SplitPlace.RF D) j)) =
        (fun j => π ((GlobalTheory.AdLat.fv D.host.F x : Fin n → GlobalTheory.SplitPlace.RF D) j)) +
          (fun j => π ((GlobalTheory.AdLat.fv D.host.F y : Fin n → GlobalTheory.SplitPlace.RF D) j)) := by
    intro x y
    funext j
    simp only [GlobalTheory.AdLat.fv, Pi.add_apply, TensorProduct.tmul_add, map_add]
  let Ψ : Λ.toAddSubgroup →+ (Fin n → Formalism.UG.Ov D.host.F v) :=
    { toFun := fun x i => ⟨_, hfvΛ x.1 x.2 i⟩
      map_zero' := by
        funext i
        apply Subtype.ext
        show ((t • T.1) *ᵥ fun j => π ((GlobalTheory.AdLat.fv D.host.F (0 : Fin n → D.host.E) : Fin n → GlobalTheory.SplitPlace.RF D) j)) i = 0
        rw [hfv0, Matrix.mulVec_zero]
        rfl
      map_add' := by
        intro x y
        funext i
        apply Subtype.ext
        show ((t • T.1) *ᵥ fun j => π ((GlobalTheory.AdLat.fv D.host.F (x.1 + y.1) : Fin n → GlobalTheory.SplitPlace.RF D) j)) i = _
        rw [hfvadd, Matrix.mulVec_add]
        rfl }
  have hΨ : ∀ x : Λ.toAddSubgroup, (fun j => ((Ψ x j : Formalism.UG.Ov D.host.F v) : v.adicCompletion D.host.F)) =
      (t • T.1) *ᵥ fun j => π ((GlobalTheory.AdLat.fv D.host.F x.1 : Fin n → GlobalTheory.SplitPlace.RF D) j) := fun x => rfl
  have hmem : ∀ x : Λ.toAddSubgroup, (x : Fin n → D.host.E) ∈ M.toAddSubgroup ↔
      Ψ x ∈ (LinearMap.range (Matrix.toLin' (intMat Z hZint))).toAddSubgroup := by
    intro x
    rw [Submodule.mem_toAddSubgroup, mem_iff_ePart D P e Λ M he hΛfg hΛsp hPM hMΛ x.1 x.2, hM,
      Submodule.mem_toAddSubgroup, mem_range_iff, hΨ, Matrix.mulVec_mulVec, hZC]

  have hN0 : 0 < Ideal.absNorm P.asIdeal :=
    Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hNw : ∃ c ∈ Formalism.UG.Ov D.host.F v, ((Ideal.absNorm P.asIdeal : ℕ) : v.adicCompletion D.host.F) = w * c := by
    have h6 := (hP _).1 (Ideal.absNorm_mem P.asIdeal)
    have h7 : φ ((((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E)) : D.host.E) = ((Ideal.absNorm P.asIdeal : ℕ) : v.adicCompletion D.host.F) := by
      show φ (algebraMap (𝓞 D.host.E) D.host.E ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E)) = _
      rw [map_natCast, map_natCast]
    rw [h7, GlobalTheory.SplitUnif.lt_one_iff] at h6
    refine ⟨((Ideal.absNorm P.asIdeal : ℕ) : v.adicCompletion D.host.F) / w, ?_, by rw [mul_div_cancel₀ _ hw0]⟩
    show Valued.v (((Ideal.absNorm P.asIdeal : ℕ) : v.adicCompletion D.host.F) / w) ≤ 1
    rw [map_div₀]
    refine div_le_one_of_le₀ ?_ zero_le
    rw [hu]
    exact h6
  obtain ⟨c, hc, hcN⟩ := hNw
  have hsurj : ∀ b : Fin n → Formalism.UG.Ov D.host.F v, ∃ x : Λ.toAddSubgroup,
      b - Ψ x ∈ (LinearMap.range (Matrix.toLin' (intMat Z hZint))).toAddSubgroup := by
    intro b
    obtain ⟨u, hud⟩ : ∃ u, u = (t⁻¹ • (T⁻¹).1) *ᵥ (fun j => (b j : v.adicCompletion D.host.F)) := ⟨_, rfl⟩
    have hTu : (t • T.1) *ᵥ u = fun j => (b j : v.adicCompletion D.host.F) := by
      rw [hud, Matrix.mulVec_mulVec]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ ht, mul_inv_cancel₀ ht, one_smul,
        Units.mul_inv, Matrix.one_mulVec]
    have hy := (hΛ (fun i => finPart D (s (u i)))).2 (by
      intro l
      rw [hsec, hTu]
      exact (b l).2)
    obtain ⟨x, hx, z, hz, hdec⟩ := happ.2.1 _ hN0 _ hy
    have hg := (hΛ z).1 (smul_mem_hat D Λ hint hz)
    have hu2 : u = (fun j => π ((GlobalTheory.AdLat.fv D.host.F x : Fin n → GlobalTheory.SplitPlace.RF D) j)) +
        ((Ideal.absNorm P.asIdeal : ℕ) : v.adicCompletion D.host.F) • (fun j => π (z j)) := by
      funext j
      have h8 := congrArg (fun q : Fin n → GlobalTheory.SplitPlace.RF D => π (q j)) hdec
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, map_mul, map_add, map_nsmul, hπe, one_mul, hs2] at h8
      rw [h8, nsmul_eq_mul]
      rfl
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [Submodule.mem_toAddSubgroup, mem_range_iff]
    intro i
    have e5 : (fun j => ((b - Ψ ⟨x, hx⟩) j : v.adicCompletion D.host.F)) =
        ((Ideal.absNorm P.asIdeal : ℕ) : v.adicCompletion D.host.F) •
          ((t • T.1) *ᵥ fun j => π (z j)) := by
      have e6 : (fun j => ((b - Ψ ⟨x, hx⟩) j : v.adicCompletion D.host.F)) =
          (fun j => (b j : v.adicCompletion D.host.F)) - fun j => ((Ψ ⟨x, hx⟩ j : Formalism.UG.Ov D.host.F v) : v.adicCompletion D.host.F) := by
        funext j; rfl
      rw [e6, hΨ, ← hTu, hu2, Matrix.mulVec_add, Matrix.mulVec_smul, add_sub_cancel_left]
    rw [e5, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hcN, Pi.smul_apply, smul_eq_mul, mul_comm w c, mul_assoc]
    refine mul_mem hc ?_
    have e7 : w * (((Z⁻¹).1 * (t • T.1)) *ᵥ fun j => π (z j)) i =
        ((w • (Z⁻¹).1) *ᵥ ((t • T.1) *ᵥ fun j => π (z j))) i := by
      rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec, Pi.smul_apply, smul_eq_mul]
    rw [e7]
    exact mulVec_mem (fun a b => hwZ a b) hg i
  have htr := relIndex_eq_index_of_reading Ψ _ hmem hsurj
  rw [htr, hidx', hq] at hidx
  have h2le : 2 ≤ Ideal.absNorm P.asIdeal := by
    have h9 : Ideal.absNorm P.asIdeal ≠ 1 := fun h => P.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    omega
  exact Nat.pow_right_injective h2le hidx

end GlobalTheory.HeckeLocMatrix
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField
open IsDedekindDomain Formalism.L2.NTheta
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localHeckeMatrix_intermediateLattice : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (k n : ℕ)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (π : GlobalTheory.SplitPlace.RF D →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)
    (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v → AE D)
    (Λ M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)
    (T C : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)),
    IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    (∀ x, s (π (finPart D x)) = e * x) → (∀ a, π (finPart D (s a)) = a) →
    (∀ x, finPart D (s (π x)) = finPart D e * x) →
    (∀ x, finPart D e * x ∈ intAE D ↔ π x ∈ Formalism.UG.Ov D.host.F v) →
    (∀ x : D.host.F, π (finPart D (incA D (algebraMap D.host.F D.host.E x))) =
      algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) x) →
    Λ.FG → Submodule.span D.host.E (Λ : Set (Fin n → D.host.E)) = ⊤ →
    P.asIdeal • Λ ≤ M → M ≤ Λ → M.toAddSubgroup.relIndex Λ.toAddSubgroup = Ideal.absNorm P.asIdeal ^ k →
    t ≠ 0 →
    (∀ y : Fin n → GlobalTheory.SplitPlace.RF D, finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) ↔
      ∀ i, ((t • T.1) *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v) →
    (∀ y : Fin n → GlobalTheory.SplitPlace.RF D, finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin n → D.host.E)) ↔
      ∀ i, ((C⁻¹ : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1 *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v) →
    ∃ Z : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v), (∀ i j, Z.1 i j ∈ Formalism.UG.Ov D.host.F v) ∧
      (∀ i j, π (finPart D (incA D (ϖ : D.host.E))) * (Z⁻¹).1 i j ∈ Formalism.UG.Ov D.host.F v) ∧
      Valued.v Z.1.det = Valued.v (π (finPart D (incA D (ϖ : D.host.E)))) ^ k ∧
      ∀ y : Fin n → GlobalTheory.SplitPlace.RF D, (finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin n → D.host.E)) ↔
        ∀ i, (((Z⁻¹).1 * (t • T.1)) *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v) := by
  atlas_forward_decl GlobalTheory.HeckeLocMatrix.exists_local_matrix
end
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.HeckeLocLift
open IsDedekindDomain Formalism.L2.NTheta
open scoped Matrix

theorem span_smul_top {D : D7} {n : ℕ} (P : Formalism.L2.DIV.Pl D.host.E) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hL : Submodule.span D.host.E (L : Set (Fin n → D.host.E)) = ⊤) :
    Submodule.span D.host.E ((P.asIdeal • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = ⊤ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  have hx0' : ((x : D.host.E)) ≠ 0 := fun h => hx0 (RingOfIntegers.ext h)
  rw [eq_top_iff, ← hL, Submodule.span_le]
  intro w hw
  have hm : x • w ∈ (P.asIdeal • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) := Submodule.smul_mem_smul hx hw
  have : w = (x : D.host.E)⁻¹ • (x • w) := by
    rw [← algebraMap_smul D.host.E x w]
    rw [smul_smul, inv_mul_cancel₀ (by simpa using hx0'), one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

theorem exists_hecke_ePart : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (k : ℕ) (g : GA D V)
    (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    P.asIdeal • latG V g ≤ M → M ≤ latG V g →
    M.toAddSubgroup.relIndex (latG V g).toAddSubgroup = Ideal.absNorm P.asIdeal ^ k →
    ∃ a₀ : GA D V, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k a₀ ∧ ∀ v ∈ latG V g,
      (finPart D e • finVec V v ∈ latGHat V (g * a₀) ↔
        finPart D e • finVec V v ∈ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin V.rank → D.host.E))) := by
  intro D V P e ϖ k g M he hϖ1 hϖ2 hPM hMΛ hidx
  obtain ⟨v, π, s, h1, h2, h3, h4, h5⟩ := GlobalTheory.SplitCoord.exists_coord e he.1
  obtain ⟨B, hB⟩ := GlobalTheory.SplitLatBasis.exists_basis V e v π s he.1.1 h2 h3 h4
    (GlobalTheory.LatDual.lamHat_selfDual_and_module V).2
  obtain ⟨t, ht, hch⟩ := GlobalTheory.T.idempotent_part_completed_lattice_local_chart D V e v π s B he.1.1 h2 h3 h4 hB
  obtain ⟨hfg, hsp, -, -, hhat, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V g
  have hMfg : M.FG := by
    have hN : IsNoetherian (𝓞 D.host.E) (latG V g) := isNoetherian_of_fg_of_noetherian _ hfg
    have hc := (IsNoetherian.noetherian (M.comap (latG V g).subtype)).map (latG V g).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hMΛ] at hc
  have hMsp : Submodule.span D.host.E (M : Set (Fin V.rank → D.host.E)) = ⊤ :=
    eq_top_iff.2 ((span_smul_top P _ hsp).symm.le.trans (Submodule.span_mono hPM))
  obtain ⟨C, hC⟩ := GlobalTheory.T.exists_local_matrix_chart_split_idempotent_completion D e v π s V.rank M he.1.1 h2 h3 h4 hMfg hMsp
  have hT : ∀ y : Fin V.rank → GlobalTheory.SplitPlace.RF D,
      finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (latG V g : Set (Fin V.rank → D.host.E)) ↔
      ∀ i, ((t • (GlobalTheory.SplitPlace.comp V π B g⁻¹ * B⁻¹).1) *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v := by
    intro y
    rw [← hhat, Units.val_mul]
    exact hch g y
  obtain ⟨Z, hZ1, hZ2, hZ3, hZM⟩ := GlobalTheory.T.exists_localHeckeMatrix_intermediateLattice D P e ϖ k V.rank v π s (latG V g) M t _ C he hϖ1 hϖ2
    h1 h2 h3 h4 h5 hfg hsp hPM hMΛ hidx ht hT hC
  obtain ⟨a₀, hsupp, hcomp⟩ := (GlobalTheory.SplitPlace.comp_bij (V := V) (B := B) he.1 h1 h2).1 Z
  have hu := GlobalTheory.SplitPlace.isUnif he h4 h5 ϖ hϖ1 hϖ2
  have hϖ0 := (GlobalTheory.SplitPlace.unif_facts hu).1
  refine ⟨a₀, (GlobalTheory.SplitPlace.hecke_iff he.1 h1 h2 h3 h4 hB hϖ0 k a₀).2 ⟨hsupp, ?_, ?_, ?_⟩, fun w _ => ?_⟩
  · rw [hcomp]; exact hZ1
  · rw [hcomp]; exact hZ2
  · rw [hcomp]; exact hZ3
  · rw [hch, hZM]
    have : (GlobalTheory.SplitPlace.comp V π B (g * a₀)⁻¹).1 = (Z⁻¹).1 * (GlobalTheory.SplitPlace.comp V π B g⁻¹).1 := by
      rw [mul_inv_rev, map_mul, map_inv, hcomp, Units.val_mul]
    rw [this, Units.val_mul, Matrix.mul_assoc, Matrix.mul_smul]

end GlobalTheory.HeckeLocLift
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeElement_idempotentPart_splitPlace_lattice : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (k : ℕ) (g : GA D V)
    (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    P.asIdeal • latG V g ≤ M → M ≤ latG V g →
    M.toAddSubgroup.relIndex (latG V g).toAddSubgroup = Ideal.absNorm P.asIdeal ^ k →
    ∃ a₀ : GA D V, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k a₀ ∧ ∀ v ∈ latG V g,
      (finPart D e • finVec V v ∈ latGHat V (g * a₀) ↔
        finPart D e • finVec V v ∈ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin V.rank → D.host.E))) := by
  atlas_forward_decl GlobalTheory.HeckeLocLift.exists_hecke_ePart
end
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.HeckeOffParts
open scoped Matrix

theorem mulVec_one_sub_idempotent_of_split_sum_identity {A : Type} [CommRing A] {n : ℕ} (a b : A) (h1 : a * a = a) (h2 : a * b = 0)
    (M : Matrix (Fin n) (Fin n) A) (z : Fin n → A) (h6 : M *ᵥ z = (a + b) • M *ᵥ z + z - (a + b) • z) :
    M *ᵥ ((1 - a) • z) = b • M *ᵥ z + z - a • z - b • z := by
  have hP : (1 - a) * (a + b) = b := by linear_combination -h1 - h2
  rw [Matrix.mulVec_smul]
  conv_lhs => rw [h6]
  rw [smul_sub, smul_add, smul_smul, smul_smul, hP, sub_smul, one_smul]
  abel

open GlobalTheory.SplitPlace in
theorem inv_part_mem {D : D7} {e : AE D} (he : IsSplitIdem D e) {V : HSp D} {ϖ : D.host.E} {k : ℕ} {a₀ : GA D V}
    (ha : Formalism.L2.NTheta.IsHeckeElt V e ϖ k a₀) :
    ∀ z ∈ Formalism.L2.NTheta.LamHat V,
      fm V a₀⁻¹ *ᵥ ((1 - finPart D e) • z) ∈ Formalism.L2.NTheta.LamHat V := by
  intro z hz
  obtain ⟨-, hs, h3, -⟩ := ha
  have hi := idem_mem he.1
  have hci := cf_mem hi
  have h3' : ∀ y ∈ Formalism.L2.NTheta.LamHat V, finPart D e • fm V a₀ *ᵥ y ∈ Formalism.L2.NTheta.LamHat V := h3
  have hadj := adj_mem V (finPart D e) a₀ h3' z hz
  have h6 := mulVec_parts (finPart D) ((suppAt_iff e V a₀⁻¹).1 (suppAt_inv hs)) z
  rw [RingHom.map_add, fin_cA, ← fm_eq] at h6
  have e1 : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he.1]
  have e2 : finPart D e * cf D (finPart D e) = 0 := by rw [← fin_cA, ← map_mul, he.2.1, map_zero]
  rw [mulVec_one_sub_idempotent_of_split_sum_identity _ _ e1 e2 _ z h6]
  have m1 : finPart D e • z ∈ Formalism.L2.NTheta.LamHat V := smul_mem V hi hz
  have m2 : cf D (finPart D e) • z ∈ Formalism.L2.NTheta.LamHat V := smul_mem V hci hz
  have m3 := (Formalism.L2.NTheta.LamHat V).add_mem hadj hz
  have m4 := (Formalism.L2.NTheta.LamHat V).sub_mem m3 m1
  exact (Formalism.L2.NTheta.LamHat V).sub_mem m4 m2

open GlobalTheory.SplitPlace in
theorem hat_one_mem {D : D7} {e : AE D} (he : IsSplitIdem D e) {V : HSp D} {ϖ : D.host.E} {k : ℕ} {a₀ : GA D V}
    (ha : Formalism.L2.NTheta.IsHeckeElt V e ϖ k a₀) :
    ∀ w ∈ latGHat V 1, fm V a₀⁻¹ *ᵥ ((1 - finPart D e) • w) ∈ latGHat V 1 := by
  intro w hw
  let f : (Fin V.rank → RF D) →+ (Fin V.rank → RF D) :=
    (Matrix.mulVecLin (fm V a₀⁻¹)).toAddMonoidHom.comp (DistribMulAction.toAddMonoidHom _ (1 - finPart D e))
  change f w ∈ latGHat V 1
  unfold latGHat at hw ⊢
  refine AddSubgroup.mem_comap.1 ((AddSubgroup.closure_le (K := AddSubgroup.comap f _)).2 ?_ hw)
  rintro _ ⟨a, haA, x, ⟨x', hx', rfl⟩, rfl⟩
  rw [SetLike.mem_coe, AddSubgroup.mem_comap]
  refine AddSubgroup.subset_closure ⟨a, haA, _, ⟨fm V a₀⁻¹ *ᵥ ((1 - finPart D e) • x'), ?_, rfl⟩, ?_⟩
  · have hx'' : x' ∈ Formalism.L2.NTheta.LamHat V := by
      rw [← GlobalTheory.LatReflection.latHat_eq_lamHat]; exact hx'
    have := inv_part_mem he ha x' hx''
    rw [← GlobalTheory.LatReflection.latHat_eq_lamHat] at this
    exact this
  · simp only [map_one, Units.val_one, Matrix.one_mulVec]
    change fm V a₀⁻¹ *ᵥ ((1 - finPart D e) • (((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] a) • x')) =
      ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] a) • (fm V a₀⁻¹ *ᵥ ((1 - finPart D e) • x'))
    rw [smul_comm (1 - finPart D e), Matrix.mulVec_smul]

open GlobalTheory.SplitPlace in
theorem off_parts : ∀ (D : D7) (V : HSp D) (e : AE D) (ϖ : D.host.E) (k : ℕ) (g a₀ : GA D V),
    Formalism.L2.Theta.IsSplitIdem D e → Formalism.L2.NTheta.IsHeckeElt V e ϖ k a₀ →
    ∀ y ∈ latGHat V g, (1 - finPart D e) • y ∈ latGHat V (g * a₀) := by
  intro D V e ϖ k g a₀ he ha y hy
  obtain ⟨z, hz, rfl⟩ := ((GlobalTheory.MarkCoset.latG_spec D V g).2 y).1 hy
  refine ((GlobalTheory.MarkCoset.latG_spec D V (g * a₀)).2 _).2
    ⟨fm V a₀⁻¹ *ᵥ ((1 - finPart D e) • z), hat_one_mem he ha z hz, ?_⟩
  rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
  change (finHom V g).1 *ᵥ (fm V a₀ *ᵥ (fm V a₀⁻¹ *ᵥ ((1 - finPart D e) • z))) = _
  rw [fm_vec_inv, Matrix.mulVec_smul]

end GlobalTheory.HeckeOffParts
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_element_keeps_one_sub_idempotent_part_lattice : ∀ (D : D7) (V : HSp D) (e : AE D) (ϖ : D.host.E) (k : ℕ) (g a₀ : GA D V),
    Formalism.L2.Theta.IsSplitIdem D e → Formalism.L2.NTheta.IsHeckeElt V e ϖ k a₀ →
    ∀ y ∈ latGHat V g, (1 - finPart D e) • y ∈ latGHat V (g * a₀) := by
  atlas_forward_decl GlobalTheory.HeckeOffParts.off_parts
end
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.HeckeConjPart

open Formalism.L2.NTheta GlobalTheory.SplitPlace IsDedekindDomain

variable {D : D7}

theorem le_unif {x : WithZero (Multiplicative ℤ)} (h : x < 1) :
    x ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le'
  obtain ⟨u, rfl⟩ := WithZero.ne_zero_iff_exists.1 hx
  rw [← WithZero.coe_one, WithZero.coe_lt_coe] at h
  rw [WithZero.coe_le_coe]
  rw [← Multiplicative.toAdd_lt, toAdd_one] at h
  rw [← Multiplicative.toAdd_le, toAdd_ofAdd]
  omega

theorem ratio_int {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (he : IsIdemAt e P)
    {ϖ : 𝓞 D.host.E} (hP : ϖ ∈ P.asIdeal) (hP2 : ϖ ∉ P.asIdeal ^ 2) {y : 𝓞 D.host.E} (hy : y ∈ P.asIdeal) :
    ∃ t ∈ intAE D, finPart D e * finPart D (incA D (y : D.host.E)) =
      t * (finPart D e * finPart D (incA D (ϖ : D.host.E))) := by
  obtain ⟨v, π, s, h1, h2, h3, h4, h5⟩ := GlobalTheory.SplitCoord.exists_coord e he.1
  have hu := isUnif he h4 h5 ϖ hP hP2
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := by
    intro h0
    apply hP2
    rw [show ϖ = 0 from RingOfIntegers.coe_eq_zero_iff.1 h0]
    exact zero_mem _
  set φ : D.host.E →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v := (π.comp (finPart D)).comp (incA D) with hφ
  set q : D.host.E := (y : D.host.E) / (ϖ : D.host.E)
  refine ⟨finPart D e * finPart D (incA D q), ?_, ?_⟩
  · rw [h4]
    change Valued.v (φ q) ≤ 1
    rw [map_div₀, map_div₀]
    rcases eq_or_ne y 0 with rfl | hy0
    · simp
    have hn := (he.2 y hy0).1 hy
    rw [map_mul, h4] at hn
    change ¬ Valued.v (φ ((y : D.host.E)⁻¹)) ≤ 1 at hn
    rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ((map_ne_zero φ).2 fun h0 => hy0 (RingOfIntegers.coe_eq_zero_iff.1 h0))))] at hn
    have hϖv : Valued.v (φ ϖ) = _ := hu
    have h6 := le_unif hn
    rw [← hϖv] at h6
    rw [div_le_one₀ (by rw [hϖv]; exact zero_lt_iff.2 WithZero.coe_ne_zero)]
    exact h6
  · have hee : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he.1.1]
    have hq : q * (ϖ : D.host.E) = y := div_mul_cancel₀ _ hϖ0
    calc finPart D e * finPart D (incA D (y : D.host.E))
        = (finPart D e * finPart D e) * (finPart D (incA D q) * finPart D (incA D (ϖ : D.host.E))) := by
          rw [hee, ← map_mul (finPart D) (incA D q), ← map_mul (incA D) q, hq]
      _ = _ := mul_mul_mul_comm _ _ _ _

open scoped Matrix

set_option maxHeartbeats 1000000 in

theorem keeps {V : HSp D} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (he : IsIdemAt e P)
    {ϖ : 𝓞 D.host.E} (hP : ϖ ∈ P.asIdeal) (hP2 : ϖ ∉ P.asIdeal ^ 2) {k : ℕ} {a₀ : GA D V}
    (ha : IsHeckeElt V e (ϖ : D.host.E) k a₀) {x : 𝓞 D.host.E} (hx : x ∈ (Formalism.L2.Col.conjPrime₂ P).asIdeal) :
    ∀ z ∈ LamHat V, finPart D (incA D (x : D.host.E)) • fm V a₀ *ᵥ z ∈ LamHat V := by
  intro z hz
  have hee : e * e = e := he.1.1
  have hint : finPart D (incA D (x : D.host.E)) ∈ intAE D :=
    AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, x, rfl⟩
  have hc := hecke_conj hee ha
  have hce : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have h4 := (lower_iff hce V _ a₀⁻¹).1 hc.2.2.2.1
  rw [inv_inv] at h4
  obtain ⟨t, ht, hteq⟩ := ratio_int he hP hP2 ((Formalism.L2.Col.mem_conjP P x).1 hx)
  have hteq' := congrArg (cf D) hteq
  rw [map_mul, map_mul, map_mul, ← fin_cA, ← fin_cA, ← fin_cA, cA_incA, cA_incA] at hteq'
  have hsx : star ((Formalism.L2.Col.cO D.host.E x : 𝓞 D.host.E) : D.host.E) = (x : D.host.E) := by
    change star (star (x : D.host.E)) = _
    exact star_star _
  rw [hsx] at hteq'
  have h6 := mulVec_parts (finPart D) ((suppAt_iff e V a₀).1 ha.2.1) z
  rw [← fm_eq V a₀] at h6
  rw [h6, RingHom.map_add, add_smul, smul_sub, smul_add, smul_add]
  have hi1 := idem_mem hee
  have hi2 := idem_mem hce
  refine sub_mem (add_mem (add_mem ?_ ?_) (smul_mem V hint hz))
    (smul_mem V hint (smul_mem V (add_mem hi1 hi2) hz))
  · exact smul_mem V hint (ha.2.2.1 z hz)
  · rw [smul_smul, mul_comm, hteq', mul_smul]
    exact smul_mem V (cf_mem ht) (h4 z hz)

theorem finHom_eq {V : HSp D} (g : GA D V) : (finHom V g).1 = fm V g := rfl

theorem finPart_incA (c : D.host.E) :
    finPart D (incA D c) = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] c := rfl

theorem keeps_one {V : HSp D} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (he : IsIdemAt e P)
    {ϖ : 𝓞 D.host.E} (hP : ϖ ∈ P.asIdeal) (hP2 : ϖ ∉ P.asIdeal ^ 2) {k : ℕ} {a₀ : GA D V}
    (ha : IsHeckeElt V e (ϖ : D.host.E) k a₀) {x : 𝓞 D.host.E} (hx : x ∈ (Formalism.L2.Col.conjPrime₂ P).asIdeal) :
    ∀ y ∈ latGHat V 1, finPart D (incA D (x : D.host.E)) • fm V a₀ *ᵥ y ∈ latGHat V 1 := by
  intro y hy
  rw [GlobalTheory.LevelActionPinned.latGHat_one] at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, hc, z, hz, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨c, hc, finPart D (incA D (x : D.host.E)) • fm V a₀ *ᵥ z, ?_, ?_⟩
    · rw [GlobalTheory.StdFrameCong.pj_latHat_eq] at hz ⊢
      exact keeps he hP hP2 ha hx z hz
    · rw [Matrix.mulVec_smul, smul_comm]
  | zero => rw [Matrix.mulVec_zero, smul_zero]; exact zero_mem _
  | add a b _ _ ha' hb' => rw [Matrix.mulVec_add, smul_add]; exact add_mem ha' hb'
  | neg a _ ha' => rw [Matrix.mulVec_neg, smul_neg]; exact neg_mem ha'

end GlobalTheory.HeckeConjPart

open scoped Matrix

open GlobalTheory.SplitPlace in

theorem GlobalTheory.HeckeConjPart.conj_part : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E)
    (k : ℕ) (g a₀ : GA D V),
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k a₀ →
    (Formalism.L2.Col.conjPrime₂ P).asIdeal • latG V (g * a₀) ≤ latG V g := by
  intro D V P e ϖ k g a₀ he hP hP2 ha
  rw [Submodule.smul_le]
  intro x hx v hv
  have spec := GlobalTheory.MarkCoset.latG_spec D V
  rw [(spec (g * a₀)).1, (spec (g * a₀)).2] at hv
  obtain ⟨y, hy, hyv⟩ := hv
  rw [(spec g).1, (spec g).2]
  refine ⟨finPart D (incA D (x : D.host.E)) • fm V a₀ *ᵥ y, GlobalTheory.HeckeConjPart.keeps_one he hP hP2 ha hx y hy, ?_⟩
  rw [GlobalTheory.HeckeConjPart.finHom_eq] at hyv ⊢
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← fm_mul, hyv]
  funext i
  simp only [finVec, Pi.smul_apply, smul_eq_mul, GlobalTheory.HeckeConjPart.finPart_incA,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjPrime_smul_lattice_heckeElement_le : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (k : ℕ) (g a₀ : GA D V),
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k a₀ →
    (Formalism.L2.Col.conjPrime₂ P).asIdeal • latG V (g * a₀) ≤ latG V g := by
  atlas_forward_decl GlobalTheory.HeckeConjPart.conj_part
end
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.HeckeLocStep

open Formalism.L2.Theta
open scoped TensorProduct

theorem smul_mem_hat (D : D7) {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    {a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (ha : a ∈ intAE D)
    {y : Fin n → GlobalTheory.AdLat.RA D.host.F D.host.E} (hy : y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E))) :
    a • y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) := by
  induction ha using AddSubgroup.closure_induction generalizing y with
  | mem w hw =>
    obtain ⟨b, hb, x, rfl⟩ := hw
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨c, hc, m, hm, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨b * c, fun v => ?_, x • m, L.smul_mem x hm, ?_⟩
      · exact mul_mem (hb v) (hc v)
      · funext i
        simp [Algebra.TensorProduct.tmul_mul_tmul]
        rfl
    | zero => rw [smul_zero]; exact zero_mem _
    | add z z' _ _ h h' => rw [smul_add]; exact add_mem h h'
    | neg z _ h => rw [smul_neg]; exact neg_mem h
  | zero => rw [zero_smul]; exact zero_mem _
  | add a b _ _ h h' => rw [add_smul]; exact add_mem (h hy) (h' hy)
  | neg a _ h => rw [neg_smul]; exact neg_mem (h hy)

end GlobalTheory.HeckeLocStep

namespace GlobalTheory.HeckeLocStep

open Formalism.L2.Theta
open scoped TensorProduct

theorem hat_mono {D : D7} {n : ℕ} {L L' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : L ≤ L') :
    GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) ≤ GlobalTheory.AdLat.hat D.host.F (L' : Set (Fin n → D.host.E)) := by
  refine AddSubgroup.closure_mono ?_
  rintro _ ⟨a, ha, x, hx, rfl⟩
  exact ⟨a, ha, x, h hx, rfl⟩

theorem span_smul_top {D : D7} {n : ℕ} (P : Formalism.L2.DIV.Pl D.host.E) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hL : Submodule.span D.host.E (L : Set (Fin n → D.host.E)) = ⊤) :
    Submodule.span D.host.E ((P.asIdeal • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = ⊤ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  have hx0' : ((x : D.host.E)) ≠ 0 := fun h => hx0 (RingOfIntegers.ext h)
  rw [eq_top_iff, ← hL, Submodule.span_le]
  intro w hw
  have hm : x • w ∈ (P.asIdeal • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) := Submodule.smul_mem_smul hx hw
  have : w = (x : D.host.E)⁻¹ • (x • w) := by
    rw [← algebraMap_smul D.host.E x w]
    rw [smul_smul, inv_mul_cancel₀ (by simpa using hx0'), one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

theorem mem_iff_ePart : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (g : GA D V)
    (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.L2.NTheta.IsIdemAt e P → P.asIdeal • latG V g ≤ M → M ≤ latG V g →
    ∀ v ∈ latG V g, (v ∈ M ↔ finPart D e • finVec V v ∈ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin V.rank → D.host.E))) := by
  intro D V P e g M he hPM hMΛ v hv
  obtain ⟨h1, h2, -, -, -, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V g
  have hMfg : M.FG := by
    have hN : IsNoetherian (𝓞 D.host.E) (latG V g) := isNoetherian_of_fg_of_noetherian _ h1
    have hc := (IsNoetherian.noetherian (M.comap (latG V g).subtype)).map (latG V g).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hMΛ] at hc
  have hMsp : Submodule.span D.host.E (M : Set (Fin V.rank → D.host.E)) = ⊤ :=
    eq_top_iff.2 ((span_smul_top P _ h2).symm.le.trans (Submodule.span_mono hPM))
  have hrat := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank M hMfg hMsp).1
  have hint : finPart D e ∈ intAE D := GlobalTheory.SplitPlace.idem_mem he.1.1
  have hvM : ∀ {w}, w ∈ M → GlobalTheory.AdLat.fv D.host.F w ∈ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin V.rank → D.host.E)) :=
    fun hw => (hrat _).2 hw
  constructor
  · intro hm
    exact smul_mem_hat D M hint (hvM hm)
  · intro h
    refine (hrat v).1 ?_
    have hΛ : GlobalTheory.AdLat.fv D.host.F v ∈ GlobalTheory.AdLat.hat D.host.F ((latG V g : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) :=
      ((GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank _ h1 h2).1 v).2 hv
    have h3 := hat_mono hPM (GlobalTheory.T.one_sub_idempotent_smul_mem_completion_prime_mul D P e V.rank (latG V g) he _ hΛ)
    have hsplit : GlobalTheory.AdLat.fv D.host.F v = finPart D e • finVec V v + (1 - finPart D e) • finVec V v := by
      rw [← add_smul, add_sub_cancel, one_smul]; rfl
    rw [hsplit]
    exact add_mem h h3

theorem mem_latG_iff (D : D7) (V : HSp D) (x : GA D V) (v : Fin V.rank → D.host.E) :
    v ∈ latG V x ↔ finVec V v ∈ latGHat V x := by
  obtain ⟨h1, h2, -, -, h5, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V x
  rw [h5]
  exact ((GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank _ h1 h2).1 v).symm

theorem exists_hecke : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (k : ℕ) (g : GA D V)
    (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    P.asIdeal • latG V g ≤ M → M ≤ latG V g →
    M.toAddSubgroup.relIndex (latG V g).toAddSubgroup = Ideal.absNorm P.asIdeal ^ k →
    ∃ a₀ : GA D V, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k a₀ ∧ latG V (g * a₀) ⊓ latG V g = M ∧
      (Formalism.L2.Col.conjPrime₂ P).asIdeal • latG V (g * a₀) ≤ latG V g := by
  intro D V P e ϖ k g M he h1 h2 hPM hMΛ hidx
  obtain ⟨a₀, hH, hloc⟩ := GlobalTheory.T.exists_heckeElement_idempotentPart_splitPlace_lattice D V P e ϖ k g M he h1 h2 hPM hMΛ hidx
  refine ⟨a₀, hH, ?_, GlobalTheory.T.conjPrime_smul_lattice_heckeElement_le D V P e ϖ k g a₀ he h1 h2 hH⟩
  have hint : finPart D e ∈ intAE D := GlobalTheory.SplitPlace.idem_mem he.1.1
  ext v
  rw [Submodule.mem_inf]
  constructor
  · rintro ⟨ha, hg⟩
    refine (mem_iff_ePart D V P e g M he hPM hMΛ v hg).2 ((hloc v hg).1 ?_)
    have := (mem_latG_iff D V (g * a₀) v).1 ha
    rw [(GlobalTheory.Member.latG_lattice_and_completion D V (g * a₀)).2.2.2.2.1] at this ⊢
    exact smul_mem_hat D _ hint this
  · intro hv
    have hg := hMΛ hv
    refine ⟨(mem_latG_iff D V (g * a₀) v).2 ?_, hg⟩
    have hsplit : finVec V v = finPart D e • finVec V v + (1 - finPart D e) • finVec V v := by
      rw [← add_smul, add_sub_cancel, one_smul]
    rw [hsplit]
    exact add_mem ((hloc v hg).2 ((mem_iff_ePart D V P e g M he hPM hMΛ v hg).1 hv))
      (GlobalTheory.T.hecke_element_keeps_one_sub_idempotent_part_lattice D V e ϖ k g a₀ he.1 hH _ ((mem_latG_iff D V g v).1 hg))

end GlobalTheory.HeckeLocStep
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeElement_lattice_between_prime_mul_split : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (k : ℕ) (g : GA D V)
    (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    P.asIdeal • latG V g ≤ M → M ≤ latG V g →
    M.toAddSubgroup.relIndex (latG V g).toAddSubgroup = Ideal.absNorm P.asIdeal ^ k →
    ∃ a₀ : GA D V, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k a₀ ∧ latG V (g * a₀) ⊓ latG V g = M ∧
      (Formalism.L2.Col.conjPrime₂ P).asIdeal • latG V (g * a₀) ≤ latG V g := by
  atlas_forward_decl GlobalTheory.HeckeLocStep.exists_hecke
end
end
