import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.InfinityTypes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtEqInfMat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicFamilyLowLieAction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestWeightMatrixCoefficientDependsOnWeight
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialActionOneMulAdjoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FsubMinorMinus
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolynomialModelCoefficientSpaceRealPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilMaximalCompactFockSubstitutionCharacterStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaWeightArithmeticAtPlaceProofStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftInfinityTypesAtRealPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeCoefficientWeightEqMinorWeightsStatement

section
namespace GlobalTheory.GramLinearMap

theorem gram_comb {P : Type} [AddCommGroup P] [Module ℂ P] {B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ}
    {P' : Type} [AddCommGroup P'] [Module ℂ P'] {B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ} {U : Type}
    (f : U → P) (f' : U → P') {c d : ℂ}
    (h : ∀ u v : U, B (f u) (f v) * c = d * B' (f' u) (f' v)) (x y : U →₀ ℂ) :
    B (Finsupp.linearCombination ℂ f x) (Finsupp.linearCombination ℂ f y) * c =
      d * B' (Finsupp.linearCombination ℂ f' x) (Finsupp.linearCombination ℂ f' y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply, add_mul, mul_add, h₁, h₂]
  | single u a =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add, add_mul, mul_add, h₁, h₂]
    | single v b =>
      simp only [Finsupp.linearCombination_single, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
        smul_eq_mul, RingHom.id_apply]
      linear_combination (b * (starRingEnd ℂ) a) * h u v

theorem exists_linearMap_of_gram {P : Type} [AddCommGroup P] [Module ℂ P]
    {B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ}
    {P' : Type} [AddCommGroup P'] [Module ℂ P'] {B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ} {U : Type}
    (f : U → P) (f' : U → P') (hB : ∀ y : P, B y y = 0 → y = 0) {c d : ℂ} (hc : c ≠ 0)
    (h : ∀ u v : U, B (f u) (f v) * c = d * B' (f' u) (f' v)) :
    ∃ ψ : P' →ₗ[ℂ] P, ∀ u : U, ψ (f' u) = f u := by
  set T := Finsupp.linearCombination ℂ f with hT
  set T' := Finsupp.linearCombination ℂ f' with hT'
  have hker : ∀ x, T' x = 0 → T x = 0 := by
    intro x hx
    apply hB
    have := gram_comb f f' h x x
    rw [← hT, ← hT', hx] at this
    simpa [hc] using this
  obtain ⟨g, hg⟩ := T'.rangeRestrict.exists_rightInverse_of_surjective T'.range_rangeRestrict
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend (T ∘ₗ g)
  refine ⟨ψ, fun u => ?_⟩
  have h1 : T' (Finsupp.single u 1) = f' u := by simp [hT']
  have h2 : T (Finsupp.single u 1) = f u := by simp [hT]
  let z : LinearMap.range T' := ⟨f' u, _, h1⟩
  have h3 : ψ (f' u) = T (g z) := LinearMap.congr_fun hψ z
  have h4 : T' (g z) = f' u := congrArg Subtype.val (LinearMap.congr_fun hg z)
  have h5 : T (g z - Finsupp.single u 1) = 0 := hker _ (by rw [map_sub, h4, h1, sub_self])
  rw [map_sub, sub_eq_zero] at h5
  rw [h3, h5, h2]

end GlobalTheory.GramLinearMap
end

section
section
open Matrix GlobalTheory.JointHarm
open scoped Classical

namespace GlobalTheory.JointHarm.OrbitMap

variable {ι : Type} {n : ℕ}

theorem one_mem_K (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.REAL.Kset ε :=
  ⟨one_mem _, by simp⟩

theorem one_mem_KC (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ GlobalTheory.Dec.KC ε :=
  ⟨isUnit_one, by simp⟩

theorem K_sub_KC {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) :
    g ∈ GlobalTheory.Dec.KC ε :=
  ⟨⟨Unitary.toUnits ⟨g, hg.1⟩, rfl⟩, hg.2⟩

theorem mul_mem_K {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε)
    (hh : h ∈ Formalism.REAL.Kset ε) : g * h ∈ Formalism.REAL.Kset ε :=
  ⟨mul_mem hg.1 hh.1, by rw [Matrix.mul_assoc, hh.2, ← Matrix.mul_assoc, hg.2, Matrix.mul_assoc]⟩

theorem star_mem_K {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) :
    gᴴ ∈ Formalism.REAL.Kset ε := by
  have h1 : gᴴ * g = 1 := Unitary.star_mul_self_of_mem hg.1
  have h2 : g * gᴴ = 1 := Unitary.mul_star_self_of_mem hg.1
  refine ⟨Unitary.star_mem hg.1, ?_⟩
  calc gᴴ * Formalism.REAL.Jm ε = gᴴ * (Formalism.REAL.Jm ε * g) * gᴴ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]
    _ = Formalism.REAL.Jm ε * gᴴ := by
        rw [← hg.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem single_mem_KC {ε : ι → Fin n → Bool} {τ : ι} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ GlobalTheory.Dec.KC (ε τ)) (σ : ι) :
    (Pi.mulSingle τ g : ι → Matrix (Fin n) (Fin n) ℂ) σ ∈ GlobalTheory.Dec.KC (ε σ) := by
  by_cases h : σ = τ
  · subst h; simpa using hg
  · simpa [h] using one_mem_KC _

theorem single_comm {τ : ι} (g : Matrix (Fin n) (Fin n) ℂ) {v : ι → Matrix (Fin n) (Fin n) ℂ}
    (hv : v τ = 1) : Pi.mulSingle τ g * v = v * Pi.mulSingle τ g := by
  funext σ
  by_cases h : σ = τ
  · subst h; simp [hv]
  · simp [h]

theorem fam_induction [Fintype ι] {ε : ι → Fin n → Bool} (Q : (ι → Matrix (Fin n) (Fin n) ℂ) → Prop)
    (h1 : Q 1)
    (hs : ∀ τ k v, k ∈ Formalism.REAL.Kset (ε τ) → (∀ σ, v σ ∈ Formalism.REAL.Kset (ε σ)) → v τ = 1 → Q v →
      Q (Pi.mulSingle τ k * v)) (u : ι → Matrix (Fin n) (Fin n) ℂ)
    (hu : ∀ σ, u σ ∈ Formalism.REAL.Kset (ε σ)) : Q u := by
  have key : ∀ s : Finset ι, ∀ u : ι → Matrix (Fin n) (Fin n) ℂ,
      (∀ σ, u σ ∈ Formalism.REAL.Kset (ε σ)) → (∀ σ ∉ s, u σ = 1) → Q u := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro u _ h
      have : u = 1 := funext fun σ => h σ (by simp)
      rw [this]; exact h1
    | insert τ s _ ih =>
      intro u hu h
      have hv : ∀ σ, Function.update u τ 1 σ ∈ Formalism.REAL.Kset (ε σ) := by
        intro σ
        by_cases e : σ = τ
        · subst e; simpa using one_mem_K _
        · simpa [e] using hu σ
      have e : u = Pi.mulSingle τ (u τ) * Function.update u τ 1 := by
        funext σ
        by_cases e : σ = τ
        · subst e; simp
        · simp [e]
      rw [e]
      refine hs τ _ _ (hu τ) hv (by simp) (ih _ hv fun σ hσ => ?_)
      by_cases e : σ = τ
      · subst e; simp
      · simpa [e] using h σ (by simp [e, hσ])
  exact key Finset.univ u hu (by simp)

variable {P : Type} [AddCommGroup P] [Module ℂ P] {B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ}
  {ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P} {ε : ι → Fin n → Bool} {μ : ι → Fin n → ℝ}

theorem adj_fam [Fintype ι] (h : IsHolFam ε B ϖ) (u : ι → Matrix (Fin n) (Fin n) ℂ)
    (hu : ∀ σ, u σ ∈ Formalism.REAL.Kset (ε σ)) :
    ∀ a b, B (ϖ u a) b = B a (ϖ (fun σ => (u σ)ᴴ) b) := by
  refine fam_induction (ε := ε) (fun u => ∀ a b, B (ϖ u a) b = B a (ϖ (fun σ => (u σ)ᴴ) b)) ?_ ?_ u hu
  · intro a b
    have : (fun σ => ((1 : ι → Matrix (Fin n) (Fin n) ℂ) σ)ᴴ) = 1 := by funext σ; simp
    rw [this, h.2.1]; rfl
  · intro τ k v hk hv _ ih a b
    have e : (fun σ => ((Pi.mulSingle τ k * v : ι → Matrix (Fin n) (Fin n) ℂ) σ)ᴴ) =
        (fun σ => (v σ)ᴴ) * Pi.mulSingle τ kᴴ := by
      funext σ
      by_cases e : σ = τ
      · subst e; simp
      · simp [e]
    rw [e, h.2.2.1 _ _ (single_mem_KC (K_sub_KC hk)) (fun σ => K_sub_KC (hv σ)),
      h.2.2.1 _ _ (fun σ => K_sub_KC (star_mem_K (hv σ))) (single_mem_KC (K_sub_KC (star_mem_K hk))),
      Module.End.mul_apply, Module.End.mul_apply, ← ih]
    exact (h.2.2.2 τ).2.2.2.1 k (K_sub_KC hk) _ _

theorem bottom_move (h : IsHolFam ε B ϖ) {x : P} (hx : IsBotFam ε ϖ μ x) {τ : ι}
    {v : ι → Matrix (Fin n) (Fin n) ℂ} (hv : ∀ σ, v σ ∈ Formalism.REAL.Kset (ε σ)) (hτ : v τ = 1) :
    IsBottom (ε τ) (fun g => ϖ (Pi.mulSingle τ g)) (μ τ) (ϖ v x) := by
  have c : ∀ g ∈ GlobalTheory.Dec.KC (ε τ), ϖ (Pi.mulSingle τ g) (ϖ v x) = ϖ v (ϖ (Pi.mulSingle τ g) x) := by
    intro g hg
    rw [← Module.End.mul_apply, ← Module.End.mul_apply,
      ← h.2.2.1 _ _ (single_mem_KC hg) (fun σ => K_sub_KC (hv σ)),
      ← h.2.2.1 _ _ (fun σ => K_sub_KC (hv σ)) (single_mem_KC hg), single_comm g hτ]
  refine ⟨fun g hg hl => ?_, fun θ => ?_⟩
  · show ϖ (Pi.mulSingle τ g) (ϖ v x) = _
    rw [c g hg]
    exact congrArg _ ((hx τ).1 g hg hl)
  · show ϖ (Pi.mulSingle τ _) (ϖ v x) = _
    rw [c, ← map_smul]
    · exact congrArg _ ((hx τ).2 θ)
    · refine ⟨?_, by simp [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]⟩
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal, isUnit_iff_ne_zero]
      exact Finset.prod_ne_zero_iff.2 fun a _ => Complex.exp_ne_zero _

variable {P' : Type} [AddCommGroup P'] [Module ℂ P'] {B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ}
  {ϖ' : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P'}

theorem coef_fam [Fintype ι] (h : IsHolFam ε B ϖ) (h' : IsHolFam ε B' ϖ') {x : P} {x' : P'}
    (hx : IsBotFam ε ϖ μ x) (hx' : IsBotFam ε ϖ' μ x') (h0 : x' ≠ 0)
    (u : ι → Matrix (Fin n) (Fin n) ℂ) (hu : ∀ σ, u σ ∈ Formalism.REAL.Kset (ε σ)) :
    B x (ϖ u x) * B' x' x' = B x x * B' x' (ϖ' u x') := by
  have hc : B' x' x' ≠ 0 := fun e => h0 (h'.1 _ e)
  refine fam_induction (ε := ε) (fun u => B x (ϖ u x) * B' x' x' = B x x * B' x' (ϖ' u x')) ?_ ?_ u hu
  · show B x (ϖ 1 x) * B' x' x' = B x x * B' x' (ϖ' 1 x')
    rw [h.2.1, h'.2.1]; rfl
  · intro τ k v hk hv hτ ih
    have e1 := GlobalTheory.JointHarm.Sph.coeff_eq n (ε τ) (μ τ) P B _ P' B' _ x (ϖ v x) x' x' (h.2.2.2 τ) (h'.2.2.2 τ)
      (hx τ) (bottom_move h hx hv hτ) (hx' τ) (hx' τ) k hk
    have e2 := GlobalTheory.JointHarm.Sph.coeff_eq n (ε τ) (μ τ) P' B' _ P' B' _ x' (ϖ' v x') x' x' (h'.2.2.2 τ) (h'.2.2.2 τ)
      (hx' τ) (bottom_move h' hx' hv hτ) (hx' τ) (hx' τ) k hk
    show B x (ϖ (Pi.mulSingle τ k * v) x) * B' x' x' = B x x * B' x' (ϖ' (Pi.mulSingle τ k * v) x')
    rw [h.2.2.1 _ _ (single_mem_KC (K_sub_KC hk)) (fun σ => K_sub_KC (hv σ)),
      h'.2.2.1 _ _ (single_mem_KC (K_sub_KC hk)) (fun σ => K_sub_KC (hv σ)),
      Module.End.mul_apply, Module.End.mul_apply]
    apply mul_right_cancel₀ hc
    linear_combination (B' x' x') * e1 - (B x x) * e2 + (B' x' (ϖ' (Pi.mulSingle τ k) x')) * ih

theorem gram_fam [Fintype ι] (h : IsHolFam ε B ϖ) (h' : IsHolFam ε B' ϖ') {x : P} {x' : P'}
    (hx : IsBotFam ε ϖ μ x) (hx' : IsBotFam ε ϖ' μ x') (h0 : x' ≠ 0)
    (u v : ι → Matrix (Fin n) (Fin n) ℂ) (hu : ∀ σ, u σ ∈ Formalism.REAL.Kset (ε σ))
    (hv : ∀ σ, v σ ∈ Formalism.REAL.Kset (ε σ)) :
    B (ϖ u x) (ϖ v x) * B' x' x' = B x x * B' (ϖ' u x') (ϖ' v x') := by
  rw [adj_fam h u hu, adj_fam h' u hu, ← Module.End.mul_apply, ← Module.End.mul_apply,
    ← h.2.2.1 _ _ (fun σ => K_sub_KC (star_mem_K (hu σ))) (fun σ => K_sub_KC (hv σ)),
    ← h'.2.2.1 _ _ (fun σ => K_sub_KC (star_mem_K (hu σ))) (fun σ => K_sub_KC (hv σ))]
  exact coef_fam h h' hx hx' h0 _ fun σ => mul_mem_K (star_mem_K (hu σ)) (hv σ)

theorem exists_map_of_gram {U : Type} (f : U → P) (f' : U → P') (hB : ∀ y, B y y = 0 → y = 0)
    {c d : ℂ} (hc : c ≠ 0) (hg : ∀ u v, B (f u) (f v) * c = d * B' (f' u) (f' v)) :
    ∃ ψ : P' →ₗ[ℂ] P, ∀ u, ψ (f' u) = f u := by
  first
  | exact @_root_.GlobalTheory.GramLinearMap.exists_linearMap_of_gram
  | exact _root_.GlobalTheory.GramLinearMap.exists_linearMap_of_gram
  | (apply _root_.GlobalTheory.GramLinearMap.exists_linearMap_of_gram <;> assumption)
  | (intros; apply _root_.GlobalTheory.GramLinearMap.exists_linearMap_of_gram <;> assumption)
  | (intros; apply @_root_.GlobalTheory.GramLinearMap.exists_linearMap_of_gram <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.GramLinearMap.exists_linearMap_of_gram ..)

theorem exists_orbit_map : ∀ (ι : Type) [Fintype ι] (n : ℕ) (ε : ι → Fin n → Bool) (μ : ι → Fin n → ℝ) (P : Type) [AddCommGroup P] [Module ℂ P] (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ) (ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P) (P' : Type) [AddCommGroup P'] [Module ℂ P'] (B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ) (ϖ' : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P') (x : P) (x' : P'), IsHolFam ε B ϖ → IsHolFam ε B' ϖ' → IsBotFam ε ϖ μ x → IsBotFam ε ϖ' μ x' → x' ≠ 0 → ∃ ψ : P' →ₗ[ℂ] P, ∀ u : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, u τ ∈ Formalism.REAL.Kset (ε τ)) → ψ (ϖ' u x') = ϖ u x := by
  intro ι _ n ε μ P _ _ B ϖ P' _ _ B' ϖ' x x' h h' hx hx' h0
  obtain ⟨ψ, hψ⟩ := exists_map_of_gram (B := B) (B' := B')
    (U := {u : ι → Matrix (Fin n) (Fin n) ℂ // ∀ τ, u τ ∈ Formalism.REAL.Kset (ε τ)})
    (fun u => ϖ u.1 x) (fun u => ϖ' u.1 x') h.1 (fun e => h0 (h'.1 _ e))
    (fun u v => gram_fam h h' hx hx' h0 u.1 v.1 u.2 v.2)
  exact ⟨ψ, fun u hu => hψ ⟨u, hu⟩⟩

end GlobalTheory.JointHarm.OrbitMap
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowest_weight_vector_transfer : ∀ (ι : Type) [Fintype ι] (n : ℕ) (ε : ι → Fin n → Bool) (μ : ι → Fin n → ℝ) (P : Type) [AddCommGroup P] [Module ℂ P] (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ) (ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P) (P' : Type) [AddCommGroup P'] [Module ℂ P'] (B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ) (ϖ' : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P') (x : P) (x' : P'), IsHolFam ε B ϖ → IsHolFam ε B' ϖ' → IsBotFam ε ϖ μ x → IsBotFam ε ϖ' μ x' → x' ≠ 0 → ∃ ψ : P' →ₗ[ℂ] P, ∀ u : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, u τ ∈ Formalism.REAL.Kset (ε τ)) → ψ (ϖ' u x') = ϖ u x := by
  atlas_forward_decl GlobalTheory.JointHarm.OrbitMap.exists_orbit_map
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialAction_one_mul_adjoint : ∀ (D : D7) (m n : ℕ) (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ), fact (n := n) ε x₁ x₂ x₃ 1 1 = 1 ∧ (∀ (k k' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (u u' : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ), (∀ τ, k τ ∈ GlobalTheory.Dec.KC (ε τ)) → (∀ τ, k' τ ∈ GlobalTheory.Dec.KC (ε τ)) → (∀ τ, IsUnit (u τ)) → (∀ τ, IsUnit (u' τ)) → fact ε x₁ x₂ x₃ (k * k') (u * u') = fact ε x₁ x₂ x₃ k u * fact ε x₁ x₂ x₃ k' u') ∧ ∀ (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ), (∀ τ, k τ ∈ GlobalTheory.Dec.KC (ε τ)) → (∀ τ, IsUnit (u τ)) → ∀ F F' : PolF D m n, fockL (fact ε x₁ x₂ x₃ k u F) F' = fockL F (fact ε x₁ x₂ x₃ (fun τ => (k τ)ᴴ) (fun τ => (u τ)ᴴ) F') := by
  first | exact @GlobalTheory.JointHarm.fact_one_mul_adj | exact GlobalTheory.JointHarm.fact_one_mul_adj | (intros; apply GlobalTheory.JointHarm.fact_one_mul_adj <;> assumption)
end

section
section
noncomputable section

namespace GlobalTheory.FockHol

open Matrix

section Diff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z : E} {n : ℕ}

theorem diff_prod {ι : Type} (s : Finset ι) {f : ι → E → ℂ} (h : ∀ i ∈ s, DifferentiableAt ℂ (f i) z) :
    DifferentiableAt ℂ (fun w => ∏ i ∈ s, f i w) z := by
  classical
  exact (HasFDerivAt.finset_prod fun i hi => (h i hi).hasFDerivAt).differentiableAt

def EntryDiff (M : E → Matrix (Fin n) (Fin n) ℂ) (z : E) : Prop :=
  ∀ i j, DifferentiableAt ℂ (fun w => M w i j) z

theorem EntryDiff.const (A : Matrix (Fin n) (Fin n) ℂ) : EntryDiff (fun _ : E => A) z :=
  fun _ _ => differentiableAt_const _

theorem EntryDiff.det {M : E → Matrix (Fin n) (Fin n) ℂ} (h : EntryDiff M z) :
    DifferentiableAt ℂ (fun w => (M w).det) z := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun σ _ => (differentiableAt_const _).mul ?_
  exact diff_prod _ fun i _ => h _ _

theorem EntryDiff.transpose {M : E → Matrix (Fin n) (Fin n) ℂ} (h : EntryDiff M z) :
    EntryDiff (fun w => (M w)ᵀ) z := fun i j => h j i

theorem EntryDiff.affine {M : E → Matrix (Fin n) (Fin n) ℂ} (h : EntryDiff M z) (A B : Matrix (Fin n) (Fin n) ℂ) :
    EntryDiff (fun w => A * M w + B) z := by
  intro i j
  simp only [Matrix.add_apply, Matrix.mul_apply]
  exact (DifferentiableAt.fun_sum fun k _ => (differentiableAt_const _).mul (h _ _)).add (differentiableAt_const _)

theorem EntryDiff.inv {M : E → Matrix (Fin n) (Fin n) ℂ} (h : EntryDiff M z) (hu : IsUnit (M z)) :
    EntryDiff (fun w => (M w)⁻¹) z := by
  intro i j
  have hd : (M z).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  refine (h.det.inv hd).mul (EntryDiff.det ?_)
  intro a b
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact differentiableAt_const _
  · exact h _ _

theorem EntryDiff.zpow_det {M : E → Matrix (Fin n) (Fin n) ℂ} (h : EntryDiff M z) (hd : (M z).det ≠ 0) (x : ℤ) :
    DifferentiableAt ℂ (fun w => (M w).det ^ x) z :=
  h.det.zpow (Or.inl hd)

def CoeffDiff {σ : Type} (F : E → MvPolynomial σ ℂ) (z : E) : Prop :=
  ∀ d, DifferentiableAt ℂ (fun w => (F w).coeff d) z

theorem CoeffDiff.mul {σ : Type} {F G : E → MvPolynomial σ ℂ} (hF : CoeffDiff F z) (hG : CoeffDiff G z) :
    CoeffDiff (fun w => F w * G w) z := by
  classical
  intro d
  simp only [MvPolynomial.coeff_mul]
  exact DifferentiableAt.fun_sum fun k _ => (hF _).mul (hG _)

theorem CoeffDiff.aeval {σ : Type} {F : E → σ → MvPolynomial σ ℂ} (hF : ∀ v, CoeffDiff (fun w => F w v) z)
    (y : MvPolynomial σ ℂ) : CoeffDiff (fun w => MvPolynomial.aeval (F w) y) z := by
  induction y using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.aeval_C]
    exact fun _ => differentiableAt_const _
  | add p q hp hq =>
    intro d
    simp only [map_add, MvPolynomial.coeff_add]
    exact (hp d).add (hq d)
  | mul_X p v hp =>
    simp only [map_mul, MvPolynomial.aeval_X]
    exact hp.mul (hF v)

theorem CoeffDiff.fock {σ : Type} {F : E → MvPolynomial σ ℂ} (hF : CoeffDiff F z) (x : MvPolynomial σ ℂ) :
    DifferentiableAt ℂ (fun w => Formalism.L2.DIV.fockL x (F w)) z := by
  simp only [Formalism.L2.DIV.fockL_apply, Formalism.L2.DIV.fockS]
  exact DifferentiableAt.fun_sum fun k _ => ((differentiableAt_const _).mul (hF _)).mul (differentiableAt_const _)

end Diff

theorem fockL_aniso {σ : Type} (f : MvPolynomial σ ℂ) (h : Formalism.L2.DIV.fockL f f = 0) : f = 0 := by
  by_contra hf
  have e : Formalism.L2.DIV.fockL f f =
      ((∑ m ∈ f.support, ‖f.coeff m‖ ^ 2 * (Formalism.L2.DIV.mfact m : ℝ) : ℝ) : ℂ) := by
    rw [Formalism.L2.DIV.fockL_apply]
    unfold Formalism.L2.DIV.fockS
    push_cast
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Complex.conj_mul']
    rfl
  rw [e, Complex.ofReal_eq_zero] at h
  refine ne_of_gt (Finset.sum_pos (fun m hm => mul_pos (pow_pos (norm_pos_iff.mpr
    (MvPolynomial.mem_support_iff.mp hm)) 2) ?_) (MvPolynomial.support_nonempty.mpr hf)) h
  exact_mod_cast Finset.prod_pos fun k _ => Nat.factorial_pos _

section KC

open GlobalTheory.Dec GlobalTheory.JointHarm Formalism.REAL

variable {m : ℕ} {ε : Fin m → Bool}

theorem Jm_mul_self : Jm ε * Jm ε = 1 := by
  rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

theorem detPlus_mul_detMinus {k : Matrix (Fin m) (Fin m) ℂ} (hk : k ∈ KC ε) : detP ε k * detM ε k = k.det := by
  rw [detP, detM, ← Matrix.det_mul]
  congr 1
  have h1 := Jm_mul_self (ε := ε)
  have h2 : k * Jm ε = Jm ε * k := hk.2
  have h3 : ∀ x, Jm ε * (Jm ε * x) = x := fun x => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have h4 : ∀ x, k * (Jm ε * x) = Jm ε * (k * x) := fun x => by rw [← Matrix.mul_assoc, h2, Matrix.mul_assoc]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one, h1, h2, h3, h4]
  module

theorem det_ne {k : Matrix (Fin m) (Fin m) ℂ} (hk : IsUnit k) : k.det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).1 hk).ne_zero

theorem one_mem_KC : (1 : Matrix (Fin m) (Fin m) ℂ) ∈ KC ε := ⟨isUnit_one, by simp⟩

theorem invT_mem_KC {k : Matrix (Fin m) (Fin m) ℂ} (hk : k ∈ KC ε) : (k⁻¹)ᵀ ∈ KC ε := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hk.1
  refine ⟨(Matrix.isUnit_transpose _).2 (Matrix.isUnit_nonsing_inv_iff.2 hk.1), ?_⟩
  have hJ : (Jm ε)ᵀ = Jm ε := Matrix.diagonal_transpose _
  have h2 : k * Jm ε = Jm ε * k := hk.2
  have : Jm ε * k⁻¹ = k⁻¹ * Jm ε := by
    calc Jm ε * k⁻¹ = k⁻¹ * (k * Jm ε) * k⁻¹ := by rw [Matrix.nonsing_inv_mul_cancel_left _ _ hd]
      _ = k⁻¹ * Jm ε := by rw [h2, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hd]
  rw [← hJ, ← Matrix.transpose_mul, ← Matrix.transpose_mul, this]

theorem mulSingle_mem_KC {ι : Type} [DecidableEq ι] {ε : ι → Fin m → Bool} {τ : ι} {g : Matrix (Fin m) (Fin m) ℂ}
    (hg : g ∈ KC (ε τ)) (τ' : ι) : (Pi.mulSingle τ g : ι → Matrix (Fin m) (Fin m) ℂ) τ' ∈ KC (ε τ') := by
  by_cases h : τ' = τ
  · subst h; simpa using hg
  · simpa [h] using one_mem_KC

theorem mulSingle_conjTranspose {ι : Type} [DecidableEq ι] (τ τ' : ι) (g : Matrix (Fin m) (Fin m) ℂ) :
    ((Pi.mulSingle τ g : ι → Matrix (Fin m) (Fin m) ℂ) τ')ᴴ =
      (Pi.mulSingle τ gᴴ : ι → Matrix (Fin m) (Fin m) ℂ) τ' := by
  by_cases h : τ' = τ
  · subst h; simp
  · simp [h]

theorem entryDiff_mulSingle {ι : Type} [DecidableEq ι] (τ τ' : ι) (z : Fin m → Fin m → ℂ) :
    EntryDiff (fun g : Fin m → Fin m → ℂ => (Pi.mulSingle τ (Matrix.of g) : ι → Matrix (Fin m) (Fin m) ℂ) τ') z := by
  by_cases h : τ' = τ
  · subst h
    intro i j
    simp only [Pi.mulSingle_eq_same, Matrix.of_apply]
    fun_prop
  · simp only [Pi.mulSingle_eq_of_ne h]
    exact EntryDiff.const _

open scoped Classical in

theorem isHolFam_of {ι P : Type} [AddCommGroup P] [Module ℂ P] {ε : ι → Fin m → Bool}
    {B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ} {ϖ : (ι → Matrix (Fin m) (Fin m) ℂ) → Module.End ℂ P}
    (h0 : ∀ x, B x x = 0 → x = 0) (h1 : ϖ 1 = 1)
    (hm : ∀ a b, (∀ τ, a τ ∈ KC (ε τ)) → (∀ τ, b τ ∈ KC (ε τ)) → ϖ (a * b) = ϖ a * ϖ b)
    (ha : ∀ a, (∀ τ, a τ ∈ KC (ε τ)) → ∀ x y, B (ϖ a x) y = B x (ϖ (fun τ => (a τ)ᴴ) y))
    (hd : ∀ (a : (Fin m → Fin m → ℂ) → ι → Matrix (Fin m) (Fin m) ℂ) (z : Fin m → Fin m → ℂ),
      (∀ τ, a z τ ∈ KC (ε τ)) → (∀ τ, EntryDiff (fun w => a w τ) z) → ∀ x y,
        DifferentiableAt ℂ (fun w => B x (ϖ (a w) y)) z) :
    IsHolFam ε B ϖ := by
  refine ⟨h0, h1, hm, fun τ => ⟨h0, ?_, fun a ha' b hb => ?_, fun g hg x y => ?_, fun x y z hz => ?_⟩⟩
  · simp only [Pi.mulSingle_one, h1]
  · simp only [Pi.mulSingle_mul]
    exact hm _ _ (mulSingle_mem_KC ha') (mulSingle_mem_KC hb)
  · rw [ha _ (mulSingle_mem_KC hg)]
    simp only [mulSingle_conjTranspose]
  · exact (hd (fun g => Pi.mulSingle τ (Matrix.of g)) z (mulSingle_mem_KC hz)
      (fun τ' => entryDiff_mulSingle τ τ' z) x y).differentiableWithinAt

end KC

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical

theorem fact_diff {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z : E} {D : D7} {m n : ℕ}
    (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ)
    {k : E → D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ} {u : E → D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ}
    (hk : ∀ τ, k z τ ∈ GlobalTheory.Dec.KC (ε τ)) (hu : ∀ τ, IsUnit (u z τ))
    (dk : ∀ τ, EntryDiff (fun w => k w τ) z) (du : ∀ τ, EntryDiff (fun w => u w τ) z) (x y : PolF D m n) :
    DifferentiableAt ℂ (fun w => fockL x (fact ε x₁ x₂ x₃ (k w) (u w) y)) z := by
  simp only [fact, LinearMap.smul_apply, map_smul, smul_eq_mul, AlgHom.toLinearMap_apply]
  refine DifferentiableAt.mul ?_ (CoeffDiff.fock (CoeffDiff.aeval (fun v => ?_) y) x)
  · unfold fchar
    refine diff_prod _ fun τ _ => ?_
    have h := det_ne (hk τ).1
    rw [← detPlus_mul_detMinus (hk τ)] at h
    exact ((((dk τ).affine _ _).zpow_det (left_ne_zero_of_mul h) _).mul
      (((dk τ).affine _ _).zpow_det (right_ne_zero_of_mul h) _)).mul ((du τ).zpow_det (det_ne (hu τ)) _)
  · intro d
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
    refine DifferentiableAt.fun_sum fun a _ => DifferentiableAt.fun_sum fun b _ =>
      DifferentiableAt.mul ?_ (differentiableAt_const _)
    split_ifs
    · exact (dk _ _ _).mul ((du _).inv (hu _) _ _)
    · exact ((dk _).inv (hk _).1 _ _).mul (du _ _ _)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem main : ∀ (D : D7) (m n : ℕ) (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ),
    IsHolFam ε fockL (factK n ε x₁ x₂ x₃) ∧ IsHolFam (fun _ => allPos n) fockL (factU (n := n) ε x₁ x₂ x₃) := by
  intro D m n ε x₁ x₂ x₃
  obtain ⟨h1, hm, ha⟩ := GlobalTheory.T.fockPolynomialAction_one_mul_adjoint D m n ε x₁ x₂ x₃
  have hU : ∀ τ, IsUnit ((1 : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) τ) := fun _ => isUnit_one
  have hK : ∀ τ, (1 : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) τ ∈ GlobalTheory.Dec.KC (ε τ) := fun _ => one_mem_KC
  constructor
  · refine isHolFam_of fockL_aniso ?_ (fun a b ha' hb => ?_) (fun a ha' x y => ?_) (fun a z hz da x y => ?_)
    · rw [← h1, factK]
      congr 1
      funext τ
      simp
    · rw [factK, factK, factK, ← hm _ _ _ _ (fun τ => invT_mem_KC (ha' τ)) (fun τ => invT_mem_KC (hb τ)) hU hU,
        mul_one]
      congr 1
      funext τ
      simp [Matrix.mul_inv_rev]
    · rw [factK, factK, ha _ _ (fun τ => invT_mem_KC (ha' τ)) hU]
      have e1 : (fun τ => (((a τ)⁻¹)ᵀ)ᴴ) = fun τ => (((a τ)ᴴ)⁻¹)ᵀ := by
        funext τ
        rw [← Matrix.conjTranspose_nonsing_inv]
        ext i j
        simp
      have e2 : (fun τ => ((1 : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) τ)ᴴ) = 1 := by
        funext τ
        simp
      rw [e1, e2]
    · exact fact_diff ε x₁ x₂ x₃ (k := fun w τ => ((a w τ)⁻¹)ᵀ) (u := fun _ => 1)
        (fun τ => invT_mem_KC (hz τ)) hU (fun τ => ((da τ).inv (hz τ).1).transpose)
        (fun τ => EntryDiff.const _) x y
  · refine isHolFam_of fockL_aniso h1 (fun a b ha' hb => ?_) (fun a ha' x y => ?_) (fun a z hz da x y => ?_)
    · rw [factU, factU, factU, ← hm _ _ _ _ hK hK (fun τ => (ha' τ).1) (fun τ => (hb τ).1), mul_one]
    · rw [factU, factU, ha _ _ hK (fun τ => (ha' τ).1)]
      have e2 : (fun τ => ((1 : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) τ)ᴴ) = 1 := by
        funext τ
        simp
      rw [e2]
    · exact fact_diff ε x₁ x₂ x₃ (k := fun _ => 1) (u := a) hK (fun τ => (hz τ).1)
        (fun τ => EntryDiff.const _) da x y

end GlobalTheory.FockHol

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockActions_isHolomorphicProductKRepFamily : ∀ (D : D7) (m n : ℕ) (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ), IsHolFam ε fockL (factK n ε x₁ x₂ x₃) ∧ IsHolFam (fun _ => allPos n) fockL (factU (n := n) ε x₁ x₂ x₃) := by
  atlas_forward_decl GlobalTheory.FockHol.main
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.JointHarm.MinorBottom

section Mat

variable {m : ℕ}

def revTail (m p : ℕ) : Equiv.Perm (Fin m) :=
  Function.Involutive.toPerm
    (fun a => if h : (a : ℕ) < p then a else ⟨p + (m - 1 - a), by have := a.isLt; omega⟩)
    (fun a => by
      have := a.isLt
      by_cases h : (a : ℕ) < p
      · simp [h]
      · simp only [h, dite_false]
        rw [dif_neg (by simp)]
        ext
        simp only
        omega)

theorem revTail_val (p : ℕ) (a : Fin m) :
    (revTail m p a : ℕ) = if (a : ℕ) < p then (a : ℕ) else p + (m - 1 - a) := by
  change ((if h : (a : ℕ) < p then a else ⟨p + (m - 1 - a), by have := a.isLt; omega⟩ : Fin m) : ℕ) = _
  by_cases h : (a : ℕ) < p <;> simp [h]

theorem revTail_mul_self (p : ℕ) : revTail m p * revTail m p = 1 := by
  ext a
  have := a.isLt
  simp only [Equiv.Perm.mul_apply, revTail_val, Equiv.Perm.one_apply]
  split_ifs <;> omega

theorem revTail_symm (p : ℕ) : (revTail m p).symm = revTail m p := rfl

theorem comm_Jm_iff (ε : Fin m → Bool) (k : Matrix (Fin m) (Fin m) ℂ) :
    k * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * k ↔ ∀ a b, k a b ≠ 0 → ε a = ε b := by
  rw [← Matrix.ext_iff]
  refine forall₂_congr fun a b => ?_
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
  cases ε a <;> cases ε b <;> simp [neg_eq_iff_add_eq_zero, eq_neg_iff_add_eq_zero]

theorem perm_conj (σ : Equiv.Perm (Fin m)) (hσ : σ.symm = σ) (k : Matrix (Fin m) (Fin m) ℂ) :
    σ.permMatrix ℂ * k * σ.permMatrix ℂ = k.submatrix σ σ := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, hσ]
  rfl

theorem perm_mem_Kset (ε : Fin m → Bool) (σ : Equiv.Perm (Fin m)) (h : ∀ a, ε (σ a) = ε a) :
    σ.permMatrix ℂ ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, (comm_Jm_iff _ _).2 fun a b hab => ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
      ← Matrix.permMatrix_mul]
    simp
  · have : σ a = b := by
      by_contra hne
      exact hab (by simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hne])
    rw [← this, h]

theorem Kset_KC {ε : Fin m → Bool} {k : Matrix (Fin m) (Fin m) ℂ} (h : k ∈ Formalism.REAL.Kset ε) :
    k ∈ GlobalTheory.Dec.KC ε :=
  ⟨(Unitary.toUnits ⟨k, h.1⟩).isUnit, h.2⟩

theorem KC_mul {ε : Fin m → Bool} {a b : Matrix (Fin m) (Fin m) ℂ} (ha : a ∈ GlobalTheory.Dec.KC ε)
    (hb : b ∈ GlobalTheory.Dec.KC ε) : a * b ∈ GlobalTheory.Dec.KC ε :=
  ⟨ha.1.mul hb.1, by rw [Matrix.mul_assoc, hb.2, ← Matrix.mul_assoc, ha.2, Matrix.mul_assoc]⟩

theorem KC_one (ε : Fin m → Bool) : (1 : Matrix (Fin m) (Fin m) ℂ) ∈ GlobalTheory.Dec.KC ε :=
  ⟨isUnit_one, by simp⟩

theorem KC_inv_transpose {ε : Fin m → Bool} {a : Matrix (Fin m) (Fin m) ℂ} (ha : a ∈ GlobalTheory.Dec.KC ε) :
    (a⁻¹)ᵀ ∈ GlobalTheory.Dec.KC ε := by
  have hd := (Matrix.isUnit_iff_isUnit_det a).1 ha.1
  have h1 : a⁻¹ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * a⁻¹ := by
    calc a⁻¹ * Formalism.REAL.Jm ε = a⁻¹ * (Formalism.REAL.Jm ε * a) * a⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hd]
      _ = Formalism.REAL.Jm ε * a⁻¹ := by rw [← ha.2, Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  refine ⟨by simpa using ha.1, (comm_Jm_iff _ _).2 fun x y h => ?_⟩
  exact ((comm_Jm_iff _ _).1 h1 y x h).symm

theorem detP_submatrix (ε : Fin m → Bool) (σ : Equiv.Perm (Fin m)) (h : ∀ a, ε (σ a) = ε a)
    (k : Matrix (Fin m) (Fin m) ℂ) (hk : ∀ a b, k a b ≠ 0 → a ≤ b) :
    detP ε (k.submatrix σ σ) = ∏ a, if ε a then k a a else 1 := by
  have e : (1 / 2 : ℂ) • (1 + Formalism.REAL.Jm ε) * k.submatrix σ σ + (1 / 2 : ℂ) • (1 - Formalism.REAL.Jm ε) =
      (Matrix.of fun a b => if ε a then k a b else if a = b then 1 else 0).submatrix σ σ := by
    ext a b
    simp only [Formalism.REAL.Jm, ← Matrix.diagonal_one, Matrix.diagonal_add, Matrix.diagonal_sub,
      ← Matrix.diagonal_smul, Matrix.add_apply, Matrix.diagonal_mul, Matrix.submatrix_apply,
      Matrix.of_apply, h, Matrix.diagonal_apply, Pi.smul_apply, EmbeddingLike.apply_eq_iff_eq]
    cases ε a <;> by_cases hab : a = b <;> simp [hab] <;> ring
  rw [detP, e, Matrix.det_submatrix_equiv_self, Matrix.det_of_isUpperTriangular]
  · simp
  · intro a b hab
    have h1 : k a b = 0 := by
      by_contra h0
      exact absurd (hk a b h0) (not_le.2 hab)
    have h2 : a ≠ b := ne_of_gt hab
    simp [h1, h2]

theorem detM_submatrix (ε : Fin m → Bool) (σ : Equiv.Perm (Fin m)) (h : ∀ a, ε (σ a) = ε a)
    (k : Matrix (Fin m) (Fin m) ℂ) (hk : ∀ a b, k a b ≠ 0 → a ≤ b) :
    detM ε (k.submatrix σ σ) = ∏ a, if ε a then 1 else k a a := by
  have e : (1 / 2 : ℂ) • (1 - Formalism.REAL.Jm ε) * k.submatrix σ σ + (1 / 2 : ℂ) • (1 + Formalism.REAL.Jm ε) =
      (Matrix.of fun a b => if ε a then (if a = b then 1 else 0) else k a b).submatrix σ σ := by
    ext a b
    simp only [Formalism.REAL.Jm, ← Matrix.diagonal_one, Matrix.diagonal_add, Matrix.diagonal_sub,
      ← Matrix.diagonal_smul, Matrix.add_apply, Matrix.diagonal_mul, Matrix.submatrix_apply,
      Matrix.of_apply, h, Matrix.diagonal_apply, Pi.smul_apply, EmbeddingLike.apply_eq_iff_eq]
    cases ε a <;> by_cases hab : a = b <;> simp [hab] <;> ring
  rw [detM, e, Matrix.det_submatrix_equiv_self, Matrix.det_of_isUpperTriangular]
  · simp
  · intro a b hab
    have h1 : k a b = 0 := by
      by_contra h0
      exact absurd (hk a b h0) (not_le.2 hab)
    have h2 : a ≠ b := ne_of_gt hab
    simp [h1, h2]

theorem det_lo {u : Matrix (Fin m) (Fin m) ℂ} (hu : GlobalTheory.Dec.IsLo u) : u.det = ∏ j, u j j :=
  Matrix.det_of_lowerTriangular u (fun i j h => hu i j (by simpa using h))

theorem inv_transpose_lo {g : Matrix (Fin m) (Fin m) ℂ} (hg : IsUnit g) (hl : GlobalTheory.Dec.IsLo g) :
    (∀ a b, (g⁻¹)ᵀ a b ≠ 0 → a ≤ b) ∧ ∀ a, (g⁻¹)ᵀ a a = (g a a)⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 hg
  letI := hg.invertible
  have hb : g.BlockTriangular OrderDual.toDual := fun i j h => hl i j (by simpa using h)
  have hi := Matrix.blockTriangular_inv_of_blockTriangular hb
  have h0 : ∀ a b, a < b → g⁻¹ a b = 0 := fun a b h => hi (by simpa using h)
  refine ⟨fun a b h => not_lt.1 fun hlt => h (h0 b a hlt), fun a => ?_⟩
  have h1 := congrFun (congrFun (Matrix.nonsing_inv_mul g hd) a) a
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single a] at h1
  · exact eq_inv_of_mul_eq_one_left h1
  · intro b _ hba
    rcases lt_or_gt_of_ne hba with h | h
    · rw [hl b a h, mul_zero]
    · rw [h0 a b h, zero_mul]
  · simp

end Mat

theorem eigen (D : D7) (m n : ℕ) (ε : D.what₂.Tau → Fin m → Bool) (p q : D.what₂.Tau → ℕ)
    (ap am : D.what₂.Tau → ℕ → ℕ) (x₁ x₂ x₃ : D.what₂.Tau → ℤ) (hmn : m ≤ n) (hpq : ∀ τ, p τ + q τ = m)
    (hε : ∀ τ a, ε τ a = decide ((a : ℕ) < p τ)) (hap : ∀ τ a b, a ≤ b → b < p τ → ap τ b ≤ ap τ a)
    (ham : ∀ τ a b, a ≤ b → b < q τ → am τ b ≤ am τ a)
    (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ)
    (hk : ∀ τ, k τ ∈ GlobalTheory.Dec.KC (ε τ)) (hup : ∀ τ a b, k τ a b ≠ 0 → a ≤ b) (hk0 : ∀ τ a, k τ a a ≠ 0)
    (hu : ∀ τ, IsUnit (u τ) ∧ GlobalTheory.Dec.IsLo (u τ)) :
    fact ε x₁ x₂ x₃ k u
        (fact ε x₁ x₂ x₃ (fun τ => (revTail m (p τ)).permMatrix ℂ) 1 (delta p q ap am : PolF D m n)) =
      (∏ τ, (∏ a, k τ a a ^ wtK (p τ) (ap τ) (am τ) (x₁ τ) (x₂ τ) a) *
          ∏ j, u τ j j ^ wtU (p τ) (q τ) (ap τ) (am τ) (x₃ τ) j) •
        fact ε x₁ x₂ x₃ (fun τ => (revTail m (p τ)).permMatrix ℂ) 1 (delta p q ap am : PolF D m n) := by
  obtain ⟨-, hmul, -⟩ := GlobalTheory.JointHarm.fact_one_mul_adj D m n ε x₁ x₂ x₃
  have hσ : ∀ τ a, ε τ (revTail m (p τ) a) = ε τ a := by
    intro τ a
    rw [hε, hε, revTail_val]
    split_ifs with h <;> simp [h]
  set κ : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ := fun τ => (revTail m (p τ)).permMatrix ℂ with hκ
  have hκK : ∀ τ, κ τ ∈ GlobalTheory.Dec.KC (ε τ) := fun τ => Kset_KC (perm_mem_Kset _ _ (hσ τ))
  have hκ2 : κ * κ = 1 := by
    funext τ
    simp [hκ, ← Matrix.permMatrix_mul, revTail_mul_self]
  have hk' : ∀ τ, (κ * k * κ) τ ∈ GlobalTheory.Dec.KC (ε τ) := fun τ => KC_mul (KC_mul (hκK τ) (hk τ)) (hκK τ)
  have hsub : ∀ τ, (κ * k * κ) τ = (k τ).submatrix (revTail m (p τ)) (revTail m (p τ)) :=
    fun τ => perm_conj _ (revTail_symm _) _
  have h1 : ∀ τ, IsUnit ((1 : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) τ) := fun _ => isUnit_one
  have e1 : fact ε x₁ x₂ x₃ k u * fact ε x₁ x₂ x₃ κ 1 =
      fact ε x₁ x₂ x₃ κ 1 * fact ε x₁ x₂ x₃ (κ * k * κ) u := by
    rw [← hmul _ _ _ _ hk hκK (fun τ => (hu τ).1) h1, ← hmul _ _ _ _ hκK hk' h1 (fun τ => (hu τ).1),
      ← mul_assoc, ← mul_assoc, hκ2, one_mul, one_mul, mul_one]
  have hd := GlobalTheory.JointHarm.DeltaEig.fsub_delta D m n ε p q ap am hmn hpq hε hap ham (κ * k * κ) u hk' (by
    intro τ a b hab
    rw [hsub, Matrix.submatrix_apply] at hab
    have h2 : (revTail m (p τ) a : ℕ) ≤ revTail m (p τ) b := hup τ _ _ hab
    have h3 := (comm_Jm_iff _ _).1 (hk τ).2 _ _ hab
    rw [hσ, hσ, hε, hε, decide_eq_decide] at h3
    rw [revTail_val, revTail_val] at h2
    have := a.isLt
    have := b.isLt
    simp only [Fin.le_def]
    split_ifs at h2 <;> omega) hu
  rw [← Module.End.mul_apply, e1, Module.End.mul_apply, ← map_smul]
  congr 1
  rw [fact, LinearMap.smul_apply, AlgHom.toLinearMap_apply, hd, smul_smul, fchar, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hu0 : ∀ j, u τ j j ≠ 0 := by
    have := ((Matrix.isUnit_iff_isUnit_det _).1 (hu τ).1).ne_zero
    rw [det_lo (hu τ).2, Finset.prod_ne_zero_iff] at this
    exact fun j => this j (Finset.mem_univ _)
  rw [hsub, detP_submatrix _ _ (hσ τ) _ (hup τ), detM_submatrix _ _ (hσ τ) _ (hup τ), det_lo (hu τ).2,
    mul_mul_mul_comm, ← Finset.prod_zpow, ← Finset.prod_zpow, ← Finset.prod_zpow,
    ← Finset.prod_mul_distrib]
  congr 1
  · rw [← Equiv.prod_comp (revTail m (p τ)) (fun a => (if ε τ a then k τ a a else 1) ^ x₁ τ *
        (if ε τ a then 1 else k τ a a) ^ x₂ τ),
      ← Equiv.prod_comp (revTail m (p τ)) (fun a => k τ a a ^ wtK (p τ) (ap τ) (am τ) (x₁ τ) (x₂ τ) a),
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    have := a.isLt
    have hp := hpq τ
    rw [hσ, hε, Matrix.submatrix_apply, wtK, revTail_val]
    by_cases h : (a : ℕ) < p τ
    · simp [h, zpow_add₀ (hk0 τ _), mul_comm]
    · have h4 : m - 1 - (p τ + (m - 1 - a)) = a - p τ := by omega
      simp only [h, if_false, decide_false, Bool.false_eq_true, _root_.one_zpow, one_mul, h4]
      rw [if_neg (by omega), zpow_add₀ (hk0 τ _), mul_comm]
  · rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← zpow_add₀ (hu0 j)]
    congr 1
    simp only [wtU]
    ring

theorem isUnit_diag_exp {n : ℕ} (θ : Fin n → ℝ) :
    IsUnit (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  exact fun a _ => Complex.exp_ne_zero _

theorem mulSingle_cases {ι M : Type} [DecidableEq ι] [One M] (P : ι → M → Prop) (τ : ι) (g : M) (hg : P τ g)
    (h1 : ∀ i, P i 1) (i : ι) : P i ((Pi.mulSingle τ g : ι → M) i) := by
  by_cases h : i = τ
  · subst h
    simpa using hg
  · simpa [h] using h1 i

theorem isLo_one (n : ℕ) : GlobalTheory.Dec.IsLo (1 : Matrix (Fin n) (Fin n) ℂ) :=
  fun _ _ h => Matrix.one_apply_ne (ne_of_lt h)

theorem exists_joint_bottom : ∀ (D : D7) (m n : ℕ) (ε : D.what₂.Tau → Fin m → Bool) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (x₁ x₂ x₃ : D.what₂.Tau → ℤ), m ≤ n → (∀ τ, p τ + q τ = m) → (∀ τ a, ε τ a = decide ((a : ℕ) < p τ)) → (∀ τ a b, a ≤ b → b < p τ → ap τ b ≤ ap τ a) → (∀ τ a b, a ≤ b → b < q τ → am τ b ≤ am τ a) → ∃ (κ : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (Δ' : PolF D m n), (∀ τ, κ τ ∈ Formalism.REAL.Kset (ε τ)) ∧ fact ε x₁ x₂ x₃ κ 1 Δ' = delta p q ap am ∧ IsBotFam ε (factK n ε x₁ x₂ x₃) (fun τ a => -(wtK (p τ) (ap τ) (am τ) (x₁ τ) (x₂ τ) a : ℝ)) Δ' ∧ IsBotFam (fun _ => allPos n) (factU ε x₁ x₂ x₃) (fun τ j => (wtU (p τ) (q τ) (ap τ) (am τ) (x₃ τ) j : ℝ)) Δ' := by
  intro D m n ε p q ap am x₁ x₂ x₃ hmn hpq hε hap ham
  have hE := eigen D m n ε p q ap am x₁ x₂ x₃ hmn hpq hε hap ham
  obtain ⟨hone, hmul, -⟩ := GlobalTheory.JointHarm.fact_one_mul_adj D m n ε x₁ x₂ x₃
  have hσ : ∀ τ a, ε τ (revTail m (p τ) a) = ε τ a := by
    intro τ a
    rw [hε, hε, revTail_val]
    split_ifs with h <;> simp [h]
  set κ : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ := fun τ => (revTail m (p τ)).permMatrix ℂ with hκ
  have hκK : ∀ τ, κ τ ∈ Formalism.REAL.Kset (ε τ) := fun τ => perm_mem_Kset _ _ (hσ τ)
  have hκ2 : κ * κ = 1 := by
    funext τ
    simp [hκ, ← Matrix.permMatrix_mul, revTail_mul_self]
  have h1 : ∀ τ, IsUnit ((1 : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) τ) := fun _ => isUnit_one
  set Δ' : PolF D m n := fact ε x₁ x₂ x₃ κ 1 (delta p q ap am : PolF D m n) with hΔ
  have hK : ∀ τ (g : Matrix (Fin m) (Fin m) ℂ), g ∈ GlobalTheory.Dec.KC (ε τ) → GlobalTheory.Dec.IsLo g →
      factK n ε x₁ x₂ x₃ (Pi.mulSingle τ g) Δ' =
        (∏ a, (g a a)⁻¹ ^ wtK (p τ) (ap τ) (am τ) (x₁ τ) (x₂ τ) a) • Δ' := by
    intro τ g hg hl
    have hg' := mulSingle_cases (fun i g => g ∈ GlobalTheory.Dec.KC (ε i) ∧ GlobalTheory.Dec.IsLo g) τ g ⟨hg, hl⟩
      (fun i => ⟨KC_one _, isLo_one _⟩)
    have hi := fun i => inv_transpose_lo (hg' i).1.1 (hg' i).2
    rw [factK, hE _ 1 (fun i => KC_inv_transpose (hg' i).1) (fun i => (hi i).1) ?_
      (fun i => ⟨isUnit_one, isLo_one _⟩)]
    · congr 1
      rw [Finset.prod_eq_single τ]
      · simp only [(hi τ).2]
        simp
      · intro i _ hne
        simp [hne]
      · simp
    · intro i a
      have := ((Matrix.isUnit_iff_isUnit_det _).1 (hg' i).1.1).ne_zero
      rw [det_lo (hg' i).2, Finset.prod_ne_zero_iff] at this
      rw [(hi i).2]
      exact inv_ne_zero (this a (Finset.mem_univ _))
  have hU : ∀ τ (g : Matrix (Fin n) (Fin n) ℂ), IsUnit g → GlobalTheory.Dec.IsLo g →
      factU ε x₁ x₂ x₃ (Pi.mulSingle τ g) Δ' =
        (∏ j, g j j ^ wtU (p τ) (q τ) (ap τ) (am τ) (x₃ τ) j) • Δ' := by
    intro τ g hg hl
    have hg' := mulSingle_cases (fun _ g => IsUnit g ∧ GlobalTheory.Dec.IsLo g) τ g ⟨hg, hl⟩
      (fun i => ⟨isUnit_one, isLo_one _⟩)
    rw [factU, hE 1 _ (fun i => KC_one _) ?_ (fun i a => by simp) hg']
    · congr 1
      rw [Finset.prod_eq_single τ]
      · simp
      · intro i _ hne
        simp [hne]
      · simp
    · intro i a b hab
      by_contra h
      exact hab (Matrix.one_apply_ne (fun e => h e.le))
  have hdl : ∀ {l : ℕ} (v : Fin l → ℂ), GlobalTheory.Dec.IsLo (Matrix.diagonal v) :=
    fun v _ _ h => Matrix.diagonal_apply_ne _ (ne_of_lt h)
  refine ⟨κ, Δ', hκK, ?_, fun τ => ⟨fun g hg hl => ?_, fun θ => ?_⟩, fun τ => ⟨fun g hg hl => ?_, fun θ => ?_⟩⟩
  · rw [hΔ, ← Module.End.mul_apply, ← hmul _ _ _ _ (fun τ => Kset_KC (hκK τ)) (fun τ => Kset_KC (hκK τ)) h1 h1,
      hκ2, mul_one, hone, Module.End.one_apply]
  · have := hK τ g hg (fun i j h => (hl i j).1 h)
    simpa [fun a => (hl a a).2 rfl] using this
  · refine (hK τ _ ⟨isUnit_diag_exp θ, ?_⟩ (hdl _)).trans ?_
    · simp [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]
    · congr 1
      simp only [Matrix.diagonal_apply_eq, ← Complex.exp_neg, ← Complex.exp_int_mul, ← Complex.exp_sum]
      congr 1
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by ring
  · have := hU τ g hg.1 (fun i j h => (hl i j).1 h)
    simpa [fun a => (hl a a).2 rfl] using this
  · refine (hU τ _ (isUnit_diag_exp θ) (hdl _)).trans ?_
    congr 1
    simp only [Matrix.diagonal_apply_eq, ← Complex.exp_int_mul, ← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring

end GlobalTheory.JointHarm.MinorBottom

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_minorProduct_translate_jointLowestWeight : ∀ (D : D7) (m n : ℕ) (ε : D.what₂.Tau → Fin m → Bool) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (x₁ x₂ x₃ : D.what₂.Tau → ℤ), m ≤ n → (∀ τ, p τ + q τ = m) → (∀ τ a, ε τ a = decide ((a : ℕ) < p τ)) → (∀ τ a b, a ≤ b → b < p τ → ap τ b ≤ ap τ a) → (∀ τ a b, a ≤ b → b < q τ → am τ b ≤ am τ a) → ∃ (κ : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (Δ' : PolF D m n), (∀ τ, κ τ ∈ Formalism.REAL.Kset (ε τ)) ∧ fact ε x₁ x₂ x₃ κ 1 Δ' = delta p q ap am ∧ IsBotFam ε (factK n ε x₁ x₂ x₃) (fun τ a => -(wtK (p τ) (ap τ) (am τ) (x₁ τ) (x₂ τ) a : ℝ)) Δ' ∧ IsBotFam (fun _ => allPos n) (factU ε x₁ x₂ x₃) (fun τ j => (wtU (p τ) (q τ) (ap τ) (am τ) (x₃ τ) j : ℝ)) Δ' := by
  atlas_forward_decl GlobalTheory.JointHarm.MinorBottom.exists_joint_bottom
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.JointHarm

theorem vhol_diff_prod {E κ : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {s : Set E} (u : Finset κ)
    (f : κ → E → ℂ) (h : ∀ i, DifferentiableOn ℂ (f i) s) :
    DifferentiableOn ℂ (fun z => ∏ i ∈ u, f i z) s := by
  induction u using Finset.induction_on with
  | empty => simpa using differentiableOn_const _
  | insert a u ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a).mul ih

theorem vhol_diff_det {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ} {s : Set E}
    (A : E → Matrix (Fin n) (Fin n) ℂ) (h : ∀ i j, DifferentiableOn ℂ (fun z => A z i j) s) :
    DifferentiableOn ℂ (fun z => (A z).det) s := by
  simp only [Matrix.det_apply']
  refine DifferentiableOn.fun_sum fun σ _ => DifferentiableOn.const_mul ?_ _
  exact vhol_diff_prod _ (fun i z => A z (σ i) i) fun i => h _ _

theorem vhol_diff_inv {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ} {s : Set E}
    (A : E → Matrix (Fin n) (Fin n) ℂ) (h : ∀ i j, DifferentiableOn ℂ (fun z => A z i j) s)
    (h0 : ∀ z ∈ s, (A z).det ≠ 0) (i j : Fin n) :
    DifferentiableOn ℂ (fun z => (A z)⁻¹ i j) s := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  refine ((vhol_diff_det A h).inv h0).mul (vhol_diff_det _ fun a b => ?_)
  by_cases ha : a = j
  · simp only [Matrix.updateRow_apply, if_pos ha]
    exact differentiableOn_const _
  · simp only [Matrix.updateRow_apply, if_neg ha]
    exact h a b

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem vhol_diff_fock {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {s : Set E}
    (U : E → ι → Matrix (Fin n) (Fin n) ℂ) (h : ∀ τ i j, DifferentiableOn ℂ (fun z => U z τ i j) s)
    (x y : Pol ℂ ι n) :
    DifferentiableOn ℂ (fun z => fockL x (Formalism.GradedWeylDivisibility.blockAct ℂ (U z) y)) s := by
  induction y using MvPolynomial.induction_on generalizing x with
  | C a =>
    simp only [MvPolynomial.algHom_C]
    exact differentiableOn_const _
  | add p q hp hq =>
    simp only [map_add]
    exact (hp x).add (hq x)
  | mul_X p v hp =>
    have e1 : ∀ z, Formalism.GradedWeylDivisibility.blockAct ℂ (U z) (p * MvPolynomial.X v) =
        ∑ b : Fin n, U z v.1 v.2.1 b • (MvPolynomial.X (v.1, (b, v.2.2)) * Formalism.GradedWeylDivisibility.blockAct ℂ (U z) p) := by
      intro z
      rw [map_mul, blockAct_X, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [MvPolynomial.smul_eq_C_mul]; ring
    simp only [e1, map_sum, map_smul, ← fockL_pderiv_X, smul_eq_mul]
    exact DifferentiableOn.fun_sum fun b _ => (h _ _ _).mul (hp _)

theorem vhol_aniso {σ : Type} (x : MvPolynomial σ ℂ) (hx : fockL x x = 0) : x = 0 := by
  rw [fockL_apply, fockS] at hx
  have e : ∀ m, star (x.coeff m) * x.coeff m * (mfact m : ℂ) =
      ((Complex.normSq (x.coeff m) * (mfact m : ℝ) : ℝ) : ℂ) := by
    intro m
    rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
    simp
  simp only [e] at hx
  rw [← Complex.ofReal_sum, Complex.ofReal_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg fun m _ => mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)] at hx
  ext m
  by_contra hm
  have h1 := hx m (MvPolynomial.mem_support_iff.2 hm)
  have h2 : 0 < mfact m := Finset.prod_pos fun k _ => Nat.factorial_pos _
  rcases mul_eq_zero.1 h1 with h | h
  · exact hm (Complex.normSq_eq_zero.1 h)
  · exact h2.ne' (by exact_mod_cast h)

theorem vhol_one (lam : ι → DomWeight n) : vact lam 1 = 1 := by
  unfold vact
  simp only [Pi.one_apply, Matrix.det_one, _root_.one_zpow, Finset.prod_const_one, one_smul, inv_one, blockAct_one]
  rfl

theorem vhol_mul (lam : ι → DomWeight n) (a b : ι → Matrix (Fin n) (Fin n) ℂ) :
    vact lam (a * b) = vact lam a * vact lam b := by
  apply LinearMap.ext
  intro F
  have := congrArg (fun φ => φ F) (blockAct_comp (fun τ => (a τ)⁻¹) (fun τ => (b τ)⁻¹))
  simp only [AlgHom.comp_apply] at this
  simp only [vact, Pi.mul_apply, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib, Matrix.mul_inv_rev,
    Module.End.mul_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_smul, this]
  rw [mul_comm]

theorem vhol_adj (lam : ι → DomWeight n) (a : ι → Matrix (Fin n) (Fin n) ℂ) (x y : Pol ℂ ι n) :
    fockL (vact lam a x) y = fockL x (vact lam (fun τ => (a τ)ᴴ) y) := by
  simp only [vact, LinearMap.smul_apply, AlgHom.toLinearMap_apply, LinearMap.map_smulₛₗ, map_smul,
    fockL_blockAct_adj, Matrix.conjTranspose_nonsing_inv, Matrix.det_conjTranspose, starRingEnd_apply, star_prod,
    star_zpow₀, RingHom.id_apply]

theorem vhol_units (lam : ι → DomWeight n) (G : ι → GL (Fin n) ℂ) :
    vact lam (fun τ => (G τ : Matrix (Fin n) (Fin n) ℂ)) = actP lam (invTrK G) := by
  unfold vact actP trAct
  rw [detTw_eq]
  simp only [invTrK_coe, Matrix.transpose_transpose, Matrix.det_transpose, Matrix.coe_units_inv,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv', _root_.zpow_neg, _root_.inv_zpow]

theorem vhol_ext (lam : ι → DomWeight n) (τ : ι) (g : GL (Fin n) ℂ) (c : ℂ)
    (h : sqAct ℂ n (lam τ) (inside₂ ℂ n g) (extremal ℂ n (lam τ)) = c • extremal ℂ n (lam τ)) :
    vact lam (Pi.mulSingle τ (g : Matrix (Fin n) (Fin n) ℂ)) (ten fun τ => extremal ℂ n (lam τ)) =
      c • ten fun τ => extremal ℂ n (lam τ) := by
  have e : (Pi.mulSingle τ (g : Matrix (Fin n) (Fin n) ℂ) : ι → Matrix (Fin n) (Fin n) ℂ) =
      fun σ => ((Pi.mulSingle τ g : ι → GL (Fin n) ℂ) σ : Matrix (Fin n) (Fin n) ℂ) := by
    funext σ
    by_cases hσ : σ = τ
    · subst hσ; simp
    · simp [hσ]
  rw [e, vhol_units, actTen]
  unfold ten
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ),
    ← Finset.mul_prod_erase _ (fun σ => Formalism.GradedWeylDivisibility.blockEmb ℂ σ (extremal ℂ n (lam σ))) (Finset.mem_univ τ),
    ← smul_mul_assoc]
  congr 1
  · rw [← map_smul, ← h]
    show Formalism.GradedWeylDivisibility.blockEmb ℂ τ (sqAct ℂ n (lam τ) (inside₂ ℂ n ((Pi.mulSingle τ g : ι → GL (Fin n) ℂ) τ)) _) = _
    rw [Pi.mulSingle_eq_same]
  · refine Finset.prod_congr rfl fun σ hσ => ?_
    refine congrArg (Formalism.GradedWeylDivisibility.blockEmb ℂ σ) ?_
    refine (factSqHighestWeight ℂ n (lam σ)).2 _ ?_ ?_
    · rw [invTrK_coe, Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hσ)]
      simpa using Matrix.blockTriangular_one
    · intro a
      rw [invTrK_coe, Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hσ)]
      simp

theorem vhol_lo_inv (g : Matrix (Fin n) (Fin n) ℂ) (hg : IsUnit g) (h : IsLoUni g) :
    (g⁻¹)ᵀ.BlockTriangular id ∧ ∀ a, g⁻¹ a a = 1 := by
  have h1 : gᵀ.BlockTriangular id := fun i j hij => (h j i).1 hij
  have hu : IsUnit gᵀ := (Matrix.isUnit_transpose g).2 hg
  obtain ⟨inst⟩ := hu.nonempty_invertible
  have h2 : (gᵀ)⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular h1
  rw [← Matrix.transpose_nonsing_inv] at h2
  refine ⟨h2, fun a => ?_⟩
  have h3 := congrFun (congrFun (Matrix.mul_nonsing_inv g ((Matrix.isUnit_iff_isUnit_det g).1 hg)) a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a, (h a a).2 rfl, one_mul, Matrix.one_apply_eq] at h3
  · exact h3
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with hlt | hlt
    · have : g⁻¹ b a = 0 := h2 (i := a) (j := b) hlt
      rw [this, mul_zero]
    · rw [(h a b).1 hlt, zero_mul]
  · simp

theorem vact_isHolFam_isBotFam : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n),
    IsHolFam (fun _ => allPos n) fockL (vact lam) ∧
    IsBotFam (fun _ => allPos n) (vact lam) (fun τ j => -((lam τ).w j : ℝ)) (ten fun τ => extremal ℂ n (lam τ)) ∧
    (ten fun τ => extremal ℂ n (lam τ)) ≠ 0 ∧ (ten fun τ => extremal ℂ n (lam τ)) ∈ VV ℂ lam := by
  intro ι _ n lam
  refine ⟨⟨vhol_aniso, vhol_one lam, fun a b _ _ => vhol_mul lam a b, fun τ =>
    ⟨vhol_aniso, ?_, fun a _ b _ => ?_, fun g _ x y => ?_, fun x y => ?_⟩⟩, fun τ => ⟨fun g hg hl => ?_, fun θ => ?_⟩,
    ?_, ?_⟩
  · show vact lam (Pi.mulSingle τ 1) = 1
    rw [Pi.mulSingle_one, vhol_one]
  · show vact lam (Pi.mulSingle τ (a * b)) = _
    rw [Pi.mulSingle_mul, vhol_mul]
  · show fockL (vact lam (Pi.mulSingle τ g) x) y = fockL x (vact lam (Pi.mulSingle τ gᴴ) y)
    rw [vhol_adj]
    refine congrArg (fun u => fockL x (vact lam u y)) ?_
    funext σ
    by_cases hσ : σ = τ
    · subst hσ; simp
    · simp [hσ]
  · have h1 : ∀ σ i j, DifferentiableOn ℂ (fun g : Fin n → Fin n → ℂ =>
        (Pi.mulSingle τ (Matrix.of g) : ι → Matrix (Fin n) (Fin n) ℂ) σ i j)
        {g | Matrix.of g ∈ GlobalTheory.Dec.KC (allPos n)} := by
      intro σ i j
      by_cases hσ : σ = τ
      · subst hσ
        simp only [Pi.mulSingle_eq_same, Matrix.of_apply]
        fun_prop
      · simp only [Pi.mulSingle_eq_of_ne hσ]
        exact differentiableOn_const _
    have h0 : ∀ σ, ∀ g ∈ {g : Fin n → Fin n → ℂ | Matrix.of g ∈ GlobalTheory.Dec.KC (allPos n)},
        ((Pi.mulSingle τ (Matrix.of g) : ι → Matrix (Fin n) (Fin n) ℂ) σ).det ≠ 0 := by
      intro σ g hg
      by_cases hσ : σ = τ
      · subst hσ
        rw [Pi.mulSingle_eq_same]
        exact ((Matrix.isUnit_iff_isUnit_det _).1 hg.1).ne_zero
      · rw [Pi.mulSingle_eq_of_ne hσ]
        simp
    simp only [vact, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_eq_mul]
    refine DifferentiableOn.mul (vhol_diff_prod _ (fun σ (g : Fin n → Fin n → ℂ) =>
      ((Pi.mulSingle τ (Matrix.of g) : ι → Matrix (Fin n) (Fin n) ℂ) σ).det ^ (-(lam σ).detShift)) fun σ => ?_)
      (vhol_diff_fock _ (fun σ => vhol_diff_inv _ (h1 σ) (h0 σ)) x y)
    exact (vhol_diff_det _ (h1 σ)).zpow (Or.inl (h0 σ))
  · obtain ⟨h2, h3⟩ := vhol_lo_inv g hg.1 hl
    obtain ⟨G, rfl⟩ := hg.1
    have := vhol_ext lam τ G 1 (by
      rw [one_smul]
      refine (factSqHighestWeight ℂ n (lam τ)).2 _ ?_ ?_
      · simpa [inside₂] using h2
      · simpa [inside₂] using h3)
    rwa [one_smul] at this
  · let t : Fin n → ℂˣ := fun a => Units.mk0 (Complex.exp ((θ a : ℂ) * Complex.I)) (Complex.exp_ne_zero _)
    have e1 : ((diagGL ℂ n t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
        Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I) := rfl
    have e2 : inside₂ ℂ n (diagGL ℂ n t) = diagGL ℂ n t⁻¹ := by
      apply Units.ext
      exact Matrix.diagonal_transpose _
    show vact lam (Pi.mulSingle τ _) _ = _
    rw [← e1]
    apply vhol_ext
    rw [e2, (factSqHighestWeight ℂ n (lam τ)).1]
    congr 1
    rw [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum, Units.coe_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp only [t, Pi.inv_apply, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, Units.val_mk0,
      ← Complex.exp_neg, ← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  · refine Finset.prod_ne_zero_iff.2 fun τ _ h => Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl (lam τ).natW ?_
    exact MvPolynomial.rename_injective (fun v : Fin n × Fin n => (τ, v)) (fun _ _ h => congrArg Prod.snd h)
      (h.trans (map_zero _).symm)
  · exact Submodule.subset_span ⟨fun τ => extremal ℂ n (lam τ),
      fun τ => Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl _ (natW_antitone (lam τ)), rfl⟩

end GlobalTheory.JointHarm

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameFunctionAction_holomorphic_extremal_lowest : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), IsHolFam (fun _ => allPos n) fockL (vact lam) ∧ IsBotFam (fun _ => allPos n) (vact lam) (fun τ j => -((lam τ).w j : ℝ)) (ten fun τ => extremal ℂ n (lam τ)) ∧ (ten fun τ => extremal ℂ n (lam τ)) ≠ 0 ∧ (ten fun τ => extremal ℂ n (lam τ)) ∈ VV ℂ lam := by
  atlas_forward_decl GlobalTheory.JointHarm.vact_isHolFam_isBotFam
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.JointHarm

theorem cyc_rowAct_rowAct {k n : ℕ} (g h : Matrix (Fin k) (Fin k) ℂ) (F : MvPolynomial (Fin k × Fin n) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ g (Formalism.GradedWeylDivisibility.rowAct ℂ h F) = Formalism.GradedWeylDivisibility.rowAct ℂ (h * g) F := by
  have : (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) g).comp (Formalism.GradedWeylDivisibility.rowAct ℂ h) = Formalism.GradedWeylDivisibility.rowAct ℂ (h * g) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.algHom_C,
      Matrix.mul_apply]
    simp only [MvPolynomial.algebraMap_eq, Finset.mul_sum, Finset.sum_mul, ← MvPolynomial.C_mul]
    rw [Finset.sum_comm]
    simp [MvPolynomial.C_mul, mul_assoc]
  rw [← this]; rfl

theorem cyc_rowAct_one {k n : ℕ} (F : MvPolynomial (Fin k × Fin n) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (1 : Matrix (Fin k) (Fin k) ℂ) F = F := by
  have : Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (1 : Matrix (Fin k) (Fin k) ℂ) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X, Matrix.one_apply, AlgHom.id_apply]
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [this]; rfl

theorem nablaSq_le_span_unitary (n : ℕ) (mu : DomWeight n) :
    nablaSq ℂ n mu ≤ Submodule.span ℂ
      {F | ∃ u ∈ Matrix.unitaryGroup (Fin n) ℂ, F = Formalism.GradedWeylDivisibility.rowAct ℂ u (extremal ℂ n mu)} := by
  have hν : Antitone mu.natW := (factNatW n mu).1
  have hmem : extremal ℂ n mu ∈ nablaSq ℂ n mu := Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl mu.natW hν
  set M := Submodule.span ℂ
      {F | ∃ u ∈ Matrix.unitaryGroup (Fin n) ℂ, F = Formalism.GradedWeylDivisibility.rowAct ℂ u (extremal ℂ n mu)} with hM
  have hle : M ≤ nablaSq ℂ n mu := by
    rw [hM, Submodule.span_le]
    rintro _ ⟨u, -, rfl⟩
    exact Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n _ _ _ hmem
  have hU : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ f ∈ M, Formalism.GradedWeylDivisibility.rowAct ℂ u f ∈ M := by
    intro u hu f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      rw [cyc_rowAct_rowAct]
      exact Submodule.subset_span ⟨v * u, mul_mem hv hu, rfl⟩
    | zero => rw [map_zero]; exact M.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact M.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact M.smul_mem c hx
  have hne : M ≠ ⊥ := by
    intro e
    have h1 : extremal ℂ n mu ∈ M := Submodule.subset_span ⟨1, one_mem _, (cyc_rowAct_one _).symm⟩
    rw [e, Submodule.mem_bot] at h1
    exact Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl mu.natW h1
  exact GlobalTheory.Branching.dualWeyl_le_of_rowDivClosed le_rfl mu.natW hν M hle
    (GlobalTheory.Branching.rowDivClosed_of_rowAct_stable M (GlobalTheory.Branching.rowAct_mem_of_unitary_stable M hU)) hne

theorem VV_le_span_vact_extremal : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), VV ℂ lam ≤ Submodule.span ℂ {F | ∃ u : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, u τ ∈ Formalism.REAL.Kset (allPos n)) ∧ F = vact lam u (ten fun τ => extremal ℂ n (lam τ))} := by
  intro ι _ n lam
  unfold VV Formalism.GradedWeylDivisibility.tensorLat
  rw [Submodule.span_le]
  rintro _ ⟨f, hf, rfl⟩
  choose m c g hg using fun τ => Submodule.mem_span_set'.1 (nablaSq_le_span_unitary n (lam τ) (hf τ))
  choose v hv hgv using fun τ i => (g τ i).2
  have e : ∏ τ, Formalism.GradedWeylDivisibility.blockEmb ℂ τ (f τ) =
      ∑ p ∈ Fintype.piFinset (fun τ => (Finset.univ : Finset (Fin (m τ)))),
        (∏ τ, c τ (p τ)) • ∏ τ, Formalism.GradedWeylDivisibility.blockEmb ℂ τ (g τ (p τ) : MvPolynomial (Fin n × Fin n) ℂ) := by
    simp only [← hg, map_sum, map_smul]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.prod_smul]
  rw [e, SetLike.mem_coe]
  refine Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ ?_
  set u : ι → Matrix (Fin n) (Fin n) ℂ := fun τ => star (v τ (p τ)) with hu
  have huU : ∀ τ, u τ ∈ Matrix.unitaryGroup (Fin n) ℂ := fun τ => Unitary.star_mem (hv τ (p τ))
  have hinv : ∀ τ, (u τ)⁻¹ = v τ (p τ) := fun τ =>
    Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff'.1 (hv τ (p τ)))
  have hdet : (∏ τ, (u τ).det ^ (-(lam τ).detShift)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ ?_
    exact (Matrix.UnitaryGroup.det_isUnit ⟨u τ, huU τ⟩).ne_zero
  rw [← Submodule.smul_mem_iff _ hdet]
  refine Submodule.subset_span ⟨u, fun τ => ⟨huU τ, ?_⟩, ?_⟩
  · have : Formalism.REAL.Jm (allPos n) = 1 := by
      simp [Formalism.REAL.Jm, allPos]
    rw [this, mul_one, one_mul]
  · simp only [vact, ten, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [(Formalism.GradedWeylDivisibility.blockActTensor ℂ ℂ ι n n _).1, hinv, hgv]

end GlobalTheory.JointHarm
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficientSpace_le_span_unitary_orbit_extremal : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), VV ℂ lam ≤ Submodule.span ℂ {F | ∃ u : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, u τ ∈ Formalism.REAL.Kset (allPos n)) ∧ F = vact lam u (ten fun τ => extremal ℂ n (lam τ))} := by
  atlas_forward_decl GlobalTheory.JointHarm.VV_le_span_vact_extremal
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomialModel_coefficientSpace_realPoints : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (c : CoefA V) (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.coef.W), IsInfFam θ → c.Is → Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam) → ∀ BS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsUnit (BS τ)) → ∃ j : c.W →ₗ[ℂ] Pol ℂ D.what₂.Tau V.rank, LinearMap.range j = VV ℂ lam ∧ ∀ u ∈ GinfC V, ∀ w, j (c.ρ u w) = vact lam (fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt V u) * BS τ) (j w) := by
  first | exact @GlobalTheory.CoefReal.exists_poly_model | exact GlobalTheory.CoefReal.exists_poly_model | (intros; apply GlobalTheory.CoefReal.exists_poly_model <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftInfinityTypes_atRealPlace : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → ∀ (i : Fin D.R.m) (t : T) (τ : D.what₂.Tau), GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.InfTypesAt L i t τ := by
  first | exact @GlobalTheory.PairInfTypes.infTypesAt | exact GlobalTheory.PairInfTypes.infTypesAt | (intros; apply GlobalTheory.PairInfTypes.infTypesAt <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.JointHarm

theorem isThetaFunO_of_isThetaAt {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) {S T : HSp D} {e : AE D} {Λ : AddSubgroup (WO S T)} {c : ℂ} {f₀ Φ f : WO S T → ℂ}
    (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f) (h₀ : IsThetaFunO ψ S T f₀) :
    IsThetaFunO ψ S T f := by
  let U : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {g | IsThetaFunO ψ S T g}
      add_mem' := fun ha hb => GlobalTheory.OrientedHeis.theta_add ha hb
      zero_mem' := GlobalTheory.OrientedHeis.theta_zero
      smul_mem' := fun c _ hg => GlobalTheory.OrientedHeis.theta_smul c hg }
  show f ∈ U
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro l hl
  let A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) :=
    LinearMap.pi fun w => l ∘ₗ GlobalTheory.SplitScalar.heisL ψ S T w
  have hA0 : ∀ g w, A g w = l (heisO ψ S T w g) := fun _ _ => rfl
  have hA : ∀ u g, A (heisO ψ S T u g) = heisO ψ S T u (A g) := fun u g => by
    funext w
    rw [hA0, GlobalTheory.OrientedHeis.heisO_heisO, map_smul]
    rfl
  have hf0 : A f₀ = 0 := by
    funext w
    exact (Submodule.mem_dualAnnihilator l).1 hl _ ((GlobalTheory.ThetaClosed.thetaClosed ψ θ hψ hθ S T f₀ h₀).1 w)
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  have hT' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ (Tm + A ∘ₗ Tm) :=
    { trans := fun Φ hΦ x hx => by
        rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
          hT.trans Φ hΦ x hx, hA x]
        exact ((GlobalTheory.SplitScalar.heisL ψ S T x).map_add _ _).symm
      modul := fun Φ hΦ y hy => by
        rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
          hT.modul Φ hΦ y hy, hA y]
        exact ((GlobalTheory.SplitScalar.heisL ψ S T y).map_add _ _).symm
      vac := by
        rw [LinearMap.add_apply, LinearMap.comp_apply, hT.vac, hf0, add_zero] }
  have e1 : f = Tm Φ := hall Tm hT
  have e2 : f = (Tm + A ∘ₗ Tm) Φ := hall _ hT'
  rw [LinearMap.add_apply, LinearMap.comp_apply, ← e1] at e2
  have e3 := congrFun (left_eq_add.1 e2) 0
  rwa [hA0, GlobalTheory.OrientedHeis.heisO_zero] at e3

theorem compAt_mt_one' {D : D7} (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) :
    compAt θ τ (Formalism.L2.Theta.mt V 1) = 1 :=
  (GlobalTheory.WeilDeriv.compAt_mt_eq_infMat θ τ V 1).trans (GlobalTheory.PointAtPlaceHom.infMat_one V _)

section Mat

variable {m : ℕ} {ε : Fin m → Bool}

theorem mem_KC_of_K {k : Matrix (Fin m) (Fin m) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) : k ∈ GlobalTheory.Dec.KC ε :=
  ⟨⟨⟨k, star k, Unitary.mul_star_self_of_mem hk.1, Unitary.star_mul_self_of_mem hk.1⟩, rfl⟩, hk.2⟩

theorem one_mem_K : (1 : Matrix (Fin m) (Fin m) ℂ) ∈ Formalism.REAL.Kset ε :=
  ⟨Submonoid.one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩

theorem invT_mem_KC {g : Matrix (Fin m) (Fin m) ℂ} (hg : g ∈ GlobalTheory.Dec.KC ε) : (g⁻¹)ᵀ ∈ GlobalTheory.Dec.KC ε := by
  obtain ⟨_inst⟩ := hg.1.nonempty_invertible
  refine ⟨(Matrix.isUnit_transpose _).2 (Matrix.isUnit_nonsing_inv_iff.2 hg.1), ?_⟩
  have hc : g⁻¹ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * g⁻¹ := by
    calc g⁻¹ * Formalism.REAL.Jm ε = g⁻¹ * (Formalism.REAL.Jm ε * g) * g⁻¹ := by
          rw [mul_assoc, mul_assoc, Matrix.mul_inv_of_invertible, mul_one]
      _ = Formalism.REAL.Jm ε * g⁻¹ := by
          rw [← hg.2, ← mul_assoc, Matrix.inv_mul_of_invertible, one_mul]
  have hJ : (Formalism.REAL.Jm ε)ᵀ = Formalism.REAL.Jm ε := Matrix.diagonal_transpose _
  have := congrArg Matrix.transpose hc
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hJ] at this
  exact this.symm

theorem invT_conj {k : Matrix (Fin m) (Fin m) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin m) ℂ) :
    ((k.map star)⁻¹)ᵀ = k := by
  have h : kᵀ * k.map star = 1 := by
    have := congrArg Matrix.transpose (Unitary.star_mul_self_of_mem hk)
    rw [Matrix.transpose_mul, Matrix.transpose_one] at this
    exact this
  rw [Matrix.inv_eq_left_inv h, Matrix.transpose_transpose]

theorem mem_K_allPos {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin m) ℂ) :
    u ∈ Formalism.REAL.Kset (allPos m) :=
  ⟨hu, by simp [Formalism.REAL.Jm, allPos]⟩

theorem K_mul {k k' : Matrix (Fin m) (Fin m) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) (hk' : k' ∈ Formalism.REAL.Kset ε) :
    k * k' ∈ Formalism.REAL.Kset ε :=
  ⟨Submonoid.mul_mem _ hk.1 hk'.1, by rw [Matrix.mul_assoc, hk'.2, ← Matrix.mul_assoc, hk.2, Matrix.mul_assoc]⟩

end Mat

theorem mulSingle_mem_KC {ι : Type} {m : ℕ} {ε : ι → Fin m → Bool} {τ : ι} {g : Matrix (Fin m) (Fin m) ℂ}
    (hg : g ∈ GlobalTheory.Dec.KC (ε τ)) (ρ : ι) :
    (Pi.mulSingle τ g : ι → Matrix (Fin m) (Fin m) ℂ) ρ ∈ GlobalTheory.Dec.KC (ε ρ) := by
  by_cases h : ρ = τ
  · subst h; rwa [Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne h]; exact mem_KC_of_K one_mem_K

theorem commute_factU_factK {D : D7} {m n : ℕ} (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ)
    {u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ} (hu : ∀ τ, IsUnit (u τ))
    {g : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ} (hg : ∀ τ, g τ ∈ GlobalTheory.Dec.KC (ε τ)) :
    Commute (factU ε x₁ x₂ x₃ u) (factK n ε x₁ x₂ x₃ g) := by
  have hm := (GlobalTheory.T.fockPolynomialAction_one_mul_adjoint D m n ε x₁ x₂ x₃).2.1
  have h1 : ∀ τ, (1 : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) τ ∈ GlobalTheory.Dec.KC (ε τ) := fun _ => mem_KC_of_K one_mem_K
  have h2 : ∀ τ, IsUnit ((1 : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) τ) := fun _ => isUnit_one
  have a := hm 1 (fun τ => ((g τ)⁻¹)ᵀ) u 1 h1 (fun τ => invT_mem_KC (hg τ)) hu h2
  have b := hm (fun τ => ((g τ)⁻¹)ᵀ) 1 1 u (fun τ => invT_mem_KC (hg τ)) h1 h2 hu
  rw [one_mul, mul_one] at a
  rw [one_mul, mul_one] at b
  exact a.symm.trans b

theorem IsBotFam.map_of_commute {ι : Type} {n : ℕ} {P : Type} [AddCommGroup P] [Module ℂ P] {ε : ι → Fin n → Bool}
    {ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P} {μ : ι → Fin n → ℝ} {x : P} (h : IsBotFam ε ϖ μ x)
    {A : Module.End ℂ P} (hA : ∀ g, (∀ τ, g τ ∈ GlobalTheory.Dec.KC (ε τ)) → Commute A (ϖ g)) : IsBotFam ε ϖ μ (A x) := by
  intro τ
  refine ⟨fun g hg hl => ?_, fun θ => ?_⟩
  · have := LinearMap.congr_fun (hA _ (mulSingle_mem_KC hg)).eq x
    simp only [Module.End.mul_apply] at this
    show ϖ _ (A x) = A x
    rw [← this]
    exact congrArg A ((h τ).1 g hg hl)
  · have hg : (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ GlobalTheory.Dec.KC (ε τ) := by
      refine ⟨?_, by simp [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]⟩
      rw [Matrix.isUnit_diagonal, Pi.isUnit_iff]
      exact fun a => (Complex.exp_ne_zero _).isUnit
    have := LinearMap.congr_fun (hA _ (mulSingle_mem_KC hg)).eq x
    simp only [Module.End.mul_apply] at this
    show ϖ _ (A x) = _
    rw [← this, ← map_smul]
    exact congrArg A ((h τ).2 θ)

def botSub {ι : Type} {n : ℕ} {P : Type} [AddCommGroup P] [Module ℂ P] (ε : ι → Fin n → Bool)
    (ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P) (μ : ι → Fin n → ℝ) : Submodule ℂ P where
  carrier := {x | IsBotFam ε ϖ μ x}
  zero_mem' := fun τ => ⟨fun g _ _ => map_zero _, fun θ => by simp⟩
  add_mem' := fun {a b} ha hb τ => ⟨fun g hg hl => by rw [map_add, (ha τ).1 g hg hl, (hb τ).1 g hg hl],
    fun θ => by rw [map_add, (ha τ).2 θ, (hb τ).2 θ, smul_add]⟩
  smul_mem' := fun c a ha τ => ⟨fun g hg hl => by rw [map_smul, (ha τ).1 g hg hl],
    fun θ => by rw [map_smul, (ha τ).2 θ, smul_comm]⟩

theorem exists_io_poly (D : D7) (V W : HSp D) (θ : InfFam D) (Sp : D.what₂.Tau → SPar) (M : DSModel W Sp)
    (c : CoefA V) (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.coef.W)
    (hθ : IsInfFam θ) (hc : c.Is) (h0 : Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam))
    (BS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hBS : ∀ τ, IsUnit (BS τ))
    (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (x₁ x₂ x₃ : D.what₂.Tau → ℤ) (hr : W.rank ≤ V.rank)
    (hpq : ∀ τ, p τ + q τ = W.rank) (hε : ∀ τ a, M.ε τ a = decide ((a : ℕ) < p τ))
    (hap : ∀ τ a b, a ≤ b → b < p τ → ap τ b ≤ ap τ a) (ham : ∀ τ a b, a ≤ b → b < q τ → am τ b ≤ am τ a)
    (hK : ∀ τ a, Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ) a = (wtK (p τ) (ap τ) (am τ) (x₁ τ) (x₂ τ) a : ℝ))
    (hU : ∀ τ j, wtU (p τ) (q τ) (ap τ) (am τ) (x₃ τ) j = -(lam τ).w j) :
    ∃ io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank,
      (∀ u ∈ GinfC V, (∀ τ, (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt V u) * BS τ ∈ Matrix.unitaryGroup (Fin V.rank) ℂ) →
        ∀ x w, fact M.ε x₁ x₂ x₃ 1 (fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt V u) * BS τ) (io x w) =
          io x (c.ρ u w)) ∧
      (∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (v : ∀ ρ, lowT M ρ) (u : lowT M τ),
        ((u : M.sm τ) : M.H τ) = M.σ τ k ((v τ : M.sm τ) : M.H τ) → ∀ w,
          fact M.ε x₁ x₂ x₃ (Pi.mulSingle τ k) 1 (io (PiTensorProduct.tprod ℂ v) w) =
            io (PiTensorProduct.tprod ℂ (Function.update v τ u)) w) ∧
      ∃ (v : ∀ ρ, lowT M ρ) (w : c.W), (∀ ρ, ‖((v ρ : M.sm ρ) : M.H ρ)‖ = 1) ∧ ‖w‖ = 1 ∧
        io (PiTensorProduct.tprod ℂ v) w = delta p q ap am := by
  obtain ⟨hhK, hhU⟩ := GlobalTheory.T.fockActions_isHolomorphicProductKRepFamily D W.rank V.rank M.ε x₁ x₂ x₃
  obtain ⟨κ, Δ', hκ, hΔ, hbK, hbU⟩ := GlobalTheory.T.exists_minorProduct_translate_jointLowestWeight D W.rank V.rank M.ε p q ap am x₁ x₂ x₃ hr hpq hε hap ham
  obtain ⟨m, hm1, hm2, hm3⟩ := GlobalTheory.T.holomorphic_family_low_lie_action D W Sp M _ _ _ hhK
  obtain ⟨hv1, hv2, hv3, hv4⟩ := GlobalTheory.T.frameFunctionAction_holomorphic_extremal_lowest D.what₂.Tau V.rank lam
  have eK : (fun τ a => -(wtK (p τ) (ap τ) (am τ) (x₁ τ) (x₂ τ) a : ℝ)) =
      fun τ => -Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ) := by
    funext τ a; rw [Pi.neg_apply, hK]
  have eU : (fun τ (j : Fin V.rank) => (wtU (p τ) (q τ) (ap τ) (am τ) (x₃ τ) j : ℝ)) =
      fun τ j => -((lam τ).w j : ℝ) := by
    funext τ j; rw [hU]; push_cast; rfl
  rw [eK] at hbK
  rw [eU] at hbU
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.lowest_weight_vector_transfer _ _ _ _ _ _ _ _ _ _ _ _ hhU hv1 hbU hv2 hv3
  obtain ⟨j, hj1, hj2⟩ := GlobalTheory.T.exists_polynomialModel_coefficientSpace_realPoints D V θ c lam c0 hθ hc h0 BS hBS
  have key : ∀ F ∈ VV ℂ lam,
      ψ F ∈ botSub M.ε (factK V.rank M.ε x₁ x₂ x₃) (fun τ => -Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) ∧
      ∀ u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, u τ ∈ Formalism.REAL.Kset (allPos V.rank)) →
        ψ (vact lam u F) = factU M.ε x₁ x₂ x₃ u (ψ F) := by
    intro F hF
    have hF' := GlobalTheory.T.coefficientSpace_le_span_unitary_orbit_extremal D.what₂.Tau V.rank lam hF
    clear hF
    induction hF' using Submodule.span_induction with
    | mem F h =>
      obtain ⟨u, hu, rfl⟩ := h
      refine ⟨?_, fun u' hu' => ?_⟩
      · rw [hψ u hu]
        exact hbK.map_of_commute fun g hg => commute_factU_factK _ _ _ _ (fun τ => (mem_KC_of_K (hu τ)).1) hg
      · rw [← Module.End.mul_apply, ← hv1.2.2.1 u' u (fun τ => mem_KC_of_K (hu' τ)) (fun τ => mem_KC_of_K (hu τ)),
          hψ (u' * u) (fun τ => K_mul (hu' τ) (hu τ)), hψ u hu,
          hhU.2.2.1 u' u (fun τ => mem_KC_of_K (hu' τ)) (fun τ => mem_KC_of_K (hu τ)), Module.End.mul_apply]
    | zero => exact ⟨by rw [map_zero]; exact zero_mem _, fun u _ => by simp only [map_zero]⟩
    | add a b _ _ ha hb =>
      exact ⟨by rw [map_add]; exact add_mem ha.1 hb.1, fun u hu => by simp only [map_add, ha.2 u hu, hb.2 u hu]⟩
    | smul s a _ ha =>
      exact ⟨by rw [map_smul]; exact Submodule.smul_mem _ _ ha.1, fun u hu => by simp only [map_smul, ha.2 u hu]⟩
  have hjm : ∀ w, j w ∈ VV ℂ lam := fun w => hj1 ▸ LinearMap.mem_range_self j w
  obtain ⟨v0, hv0, hmv⟩ := hm2 κ hκ
  obtain ⟨w0, hw0⟩ : (ten fun τ => extremal ℂ V.rank (lam τ)) ∈ LinearMap.range j := hj1 ▸ hv4
  have hw0' : w0 ≠ 0 := by
    rintro rfl
    exact hv3 (by rw [← hw0, map_zero])
  have hψ0 : ψ (j w0) = Δ' := by
    have := hψ 1 fun _ => one_mem_K
    rwa [hv1.2.1, hhU.2.1, Module.End.one_apply, Module.End.one_apply, ← hw0] at this
  let N : D.what₂.Tau → ℂ := fun ρ => (‖((v0 ρ : M.sm ρ) : M.H ρ)‖ : ℂ)
  have hN : ∀ ρ, ‖((v0 ρ : M.sm ρ) : M.H ρ)‖ ≠ 0 := fun ρ h =>
    hv0 ρ (Subtype.ext (Subtype.ext (norm_eq_zero.1 h)))
  have hN' : ∀ ρ, N ρ ≠ 0 := fun ρ => Complex.ofReal_ne_zero.2 (hN ρ)
  have hw1 : ‖w0‖ ≠ 0 := norm_ne_zero_iff.2 hw0'
  have hw2 : (‖w0‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hw1
  obtain ⟨io, hio⟩ : ∃ io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank,
      ∀ x w, io x w = ((∏ ρ, N ρ) * (‖w0‖ : ℂ)) • m x (ψ (j w)) :=
    ⟨((∏ ρ, N ρ) * (‖w0‖ : ℂ)) • LinearMap.compl₂ m (ψ ∘ₗ j), fun _ _ => rfl⟩
  refine ⟨io, fun u hu hun x w => ?_, fun τ k hk v u hu w => ?_,
    fun ρ => (N ρ)⁻¹ • v0 ρ, (‖w0‖ : ℂ)⁻¹ • w0, fun ρ => ?_, ?_, ?_⟩
  · rw [hio, hio, map_smul]
    refine congrArg (HSMul.hSMul _) ?_
    have hcm := hm1 (factU M.ε x₁ x₂ x₃ fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt V u) * BS τ)
      (fun k hk => commute_factU_factK _ _ _ _ (fun τ => (mem_KC_of_K (mem_K_allPos (hun τ))).1)
        fun τ => mem_KC_of_K (hk τ)) x
    rw [hj2 u hu, (key _ (hjm w)).2 _ fun τ => mem_K_allPos (hun τ)]
    exact LinearMap.congr_fun hcm.eq _
  · rw [hio, hio, map_smul]
    refine congrArg (HSMul.hSMul _) ?_
    rw [hm3 _ (key _ (hjm w)).1 τ k hk v u hu]
    have : (fun ρ => (((Pi.mulSingle τ (k.map star) : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) ρ)⁻¹)ᵀ) =
        Pi.mulSingle τ k := by
      funext ρ
      by_cases h : ρ = τ
      · subst h; rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same, invT_conj hk.1]
      · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne h, inv_one, Matrix.transpose_one]
    rw [factK, this]
  · show ‖(N ρ)⁻¹ • ((v0 ρ : M.sm ρ) : M.H ρ)‖ = 1
    rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ (hN ρ)]
  · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hw1]
  · rw [MultilinearMap.map_smul_univ]
    rw [map_smul, map_smul, LinearMap.smul_apply, hio, smul_smul, smul_smul, hψ0, hmv _ hbK, factK]
    have : (fun τ => (((κ τ).map star)⁻¹)ᵀ) = κ := funext fun τ => invT_conj (hκ τ).1
    rw [this, hΔ, Finset.prod_inv_distrib]
    have hP : (∏ ρ, N ρ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun ρ _ => hN' ρ
    convert one_smul ℂ _ using 2
    field_simp

end GlobalTheory.JointHarm

namespace GlobalTheory.JointHarm

theorem onb_eq_one {k : ℕ} {G B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G 1 B k) : Bᴴ * G * B = 1 := by
  obtain ⟨e, he, h1, -⟩ := h
  rw [h1, ← Matrix.diagonal_one]
  congr 1
  funext a
  rcases he a with h | h
  · simp [h.1]
  · exact absurd a.2 (not_lt.2 h.2)

theorem conj_mem_UH {D : D7} {W : HSp D} {Sp : D.what₂.Tau → SPar} (M : DSModel W Sp) (τ : D.what₂.Tau)
    {k : Matrix (Fin W.rank) (Fin W.rank) ℂ} (hk : k ∈ Formalism.REAL.Kset (M.ε τ)) :
    (M.fr τ)⁻¹ * k * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ) := by
  obtain ⟨_inst⟩ := (M.fr_unit τ).nonempty_invertible
  have h1 : kᴴ * Formalism.REAL.Jm (M.ε τ) * k = Formalism.REAL.Jm (M.ε τ) := by
    have : kᴴ * k = 1 := Unitary.star_mul_self_of_mem hk.1
    rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, this, Matrix.one_mul]
  have h2 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_inv_of_invertible, Matrix.conjTranspose_one]
  show ((M.fr τ)⁻¹ * k * M.fr τ)ᴴ * gramAt D W τ * ((M.fr τ)⁻¹ * k * M.fr τ) = gramAt D W τ
  rw [← M.fr_gram τ]
  calc _ = (M.fr τ)ᴴ * (kᴴ * (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * k) * M.fr τ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h2, Matrix.mul_inv_of_invertible, Matrix.mul_one, Matrix.mul_one, h1]

theorem exists_ioP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.thP_ωP → R.thP_vP → R.thP_pt_theta ∧ ∃ io, ({ R with ioP := io } : RealDat D A Ks).thP_ioP := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hF hM hω hv
  have hθ : IsInfFam R.θ := hM.inf
  have hth : ∀ i t, IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := fun i t => by
    obtain ⟨⟨hψ, h0⟩, e, -, h⟩ := hv i t
    exact isThetaFunO_of_isThetaAt hψ hθ h h0.theta
  refine ⟨fun i t P => ?_, ?_⟩
  · exact (GlobalTheory.OrientedHeis.om_pureTensorO D _ _ _ _ _ _ _ (hω i t) hθ (fun _ => 1) (fun _ => 1) (R.BV i) _
      (cart (R.MW i (sg0 D A))) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) _ 1 1
      (fun τ => by rw [Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [compAt_mt_one', Matrix.mul_one, Matrix.one_mul]) (fun _ => rfl) (fun _ => rfl) _ (hth i t) P).1
  suffices h : ∀ i, ∃ y : LowT (R.MW i (sg0 D A)) →ₗ[ℂ] (R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank,
      ∀ t, IsIoW R.θ (R.MW i (sg0 D A)) (R.cV i) (R.ωP i t) (R.ptP i t) (RealDat.Delta i) y from
    Classical.skolem.1 h
  intro i
  obtain ⟨gramR, c0R, c0L, hT⟩ := hF.tie
  have hBS : ∀ τ, (R.BV i τ)ᴴ * gramAt D (Vc D i) τ * R.BV i τ = 1 := fun τ => onb_eq_one (hM.BV i τ)
  have hBu : ∀ τ, IsUnit (R.BV i τ) := fun τ => (IsUnit.of_mul_eq_one_right _ (hBS τ))
  obtain ⟨x₁, x₂, x₃, hx⟩ := GlobalTheory.T.lowestKType_coefficientWeight_eq_minorWeights D i (sg0 D A) (sgAt_mk _ R.hv0) (R.MW i (sg0 D A)) (hM.order i)
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hpq : ∀ τ, ((Wc D i).sig (tauE D τ)).1 + ((Wc D i).sig (tauE D τ)).2 = (Wc D i).rank := fun τ =>
    (GlobalTheory.T.thetaWeightArithmeticAtPlace_proof D i τ).rank.1.trans hrk.symm
  obtain ⟨io, h1, h2, h3⟩ := exists_io_poly D (Vc D i) (Wc D i) R.θ _ (R.MW i (sg0 D A)) (R.cV i) _ (c0L i) hθ
    (hM.cV i) (hT.mapL i) (R.BV i) hBu _ _ _ _ x₁ x₂ x₃ (hrk.le.trans (r_le_V i)) hpq (hM.order i)
    (fun τ => (GlobalTheory.T.thetaWeightArithmeticAtPlace_proof D i τ).aPlus_antitone) (fun τ => (GlobalTheory.T.thetaWeightArithmeticAtPlace_proof D i τ).aM_anti) (fun τ => (hx τ).2.2.2.1)
    (fun τ => (hx τ).2.2.2.2)
  refine ⟨io, fun t => ?_⟩
  have hact := GlobalTheory.T.weil_maximalCompact_fock_substitution_character D R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) _ (R.MW i (sg0 D A)) (R.BV i) (hω i t) hθ
    (D.sp.V_sig _) (D.sp.W_sig _) hBS _ _ hpq (hM.order i) _ _ (fun τ => (GlobalTheory.T.thetaLiftInfinityTypes_atRealPlace D T R.toLevCh A.μ0 hL i t τ).chiV)
    (fun τ => (GlobalTheory.T.thetaLiftInfinityTypes_atRealPlace D T R.toLevCh A.μ0 hL i t τ).chiW) x₁ x₂ x₃ (fun τ => (hx τ).1) (fun τ => (hx τ).2.1)
    (fun τ => (hx τ).2.2.1) _ (hth i t)
    (GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hv i t) (hth i t))
  have hfr : ∀ τ, (R.MW i (sg0 D A)).fr τ * ((R.MW i (sg0 D A)).fr τ)⁻¹ = 1 := fun τ =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 ((R.MW i (sg0 D A)).fr_unit τ))
  refine ⟨fun u hu x w => ?_, fun τ k hk v u hu w => ?_, h3⟩
  · have e : (fun τ => (R.MW i (sg0 D A)).fr τ * compAt R.θ τ (Formalism.L2.Theta.mt (Wc D i) 1) *
        ((R.MW i (sg0 D A)).fr τ)⁻¹) = 1 := by
      funext τ; rw [compAt_mt_one', Matrix.mul_one, hfr]; rfl
    obtain ⟨a, b⟩ := hact u hu 1 (one_mem _) fun τ => by rw [congrFun e τ]; exact one_mem_K
    rw [← h1 u hu a x w]
    have := b (io x w)
    rw [e] at this
    exact this
  · have hs := GlobalTheory.PointAtPlaceHom.atTau_spec hθ (Wc D i) τ (conj_mem_UH (R.MW i (sg0 D A)) τ hk)
    have e : (fun ρ => (R.MW i (sg0 D A)).fr ρ * compAt R.θ ρ (Formalism.L2.Theta.mt (Wc D i)
        (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ))) *
        ((R.MW i (sg0 D A)).fr ρ)⁻¹) = Pi.mulSingle τ k := by
      funext ρ
      rw [GlobalTheory.WeilDeriv.compAt_mt_eq_infMat]
      by_cases h : ρ = τ
      · subst h
        rw [hs.2.1, Pi.mulSingle_eq_same]
        calc _ = ((R.MW i (sg0 D A)).fr ρ * ((R.MW i (sg0 D A)).fr ρ)⁻¹) * k *
            ((R.MW i (sg0 D A)).fr ρ * ((R.MW i (sg0 D A)).fr ρ)⁻¹) := by simp only [Matrix.mul_assoc]
          _ = k := by rw [hfr, Matrix.one_mul, Matrix.mul_one]
      · rw [hs.2.2 ρ h, Pi.mulSingle_eq_of_ne h, Matrix.mul_one, hfr]
    have e' : (fun ρ => (R.BV i ρ)⁻¹ * compAt R.θ ρ (Formalism.L2.Theta.mt (Vc D i) 1) * R.BV i ρ) = 1 := by
      funext ρ
      rw [compAt_mt_one', Matrix.mul_one, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (hBu ρ))]; rfl
    obtain ⟨-, b⟩ := hact 1 (one_mem _) _ hs.1 fun ρ => by
      rw [congrFun e ρ]
      by_cases h : ρ = τ
      · subst h; rwa [Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne h]; exact one_mem_K
    rw [← h2 τ k hk v u hu w]
    have := b (io (PiTensorProduct.tprod ℂ v) w)
    rw [e, e'] at this
    exact this

end GlobalTheory.JointHarm

end
end
