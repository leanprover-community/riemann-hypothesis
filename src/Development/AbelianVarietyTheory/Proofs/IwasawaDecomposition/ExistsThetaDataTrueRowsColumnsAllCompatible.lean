import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAllTiedEqTiedOnOfRealised
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeilEq
import Formalism.LocalToGlobal.JointCharacters.SameChr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMkTauE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpIffHasInfQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueNormalizedHaarMeasureAdelicUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrientedWeilDatumOfAdelicWeilRepTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTransportGroupsCuspFormsWeilDataIsometryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupChars
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueInfFam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
import BuildAid.D3

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Th

theorem weilTiedEq_of_eqTied : ∀ (D : D7) (X : ThetaX D) (T : ThetaTied D X) (W : WeilTied D X T), WeilThetaCompatibility W → WeilCompatibleEquivariance W :=
  fun _ _ _ _ h => ⟨h.range, h.Heisenberg₂, h.aut, h.cont, h.unit, h.split, ⟨h.twW, h.twV⟩, h.th⟩

end GlobalTheory.Mem.Th
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SameChrFin

theorem sameChr_of_chrEq : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch) (X : ThetaX D)
    (T : ThetaTied D X) (H : Formalism.L2.Host.ThetaChrTied D C nch Tp X),
    (∀ c, Formalism.IndefR.Links.ChrEq (T.eChr c) (H.eChr c)) → Formalism.L2.JoinChr.SameChr T H := by
  intro D C nch Tp X T H h
  refine ⟨fun P => ?_, fun c P e he k x hx => (h c).2 P e he k x hx,
    fun θ hθ c τ k x hx => GlobalTheory.CharInfPlace.chrEq_infLoc D (T.eChr c) (H.eChr c) (h c) θ hθ τ k x hx⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  exact ⟨e, he⟩

end GlobalTheory.SameChrFin
end

section
section
namespace GlobalTheory

theorem exists_common_nonzero_of_polynomial_on_lines (V : Type) [AddCommGroup V] [Module ℝ V]
    (ι : Type) [Finite ι] (f : ι → V → ℂ)
    (hpoly : ∀ i a b, ∃ p : Polynomial ℂ, ∀ s : ℝ, f i (a + s • b) = p.eval (s : ℂ))
    (hne : ∀ i, ∃ v, f i v ≠ 0) : ∃ v, ∀ i, f i v ≠ 0 := by
  classical
  have _ := Fintype.ofFinite ι
  have key : ∀ t : Finset ι, ∃ v, ∀ i ∈ t, f i v ≠ 0 := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert j t hj ih =>
      obtain ⟨v, hv⟩ := ih
      obtain ⟨w, hw⟩ := hne j
      choose p hp using fun i => hpoly i v (w - v)
      have hp0 : ∀ i ∈ insert j t, p i ≠ 0 := by
        intro i hi h
        rcases Finset.mem_insert.1 hi with hij | hi
        · subst hij
          apply hw
          have := hp i 1
          simpa [h] using this
        · apply hv i hi
          have := hp i 0
          simpa [h] using this
      have hfin : Set.Finite (⋃ i ∈ (insert j t : Finset ι),
          (fun s : ℝ => (s : ℂ)) ⁻¹' {z | (p i).IsRoot z}) :=
        Set.Finite.biUnion (Finset.finite_toSet _) fun i hi =>
          (Polynomial.finite_setOf_isRoot (hp0 i hi)).preimage Complex.ofReal_injective.injOn
      obtain ⟨s, hs⟩ := hfin.exists_notMem
      refine ⟨v + s • (w - v), fun i hi => ?_⟩
      rw [hp i s]
      intro h0
      apply hs
      simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_setOf_eq]
      exact ⟨i, hi, h0⟩
  obtain ⟨v, hv⟩ := key Finset.univ
  exact ⟨v, fun i => hv i (Finset.mem_univ i)⟩

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_nonzero_of_polynomial_on_real_lines : ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (ι : Type) [Finite ι] (f : ι → V → ℂ), (∀ i a b, ∃ p : Polynomial ℂ, ∀ s : ℝ, f i (a + s • b) = p.eval (s : ℂ)) → (∀ i, ∃ v, f i v ≠ 0) → ∃ v, ∀ i, f i v ≠ 0 := by
  atlas_forward_decl GlobalTheory.exists_common_nonzero_of_polynomial_on_lines
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.Mem.PureSep

theorem exists_finite_subspaces {ι : Type} {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    (x : ⨂[ℂ] i, E i) : ∃ W : ∀ i, Submodule ℂ (E i), (∀ i, FiniteDimensional ℂ (W i)) ∧
      ∃ y : ⨂[ℂ] i, W i, PiTensorProduct.map (fun i => (W i).subtype) y = x := by
  classical
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    refine ⟨fun i => ℂ ∙ m i, fun i => inferInstance,
      r • PiTensorProduct.tprod ℂ (fun i => (⟨m i, Submodule.mem_span_singleton_self _⟩ : ℂ ∙ m i)), ?_⟩
    rw [map_smul, PiTensorProduct.map_tprod]
    rfl
  | add a b ha hb =>
    obtain ⟨W₁, h₁, y₁, rfl⟩ := ha
    obtain ⟨W₂, h₂, y₂, rfl⟩ := hb
    refine ⟨fun i => W₁ i ⊔ W₂ i, fun i => by have := h₁ i; have := h₂ i; infer_instance,
      PiTensorProduct.map (fun i => Submodule.inclusion (le_sup_left : W₁ i ≤ W₁ i ⊔ W₂ i)) y₁ +
        PiTensorProduct.map (fun i => Submodule.inclusion (le_sup_right : W₂ i ≤ W₁ i ⊔ W₂ i)) y₂, ?_⟩
    rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp,
      ← PiTensorProduct.map_comp]
    rfl

theorem exists_ellT_ne_zero : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (x : SmT M), x ≠ 0 → ∃ w : M.Vec, ellT M (fun τ => (w τ : M.H τ)) (inclT M x) ≠ 0 := by
  classical
  intro D V S M x hx
  obtain ⟨W, hW, y, rfl⟩ := exists_finite_subspaces x
  have hy : y ≠ 0 := by
    rintro rfl
    exact hx (map_zero _)
  let ob : ∀ τ, OrthonormalBasis (Fin (Module.finrank ℂ (W τ))) ℂ (W τ) := fun τ =>
    haveI := hW τ; stdOrthonormalBasis ℂ (W τ)
  let B := Basis.piTensorProduct (fun τ => (ob τ).toBasis)
  obtain ⟨k, hk⟩ : ∃ k, B.repr y k ≠ 0 := by
    by_contra h
    push_neg at h
    apply hy
    apply B.repr.injective
    ext k
    simp [h k]
  refine ⟨fun τ => ((ob τ (k τ) : W τ) : M.sm τ), ?_⟩
  have key : ∀ y' : ⨂[ℂ] τ, W τ,
      ellT M (fun τ => (((ob τ (k τ) : W τ) : M.sm τ) : M.H τ))
        (inclT M (PiTensorProduct.map (fun τ => (W τ).subtype) y')) = B.repr y' k := by
    intro y'
    induction y' using PiTensorProduct.induction_on with
    | smul_tprod r z =>
      unfold ellT inclT
      simp only [map_smul, PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod, Finsupp.smul_apply, B,
        Basis.piTensorProduct_repr_tprod_apply, MultilinearMap.compLinearMap_apply,
        MultilinearMap.mkPiAlgebra_apply, innerₛₗ_apply_apply, smul_eq_mul]
      congr 1
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
      rfl
    | add a b ha hb =>
      simp only [map_add, Finsupp.add_apply] at ha hb ⊢
      rw [ha, hb]
  exact fun h => hk ((key y).symm.trans h)

end GlobalTheory.Mem.PureSep
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothPureTensors_separate_tensorProduct : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (x : SmT M), x ≠ 0 → ∃ w : M.Vec, ellT M (fun τ => (w τ : M.H τ)) (inclT M x) ≠ 0 := by
  atlas_forward_decl GlobalTheory.Mem.PureSep.exists_ellT_ne_zero
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.Mem.UnitPairing

def IsPolyFn (f : ℝ → ℂ) : Prop := ∃ p : Polynomial ℂ, ∀ s : ℝ, f s = p.eval (s : ℂ)

theorem IsPolyFn.const (c : ℂ) : IsPolyFn fun _ => c := ⟨Polynomial.C c, fun s => by simp⟩

theorem IsPolyFn.coe : IsPolyFn fun s => (s : ℂ) := ⟨Polynomial.X, fun s => by simp⟩

theorem IsPolyFn.add {f g : ℝ → ℂ} (hf : IsPolyFn f) (hg : IsPolyFn g) : IsPolyFn fun s => f s + g s := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun s => by simp [hp, hq]⟩

theorem IsPolyFn.mul {f g : ℝ → ℂ} (hf : IsPolyFn f) (hg : IsPolyFn g) : IsPolyFn fun s => f s * g s := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun s => by simp [hp, hq]⟩

theorem IsPolyFn.sum {ι : Type} (t : Finset ι) {f : ι → ℝ → ℂ} (hf : ∀ i, IsPolyFn (f i)) :
    IsPolyFn fun s => ∑ i ∈ t, f i s := by
  choose p hp using hf
  exact ⟨∑ i ∈ t, p i, fun s => by simp [hp, Polynomial.eval_finsetSum]⟩

theorem IsPolyFn.prod {ι : Type} (t : Finset ι) {f : ι → ℝ → ℂ} (hf : ∀ i, IsPolyFn (f i)) :
    IsPolyFn fun s => ∏ i ∈ t, f i s := by
  choose p hp using hf
  exact ⟨∏ i ∈ t, p i, fun s => by simp [hp, Polynomial.eval_prod]⟩

variable {D : D7} {V V' : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel V' S')

theorem ellT_pure (w v : ∀ τ, M.H τ) : ellT M w (PiTensorProduct.tprod ℂ v) = ∏ τ, ⟪w τ, v τ⟫_ℂ := by
  simp [ellT]

theorem isPolyFn_ellT (a b : M.Vec) (x : ⨂[ℂ] τ, M.H τ) :
    IsPolyFn fun s => ellT M (fun τ => ((a + (s : ℂ) • b) τ : M.H τ)) x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul, ellT_pure, smul_eq_mul, Pi.add_apply, Pi.smul_apply, Submodule.coe_add, Submodule.coe_smul,
      inner_add_left, inner_smul_left, Complex.conj_ofReal]
    exact (IsPolyFn.const _).mul (IsPolyFn.prod _ fun τ => (IsPolyFn.const _).add (IsPolyFn.coe.mul (IsPolyFn.const _)))
  | add x y hx hy =>
    simp only [map_add]
    exact hx.add hy

theorem ellT_smul (c : D.what₂.Tau → ℝ) (a : M.Vec) (x : ⨂[ℂ] τ, M.H τ) :
    ellT M (fun τ => (((c τ : ℂ) • a τ : M.sm τ) : M.H τ)) x = (∏ τ, (c τ : ℂ)) * ellT M (fun τ => (a τ : M.H τ)) x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul, ellT_pure, smul_eq_mul, Submodule.coe_smul, inner_smul_left, Complex.conj_ofReal,
      Finset.prod_mul_distrib]
    ring
  | add x y hx hy =>
    simp only [map_add, hx, hy, mul_add]

noncomputable def pairing (L : SmT M' →ₗ[ℂ] SmT M) (w : M.Vec) (v : M'.Vec) : ℂ :=
  ellT M (fun τ => (w τ : M.H τ)) (inclT M (L (PiTensorProduct.tprod ℂ v)))

theorem isPolyFn_pairing (L : SmT M' →ₗ[ℂ] SmT M) (a b : M.Vec) (a' b' : M'.Vec) :
    IsPolyFn fun s => pairing M M' L (a + (s : ℂ) • b) (a' + (s : ℂ) • b') := by
  classical
  have h : ∀ s : ℝ, PiTensorProduct.tprod ℂ (a' + (s : ℂ) • b') = ∑ t : Finset D.what₂.Tau,
      (∏ τ, if τ ∈ t then (1 : ℂ) else (s : ℂ)) • PiTensorProduct.tprod ℂ (t.piecewise a' b') := fun s => by
    rw [MultilinearMap.map_add_univ]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← MultilinearMap.map_smul_univ]
    congr 1
    funext τ
    by_cases hτ : τ ∈ t <;> simp [Finset.piecewise, hτ]
  simp only [pairing, h, map_sum, map_smul, smul_eq_mul]
  refine IsPolyFn.sum _ fun t => IsPolyFn.mul (IsPolyFn.prod _ fun τ => ?_) (isPolyFn_ellT M a b _)
  by_cases hτ : τ ∈ t
  · simpa [hτ] using IsPolyFn.const 1
  · simpa [hτ] using IsPolyFn.coe

noncomputable def nrm (a : M.Vec) : M.Vec := fun τ => ((‖(a τ : M.H τ)‖⁻¹ : ℝ) : ℂ) • a τ

theorem smul_nrm (a : M.Vec) : (fun τ => ((‖(a τ : M.H τ)‖ : ℝ) : ℂ) • nrm M a τ) = a := by
  funext τ
  by_cases h : a τ = 0
  · simp [nrm, h]
  · have : ‖(a τ : M.H τ)‖ ≠ 0 := by simpa using h
    rw [nrm, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ this, Complex.ofReal_one, one_smul]

theorem norm_nrm (a : M.Vec) (h : (∏ τ, ((‖(a τ : M.H τ)‖ : ℝ) : ℂ)) ≠ 0) (τ : D.what₂.Tau) : ‖(nrm M a τ : M.H τ)‖ = 1 := by
  have h1 : ‖(a τ : M.H τ)‖ ≠ 0 := Complex.ofReal_ne_zero.1 (Finset.prod_ne_zero_iff.1 h τ (Finset.mem_univ τ))
  rw [nrm, Submodule.coe_smul, norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ h1]

theorem pairing_nrm (L : SmT M' →ₗ[ℂ] SmT M) (w : M.Vec) (v : M'.Vec) :
    pairing M M' L w v = (∏ τ, ((‖(w τ : M.H τ)‖ : ℝ) : ℂ)) * ((∏ τ, ((‖(v τ : M'.H τ)‖ : ℝ) : ℂ)) *
      pairing M M' L (nrm M w) (nrm M' v)) := by
  have h1 : PiTensorProduct.tprod ℂ v = (∏ τ, ((‖(v τ : M'.H τ)‖ : ℝ) : ℂ)) • PiTensorProduct.tprod ℂ (nrm M' v) := by
    rw [← MultilinearMap.map_smul_univ, smul_nrm]
  have h2 : ∀ x, ellT M (fun τ => (w τ : M.H τ)) x =
      (∏ τ, ((‖(w τ : M.H τ)‖ : ℝ) : ℂ)) * ellT M (fun τ => (nrm M w τ : M.H τ)) x := fun x => by
    rw [← ellT_smul M (fun τ => ‖(w τ : M.H τ)‖)]
    exact congrArg (fun u : M.Vec => ellT M (fun τ => (u τ : M.H τ)) x) (smul_nrm M w).symm
  rw [pairing, pairing, h1, h2, map_smul, map_smul, map_smul, smul_eq_mul]

theorem unit_of_ne {P : Type} [AddCommGroup P] [Module ℂ P] (It : P →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (φ : P) (w : M.Vec) (v : M'.Vec)
    (h : pairing M M' (It φ) w v ≠ 0) :
    (∀ τ, ‖(nrm M w τ : M.H τ)‖ = 1) ∧ (∀ τ, ‖(nrm M' v τ : M'.H τ)‖ = 1) ∧
      ∃ φ', pairing M M' (It φ') (nrm M w) (nrm M' v) = 1 := by
  rw [pairing_nrm] at h
  obtain ⟨h1, h⟩ := mul_ne_zero_iff.1 h
  obtain ⟨h2, h3⟩ := mul_ne_zero_iff.1 h
  refine ⟨norm_nrm M w h1, norm_nrm M' v h2, (pairing M M' (It φ) (nrm M w) (nrm M' v))⁻¹ • φ, ?_⟩
  rw [← inv_mul_cancel₀ h3]
  simp only [pairing, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem exists_pairing_ne {P : Type} [AddCommGroup P] [Module ℂ P] (It : P →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (h : It ≠ 0) :
    ∃ φ w v, pairing M M' (It φ) w v ≠ 0 := by
  have : ∃ φ v, It φ (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    by_contra hn
    push Not at hn
    refine h (LinearMap.ext fun φ => ?_)
    exact PiTensorProduct.ext (MultilinearMap.ext fun v => hn φ v)
  obtain ⟨φ, v, hv⟩ := this
  obtain ⟨w, hw⟩ := GlobalTheory.T.smoothPureTensors_separate_tensorProduct D V S M _ hv
  exact ⟨φ, w, v, hw⟩

theorem exists_common (U : Type) [AddCommGroup U] [Module ℂ U] (ι : Type) [Finite ι] (f : ι → U → ℂ)
    (h : ∀ i a b, IsPolyFn fun s => f i (a + (s : ℂ) • b)) (h' : ∀ i, ∃ v, f i v ≠ 0) : ∃ v, ∀ i, f i v ≠ 0 :=
  @GlobalTheory.T.exists_common_nonzero_of_polynomial_on_real_lines U _ (Module.complexToReal U) ι _ f h h'

theorem exists_unit_vectors : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), (∀ k, k + 1 < D.R.m → R.ItY k ≠ 0) → R.ItX ≠ 0 → ∃ (d : ∀ j, (R.MY j).Vec) (dX : R.MX.Vec) (φ : ∀ k, PolF D (Yc D (k + 1)).rank (Yc D k).rank) (φX : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank), (∀ j, j < D.R.m → ∀ τ, ‖(d j τ : (R.MY j).H τ)‖ = 1) ∧ (∀ τ, ‖(dX τ : R.MX.H τ)‖ = 1) ∧ (∀ k, k + 1 < D.R.m → ellT (R.MY k) (fun τ => (d k τ : (R.MY k).H τ)) (inclT (R.MY k) (R.ItY k (φ k) (PiTensorProduct.tprod ℂ (d (k + 1))))) = 1) ∧ ellT (R.MY (D.R.m - 1)) (fun τ => (d (D.R.m - 1) τ : (R.MY (D.R.m - 1)).H τ)) (inclT (R.MY (D.R.m - 1)) (R.ItX φX (PiTensorProduct.tprod ℂ dX))) = 1 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hY hX
  classical
  have hm := D.R.two_le_m
  have e1 : ∀ k, ∃ φ : PolF D (Yc D (k + 1)).rank (Yc D k).rank, k + 1 < D.R.m →
      ∃ w v, pairing (R.MY k) (R.MY (k + 1)) (R.ItY k φ) w v ≠ 0 := fun k => by
    by_cases hk : k + 1 < D.R.m
    · obtain ⟨φ, h⟩ := exists_pairing_ne _ _ (R.ItY k) (hY k hk)
      exact ⟨φ, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose φ hφ using e1
  obtain ⟨φX, wX, vX, hφX⟩ := exists_pairing_ne _ _ R.ItX hX
  let f : Option (Fin (D.R.m - 1)) → (∀ j, (R.MY j).Vec) × R.MX.Vec → ℂ := fun i u =>
    match i with
    | none => pairing (R.MY (D.R.m - 1)) R.MX (R.ItX φX) (u.1 (D.R.m - 1)) u.2
    | some k => pairing (R.MY k) (R.MY (k + 1)) (R.ItY k (φ k)) (u.1 k) (u.1 (k + 1))
  obtain ⟨u, hu⟩ := exists_common _ _ f (fun i a b => by
      cases i with
      | none => exact isPolyFn_pairing _ _ _ _ _ _ _
      | some k => exact isPolyFn_pairing _ _ _ _ _ _ _) (fun i => by
      cases i with
      | none =>
        refine ⟨(Function.update 0 (D.R.m - 1) wX, vX), ?_⟩
        simpa only [f, Function.update_self] using hφX
      | some k =>
        obtain ⟨w, v, h⟩ := hφ k (by omega)
        refine ⟨(Function.update (Function.update 0 (k : ℕ) w) (k + 1) v, 0), ?_⟩
        simpa only [f, Function.update_self, Function.update_of_ne (Nat.succ_ne_self (k : ℕ)).symm] using h)
  obtain ⟨x1, x2, φX', x3⟩ := unit_of_ne _ _ R.ItX φX _ _ (hu none)
  have e2 : ∀ k, ∃ φ' : PolF D (Yc D (k + 1)).rank (Yc D k).rank, k + 1 < D.R.m →
      (∀ τ, ‖(nrm (R.MY k) (u.1 k) τ : (R.MY k).H τ)‖ = 1) ∧
      pairing (R.MY k) (R.MY (k + 1)) (R.ItY k φ') (nrm _ (u.1 k)) (nrm _ (u.1 (k + 1))) = 1 := fun k => by
    by_cases hk : k + 1 < D.R.m
    · obtain ⟨y1, -, φ', y3⟩ := unit_of_ne _ _ (R.ItY k) (φ k) _ _ (hu (some ⟨k, by omega⟩))
      exact ⟨φ', fun _ => ⟨y1, y3⟩⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose φ' hφ' using e2
  refine ⟨fun j => nrm _ (u.1 j), nrm _ u.2, φ', φX', fun j hj => ?_, x2, fun k hk => (hφ' k hk).2, x3⟩
  by_cases hk : j + 1 < D.R.m
  · exact (hφ' j hk).1
  · obtain rfl : j = D.R.m - 1 := by omega
    exact x1

end GlobalTheory.Mem.UnitPairing
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomial_frame_maps_bounded : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), (∀ k, k + 1 < D.R.m → R.ItY k ≠ 0) → R.ItX ≠ 0 → ∃ (d : ∀ j, (R.MY j).Vec) (dX : R.MX.Vec) (φ : ∀ k, PolF D (Yc D (k + 1)).rank (Yc D k).rank) (φX : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank), (∀ j, j < D.R.m → ∀ τ, ‖(d j τ : (R.MY j).H τ)‖ = 1) ∧ (∀ τ, ‖(dX τ : R.MX.H τ)‖ = 1) ∧ (∀ k, k + 1 < D.R.m → ellT (R.MY k) (fun τ => (d k τ : (R.MY k).H τ)) (inclT (R.MY k) (R.ItY k (φ k) (PiTensorProduct.tprod ℂ (d (k + 1))))) = 1) ∧ ellT (R.MY (D.R.m - 1)) (fun τ => (d (D.R.m - 1) τ : (R.MY (D.R.m - 1)).H τ)) (inclT (R.MY (D.R.m - 1)) (R.ItX φX (PiTensorProduct.tprod ℂ dX))) = 1 := by
  atlas_forward_decl GlobalTheory.Mem.UnitPairing.exists_unit_vectors
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.Mem.SchurTensor

theorem ellT_inclT_tprod {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : ∀ τ, M.H τ) (v : M.Vec) :
    ellT M w (inclT M (PiTensorProduct.tprod ℂ v)) = ∏ τ, ⟪w τ, (v τ : M.H τ)⟫_ℂ := by
  simp [ellT, inclT]

theorem schur_tensor : ∀ (D : D7) (θ : InfF D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), SchurMult θ M J χ μ 𝓕 → IsInfFam θ → IsQuot V μ 𝓕 → ∀ x ∈ MultT θ M J χ, ∀ y ∈ MultT θ M J χ, ∀ (v : SmT M) (w : M.Vec), IsCuspForm θ V (y (PiTensorProduct.tprod ℂ w)) ∧ IntegrableOn (fun g => star (x v g) * y (PiTensorProduct.tprod ℂ w) g) 𝓕 μ ∧ ∫ g in 𝓕, star (x v g) * y (PiTensorProduct.tprod ℂ w) g ∂μ = ipT M μ 𝓕 y x * star (ellT M (fun τ => (w τ : M.H τ)) (inclT M v)) := by
  intro D θ V S M J χ μ 𝓕 hS hθ hq x hx y hy v w
  have hx' := (mem_multT θ M J χ x).1 hx
  have hy' := (mem_multT θ M J χ y).1 hy
  have hm := (GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ _).1 hy'
  have hI := ipM_spec M μ 𝓕 _ _ (hS hθ hq.1 hq.2 _ hx' _ hy')
  refine ⟨⟨hm.aut w, hm.cusp w⟩, ?_⟩
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c u =>
    obtain ⟨h1, h2⟩ := hI u w
    have e : (fun g => star (x (c • PiTensorProduct.tprod ℂ u) g) * y (PiTensorProduct.tprod ℂ w) g) =
        fun g => star c * (star (x (PiTensorProduct.tprod ℂ u) g) * y (PiTensorProduct.tprod ℂ w) g) := by
      funext g
      rw [map_smul, Pi.smul_apply, smul_eq_mul, star_mul', mul_assoc]
    rw [e]
    refine ⟨h1.const_mul _, ?_⟩
    rw [integral_const_mul, map_smul, map_smul, ellT_inclT_tprod, smul_eq_mul, star_mul', star_prod]
    refine (congrArg (star c * ·) h2).trans ?_
    have e2 : ∏ τ, star ⟪(w τ : M.H τ), (u τ : M.H τ)⟫_ℂ = ∏ τ, ⟪(u τ : M.H τ), (w τ : M.H τ)⟫_ℂ :=
      Finset.prod_congr rfl fun τ _ => inner_conj_symm _ _
    rw [e2, ipT]
    ring
  | add a b ha hb =>
    have e : (fun g => star (x (a + b) g) * y (PiTensorProduct.tprod ℂ w) g) =
        fun g => star (x a g) * y (PiTensorProduct.tprod ℂ w) g + star (x b g) * y (PiTensorProduct.tprod ℂ w) g := by
      funext g
      rw [map_add, Pi.add_apply, star_add, add_mul]
    rw [e]
    refine ⟨ha.1.add hb.1, ?_⟩
    rw [integral_add ha.1 hb.1, ha.2, hb.2, map_add, map_add, star_add, mul_add]

end GlobalTheory.Mem.SchurTensor
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Mem.QuotHaar

theorem exists_pos_isQuotInt : ∀ (D : D7) (V : HSp D), V.SigOK → ∀ ν : Measure (GA D V), ν.IsHaarMeasure → ∃ r : ℝ, 0 < r ∧
    ∀ 𝓕, IsFundamentalDomain (GQ V) 𝓕 ν → ∀ φ : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) → IntegrableOn φ 𝓕 ν →
      GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V r φ (∫ g in 𝓕, φ g ∂ν) := by
  intro D V hV ν hν
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨μ₀, hμ₀, huniq⟩ := GlobalTheory.Mem.VolMeasure.existsUnique_isVolMeasG D V hV
  haveI := hμ₀.1
  obtain ⟨-, 𝓕₀, h𝓕₀⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ₀ hμ₀.1
  have e : ν = Measure.haarScalarFactor ν μ₀ • μ₀ := Measure.isMulLeftInvariant_eq_smul ν μ₀
  have cpos : 0 < Measure.haarScalarFactor ν μ₀ := Measure.haarScalarFactor_pos_of_isHaarMeasure ν μ₀
  set c := Measure.haarScalarFactor ν μ₀
  refine ⟨c, by exact_mod_cast cpos, ?_⟩
  intro 𝓕 h𝓕 φ hφ hint
  refine ⟨⟨(μ₀, 𝓕₀), hμ₀, h𝓕₀⟩, ?_⟩
  rintro ⟨m, F'⟩ ⟨hm, hF'⟩
  obtain rfl : m = μ₀ := huniq m hm
  have e' : m = c⁻¹ • ν := by rw [e, smul_smul, inv_mul_cancel₀ cpos.ne', one_smul]
  have hac : m ≪ ν := by
    rw [e']
    exact Measure.smul_absolutelyContinuous
  have h𝓕' : IsFundamentalDomain (GQ V) 𝓕 m := h𝓕.mono hac
  have hinv : ∀ (γ : GQ V) (g : GA D V), φ (γ • g) = φ g := fun γ g => hφ γ γ.2 g
  have hint' : IntegrableOn φ 𝓕 m := by
    rw [e', IntegrableOn, Measure.restrict_smul, ENNReal.smul_def]
    exact hint.smul_measure ENNReal.coe_ne_top
  refine ⟨(h𝓕'.integrableOn_iff hF' hinv).1 hint', ?_⟩
  simp only
  rw [← h𝓕'.setIntegral_eq hF' hinv]
  conv_lhs => rw [e]
  rw [Measure.restrict_smul, integral_smul_nnreal_measure]
  simp [NNReal.smul_def, Complex.real_smul]

end GlobalTheory.Mem.QuotHaar

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.Mem.OrientedKer

variable {D : D7}

theorem toTWsmall_zero (S T : HSp D) : toTWsmall S T 0 = 0 := by
  unfold toTWsmall
  rw [Matrix.zero_mul, Matrix.transpose_zero]

theorem ker_eq_thetaKO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (Wf : WeilFun D ψ) (S T : HSp D) (χS χT : IdC D), S.rank < T.rank → admitted T S χT χS → ∀ om, IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∃ Φ : ThS ψ T S, (f ≠ 0 → Φ ≠ 0) ∧ ∀ g h, Wf.ker T S χT χS Φ h g = thetaKO om g h f := by
  intro D ψ hψ Wf S T χS χT hr ha om H f hf
  have ha' : admitted S T χS χT := ⟨ha.1.symm, ha.2.2.1, ha.2.1, ha.2.2.2.2, ha.2.2.2.1⟩
  obtain ⟨omO, H', e⟩ := GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO D ψ hψ S T χS χT _ ha' hr (Wf.core.weil S T χS χT ha')
  obtain ⟨E, -, -, hE, -, -, -, h7, -⟩ := GlobalTheory.OrientedCoord.exists_coord D S T hr.le

  have hf0 : IsThetaFun ψ S T fun y => f (E.symm y) := by
    refine (h7 ψ _).1 ?_
    simp only [AddEquiv.symm_apply_apply]
    exact hf
  let Φ₀ : ThS ψ S T := ⟨fun y => f (E.symm y), mem_ThS.2 hf0⟩
  have hfΦ : f = fun x => Φ₀.1 (toTWsmall S T x) := by
    funext x
    simp only [Φ₀, ← hE, AddEquiv.symm_apply_apply]

  have hΦt : IsThetaFun ψ T S fun x => Φ₀.1 x.transpose :=
    (GlobalTheory.Mem.ThetaClosed.thetaFun_closed D ψ hψ S T Φ₀.1).2.2 hr.ne (mem_ThS.1 Φ₀.2)
  let Φ : ThS ψ T S := ⟨fun x => Φ₀.1 x.transpose, mem_ThS.2 hΦt⟩
  refine ⟨Φ, fun h0 hΦ => h0 ?_, fun g h => ?_⟩
  · funext x
    have := congrFun (congrArg Subtype.val hΦ) (E x).transpose
    simp only [Φ, Φ₀, Matrix.transpose_transpose, AddEquiv.symm_apply_apply, Submodule.coe_zero, Pi.zero_apply] at this
    exact this
  · have hs := Wf.om_swap S T χS χT ha' g h Φ₀ Φ (fun x => congrArg Φ₀.1 (Matrix.transpose_transpose x)) 0
    rw [Matrix.transpose_zero] at hs
    have e1 := congrFun (e (g, h) Φ₀) 0
    rw [toTWsmall_zero, ← hfΦ] at e1
    have e2 := GlobalTheory.WeilUniq.weilDatum_unique D ψ hψ S T χS χT omO om H' H (g, h) f hf
    unfold WeilFun.ker thetaKO
    rw [hs, ← e2]
    exact e1.symm

end GlobalTheory.Mem.OrientedKer

end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

noncomputable section
namespace GlobalTheory.Mem.OneTuple

variable {D : D7}

def castG {V V' : HSp D} (h : V = V') : GA D V ≃* GA D V' := h ▸ MulEquiv.refl _

@[simp] theorem castG_rfl (V : HSp D) : castG (rfl : V = V) = MulEquiv.refl _ := rfl

def Moves (V V' : HSp D) (κ : GA D V ≃* GA D V') : Prop :=
  Continuous κ ∧ Continuous κ.symm ∧ (∀ g, κ g ∈ GQ V' ↔ g ∈ GQ V) ∧
    (∀ θ : InfF D, IsInfFam θ → ∀ F, IsCuspForm θ V F → IsCuspForm θ V' fun h => F (κ.symm h)) ∧
    ∀ (ψ : AddChar (AF D.host.F) ℂ) (S : HSp D) (χ χ' : IdC D) om, IsWeilDatumO ψ S V χ χ' om →
      ∃ om', IsWeilDatumO ψ S V' χ χ' om' ∧ ∀ f, IsThetaFunO ψ S V f →
        ∃ f', IsThetaFunO ψ S V' f' ∧ (f ≠ 0 → f' ≠ 0) ∧ ∀ g h, thetaKO om' g (κ h) f' = thetaKO om g h f

theorem moves_castG {V V' : HSp D} (h : V = V') : Moves V V' (castG h) := by
  subst h
  refine ⟨continuous_id, continuous_id, fun g => Iff.rfl, fun θ _ F hF => hF, fun ψ S χ χ' om hom => ⟨om, hom, fun f hf => ⟨f, hf, id, fun g h => rfl⟩⟩⟩

theorem isQuotInt_rescale {V : HSp D} {c : ℝ} (hc : c ≠ 0) (κ : ℝ) {φ : GA D V → ℂ} {z : ℂ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V c φ z) : GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V κ φ (((κ / c : ℝ) : ℂ) * z) := by
  refine ⟨h.1, fun m hm => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 m hm
  refine ⟨h1, ?_⟩
  rw [h2, ← mul_assoc, ← Complex.ofReal_mul, div_mul_cancel₀ _ hc]

theorem quot_transport {V V' : HSp D} {κ : GA D V ≃* GA D V'} (hκ : Moves V V' κ) (hV' : V'.SigOK)
    {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hq : IsQuot V ν 𝓕) : ∃ r : ℝ, 0 < r ∧
    ∀ φ : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) → IntegrableOn φ 𝓕 ν →
      GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V' r (fun h => φ (κ.symm h)) (∫ g in 𝓕, φ g ∂ν) := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V'
  haveI := hq.1
  let H : GA D V ≃ₜ GA D V' := { toEquiv := κ.toEquiv, continuous_toFun := hκ.1, continuous_invFun := hκ.2.1 }
  let E : GA D V ≃ᵐ GA D V' := H.toMeasurableEquiv
  haveI : (ν.map κ).IsHaarMeasure := MulEquiv.isHaarMeasure_map ν κ hκ.1 hκ.2.1
  obtain ⟨r, hr, hR⟩ := GlobalTheory.Mem.QuotHaar.exists_pos_isQuotInt D V' hV' (ν.map κ) inferInstance
  refine ⟨r, hr, fun φ hφ hint => ?_⟩
  have hmap : ν.map κ = ν.map E := rfl
  have hmem : ∀ g : GA D V', g ∈ GQ V' ↔ κ.symm g ∈ GQ V := fun g => by
    rw [← hκ.2.2.1, MulEquiv.apply_symm_apply]
  let e : GQ V' ≃ GQ V :=
    { toFun := fun g => ⟨κ.symm g, (hmem g).1 g.2⟩
      invFun := fun g => ⟨κ g, (hκ.2.2.1 g).2 g.2⟩
      left_inv := fun g => Subtype.ext (κ.apply_symm_apply _)
      right_inv := fun g => Subtype.ext (κ.symm_apply_apply _) }
  have hF : IsFundamentalDomain (GQ V') (κ '' 𝓕) (ν.map κ) := by
    have := hq.2.image_of_equiv (ν := ν.map κ) E.toEquiv (by rw [hmap]; exact E.quasiMeasurePreserving_symm ν) e
      (fun g x => by
        show κ (κ.symm g * x) = g * κ x
        rw [map_mul, MulEquiv.apply_symm_apply])
    exact this
  have hinv : ∀ γ ∈ GQ V', ∀ g, (fun h => φ (κ.symm h)) (γ * g) = (fun h => φ (κ.symm h)) g := by
    intro γ hγ g
    simp only [map_mul]
    exact hφ _ ((hmem γ).1 hγ) _
  have hpre : E ⁻¹' (κ '' 𝓕) = 𝓕 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_image]
    refine ⟨fun ⟨y, hy, hxy⟩ => ?_, fun hx => ⟨x, hx, rfl⟩⟩
    have : y = x := κ.injective hxy
    exact this ▸ hy
  have hcomp : (fun h => φ (κ.symm h)) ∘ E = φ := funext fun x => by
    show φ (κ.symm (κ x)) = φ x
    rw [MulEquiv.symm_apply_apply]
  have hint' : IntegrableOn (fun h => φ (κ.symm h)) (κ '' 𝓕) (ν.map κ) := by
    rw [hmap, E.measurableEmbedding.integrableOn_map_iff, hcomp, hpre]
    exact hint
  have := hR _ hF _ hinv hint'
  convert this using 2
  rw [hmap, E.measurableEmbedding.setIntegral_map, hpre]
  exact (congrArg (fun f => ∫ g in 𝓕, f g ∂ν) hcomp).symm
end GlobalTheory.Mem.OneTuple
end

noncomputable section
namespace GlobalTheory.Mem.OneTuple
variable {D : D7}

theorem multT_left {θ : InfF D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {X : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hX : X ∈ MultT θ M J χ) (v : SmT M) :
    ∀ γ ∈ GQ V, ∀ g, X v (γ * g) = X v g := by
  have hm := (GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ _).1 ((mem_multT θ M J χ X).1 hX)
  intro γ hγ g
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c u =>
    have h1 := (hm.aut u).left γ hγ g
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    congr 1
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

theorem level (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfF D} (hθ : IsInfFam θ) {V V' : HSp D} {κ : GA D V ≃* GA D V'}
    (hκ : Moves V V' κ) (hV' : V'.SigOK) {S : D.what₂.Tau → SPar} (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)
    {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hq : IsQuot V ν 𝓕) : ∃ r : ℝ, 0 < r ∧
    ∀ X ∈ MultT θ M J χ, ∀ Y ∈ MultT θ M J χ, ∀ (v : SmT M) (w : M.Vec),
      GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V' r (fun h => star (X v (κ.symm h)) * Y (PiTensorProduct.tprod ℂ w) (κ.symm h))
        (ipT M ν 𝓕 Y X * star (ellT M (fun τ => (w τ : M.H τ)) (inclT M v))) := by
  obtain ⟨r, hr, hR⟩ := quot_transport hκ hV' hq
  refine ⟨r, hr, fun X hX Y hY v w => ?_⟩
  obtain ⟨-, h1, h2⟩ := GlobalTheory.Mem.SchurTensor.schur_tensor D θ V S M J χ ν 𝓕 (GlobalTheory.MultFinite.schurMult hP ν 𝓕) hθ hq X hX Y hY v w
  rw [← h2]
  refine hR (fun g => star (X v g) * Y (PiTensorProduct.tprod ℂ w) g) (fun γ hγ g => ?_) h1
  simp only [multT_left hX v γ hγ g, multT_left hY _ γ hγ g]

end GlobalTheory.Mem.OneTuple
end

noncomputable section
namespace GlobalTheory.Mem.OneTuple
variable {D : D7}

theorem isQuotInt_const_mul {V : HSp D} {c : ℝ} {φ : GA D V → ℂ} {z : ℂ} (a : ℂ)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V c φ z) : GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V c (fun g => a * φ g) (a * z) := by
  refine ⟨h.1, fun m hm => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 m hm
  refine ⟨h1.const_mul a, ?_⟩
  rw [h2, integral_const_mul]
  ring

theorem isQuotInt_congr {V : HSp D} {c : ℝ} {φ ψ : GA D V → ℂ} {z w : ℂ} (hf : φ = ψ) (hz : z = w)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V c φ z) : GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V c ψ w := hf ▸ hz ▸ h

theorem ellT_unit {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (d : M.Vec) (hd : ∀ τ, ‖(d τ : M.H τ)‖ = 1) :
    ellT M (fun τ => (d τ : M.H τ)) (inclT M (PiTensorProduct.tprod ℂ d)) = 1 := by
  rw [GlobalTheory.Mem.SchurTensor.ellT_inclT_tprod]
  refine Finset.prod_eq_one fun τ _ => ?_
  rw [inner_self_eq_norm_sq_to_K, hd τ]
  simp

theorem levelRow (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfF D} (hθ : IsInfFam θ) {V V' : HSp D} {κ : GA D V ≃* GA D V'}
    (hκ : Moves V V' κ) (hV' : V'.SigOK) {S : D.what₂.Tau → SPar} (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)
    {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hq : IsQuot V ν 𝓕) {N : Type} [NormedAddCommGroup N] [InnerProductSpace ℂ N]
    (e : N →ₗ[ℂ] MultT θ M J χ) {c : ℝ} (hc : 0 < c) (hip : ∀ x y, ⟪x, y⟫_ℂ = (c : ℂ) * ipT M ν 𝓕 (e y).1 (e x).1)
    (d : M.Vec) (hd : ∀ τ, ‖(d τ : M.H τ)‖ = 1) {kq : ℝ} (hkq : 0 < kq) :
    ∃ s r : ℝ, 0 < s ∧ 0 < r ∧ s ^ 2 * (kq / r) = c ∧ ∃ row : N →ₗ[ℂ] CuspS θ V',
      (∀ x h, (row x).1 h = (s : ℂ) * (e x).1 (PiTensorProduct.tprod ℂ d) (κ.symm h)) ∧
      (∀ x y, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V' kq (fun h => star ((row x).1 h) * (row y).1 h) ⟪x, y⟫_ℂ) ∧
      ∀ X ∈ MultT θ M J χ, ∀ (v : SmT M) (x : N),
        GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V' r (fun h => star (X v (κ.symm h)) * (e x).1 (PiTensorProduct.tprod ℂ d) (κ.symm h))
          (ipT M ν 𝓕 (e x).1 X * star (ellT M (fun τ => (d τ : M.H τ)) (inclT M v))) := by
  obtain ⟨r, hr, hR⟩ := level hP hθ hκ hV' M J χ hq
  have hcf : ∀ x, IsCuspForm θ V' fun h => (e x).1 (PiTensorProduct.tprod ℂ d) (κ.symm h) := fun x =>
    hκ.2.2.2.1 θ hθ _ (GlobalTheory.Mem.SchurTensor.schur_tensor D θ V S M J χ ν 𝓕 (GlobalTheory.MultFinite.schurMult hP ν 𝓕) hθ hq _ (e x).2 _ (e x).2
      (PiTensorProduct.tprod ℂ d) d).1
  set s := Real.sqrt (c * r / kq) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 * (kq / r) = c := by
    rw [hs, Real.sq_sqrt (by positivity)]
    field_simp
  let row : N →ₗ[ℂ] CuspS θ V' :=
    { toFun := fun x => ⟨fun h => (s : ℂ) * (e x).1 (PiTensorProduct.tprod ℂ d) (κ.symm h),
        Submodule.smul_mem _ (s : ℂ) (Submodule.subset_span (hcf x))⟩
      map_add' := fun x y => by
        apply Subtype.ext
        funext h
        simp [mul_add]
      map_smul' := fun a x => by
        apply Subtype.ext
        funext h
        simp only [map_smul, Submodule.coe_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  refine ⟨s, r, hs0, hr, hs2, row, fun x h => rfl, fun x y => ?_, fun X hX v x => hR X hX _ (e x).2 v d⟩
  have h1 := isQuotInt_const_mul ((s : ℂ) ^ 2) (isQuotInt_rescale hr.ne' kq (hR _ (e x).2 _ (e y).2 (PiTensorProduct.tprod ℂ d) d))
  refine isQuotInt_congr (funext fun h => ?_) ?_ h1
  · simp only [row, LinearMap.coe_mk, AddHom.coe_mk, star_mul', Complex.star_def, Complex.conj_ofReal]
    ring
  · rw [ellT_unit M d hd, star_one, mul_one, hip, ← hs2]
    push_cast
    ring

end GlobalTheory.Mem.OneTuple
end

noncomputable section
namespace GlobalTheory.Mem.OneTuple
variable {D : D7}

theorem ipT_swap (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfF D} (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} (hq : IsQuot V μ 𝓕)
    (d : M.Vec) (hd : ∀ τ, ‖(d τ : M.H τ)‖ = 1) {X Y : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hX : X ∈ MultT θ M J χ)
    (hY : Y ∈ MultT θ M J χ) : ipT M μ 𝓕 X Y = star (ipT M μ 𝓕 Y X) := by
  haveI := hq.1
  have hS : SchurMult θ M J χ μ 𝓕 := GlobalTheory.MultFinite.schurMult hP μ 𝓕
  obtain ⟨c, hc⟩ := hS hθ hq.1 hq.2 _ ((mem_multT θ M J χ X).1 hX) _ ((mem_multT θ M J χ Y).1 hY)
  have h1 := ipM_spec M μ 𝓕 _ _ ⟨c, hc⟩
  have hsw : IsMultIP M μ 𝓕 (PiTensorProduct.lift.symm Y) (PiTensorProduct.lift.symm X) (star c) := by
    intro v v'
    obtain ⟨i1, i2⟩ := hc v' v
    have e : (fun g => star ((PiTensorProduct.lift.symm Y) v g) * (PiTensorProduct.lift.symm X) v' g) =
        fun g => star (star ((PiTensorProduct.lift.symm X) v' g) * (PiTensorProduct.lift.symm Y) v g) := by
      funext g; rw [star_mul', star_star, mul_comm]
    have hI : IntegrableOn (fun g => star ((PiTensorProduct.lift.symm Y) v g) * (PiTensorProduct.lift.symm X) v' g) 𝓕 μ := by
      rw [e]
      exact (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ).integrable_comp i1
    have hE : ∫ g in 𝓕, star ((PiTensorProduct.lift.symm Y) v g) * (PiTensorProduct.lift.symm X) v' g ∂μ =
        star c * ∏ τ, ⟪(v τ : M.H τ), (v' τ : M.H τ)⟫_ℂ := by
      rw [e]
      have := integral_conj (μ := μ.restrict 𝓕) (f := fun g => star ((PiTensorProduct.lift.symm X) v' g) * (PiTensorProduct.lift.symm Y) v g)
      simp only [Complex.star_def] at this i2 ⊢
      rw [this, i2, map_mul, map_prod]
      congr 1
      exact Finset.prod_congr rfl fun τ _ => inner_conj_symm _ _
    exact ⟨hI, hE⟩
  have hu := hasPeterssonInner_unique M μ 𝓕 _ _ d (by
    rw [Finset.prod_eq_one fun τ _ => by rw [inner_self_eq_norm_sq_to_K, hd τ]; simp]; exact one_ne_zero)
    (ipM_spec M μ 𝓕 _ _ ⟨_, hsw⟩) hsw
  unfold ipT
  rw [hu]
  have hv := hasPeterssonInner_unique M μ 𝓕 _ _ d (by
    rw [Finset.prod_eq_one fun τ _ => by rw [inner_self_eq_norm_sq_to_K, hd τ]; simp]; exact one_ne_zero) h1 hc
  rw [hv]

end GlobalTheory.Mem.OneTuple
end

noncomputable section
namespace GlobalTheory.Mem.OneTuple
variable {D : D7}

theorem ker_smul {ψ : AddChar (AF D.host.F) ℂ} (Wf : WeilFun D ψ) (V W : HSp D) (χ χ' : IdC D) (a : ℂ) (Φ : ThS ψ V W)
    (g : GA D V) (h : GA D W) : Wf.ker V W χ χ' (a • Φ) g h = a * Wf.ker V W χ χ' Φ g h := by
  unfold WeilFun.ker
  rw [map_smul]
  rfl

theorem thetaKO_left {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : IdC D} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∀ γ ∈ GQ T, ∀ g h, thetaKO om g (γ * h) f = thetaKO om g h f := by
  intro γ hγ g h
  unfold thetaKO
  have e : ((g, γ * h) : GA D S × GA D T) = (1, γ) * (g, h) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hom.om_aut 1 (one_mem _) γ hγ _ (hom.om_pres _ f hf)

theorem step (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfF D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ}
    (Wf : WeilFun D ψ) {V V' W W' : HSp D} (hV : V = V') {κ : GA D W ≃* GA D W'} (hκ : Moves W W' κ) (hW' : W'.SigOK)
    (hrk : V'.rank < W'.rank) {χS χT : IdC D} (hS : IsHC D χS) (hT : IsHC D χT)
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hom : IsWeilDatumO ψ V W χS χT om)
    {SV SW : D.what₂.Tau → SPar} (MV : DSModel V SV) (MW : DSModel W SW) (JV : Set (GA D V)) (χV : GA D V → ℂ)
    (JW : Set (GA D W)) (χW : GA D W → ℂ) (CCs : Submodule ℂ (SmT MW →ₗ[ℂ] (GA D W → ℂ)))
    (hCC : CCs ≤ MultT θ MW JW χW) {νW : Measure (GA D W)} {𝓕W : Set (GA D W)} (hqW : IsQuot W νW 𝓕W)
    {νV : Measure (GA D V)} {𝓕V : Set (GA D V)} (hqV : IsQuot V νV 𝓕V)
    {pt : PolF D W.rank V.rank → (WO V W → ℂ)} (hpt : ∀ P, IsThetaFunO ψ V W (pt P))
    {It : PolF D W.rank V.rank →ₗ[ℂ] SmT MW →ₗ[ℂ] SmT MV} {io : CCs →ₗ[ℂ] MultT θ MV JV χV}
    (hio : Lift.IsIo νW 𝓕W (thetaKO om) pt It CCs (MultT θ MV JV χV) io)
    (φ : PolF D W.rank V.rank) (hφ : pt φ ≠ 0) (d : MV.Vec) (hd : ∀ τ, ‖(d τ : MV.H τ)‖ = 1) (d' : MW.Vec)
    (h1 : ellT MV (fun τ => (d τ : MV.H τ)) (inclT MV (It φ (PiTensorProduct.tprod ℂ d'))) = 1)
    {NV NW : Type} [NormedAddCommGroup NV] [InnerProductSpace ℂ NV] [NormedAddCommGroup NW] [InnerProductSpace ℂ NW]
    (ioN : NW →ₗ[ℂ] NV) (eV : NV →ₗ[ℂ] MultT θ MV JV χV) (eW : NW →ₗ[ℂ] CCs) {cV : ℝ} (hcV : 0 < cV)
    (hioN : ∀ x y, ⟪x, ioN y⟫_ℂ = (cV : ℂ) * ipT MV νV 𝓕V (io (eW y)).1 (eV x).1)
    (rowV : NV →ₗ[ℂ] CuspS θ V') (rowW : NW →ₗ[ℂ] CuspS θ W') {sV rV sW kV kW : ℝ} (hsV : 0 < sV) (hrV : 0 < rV)
    (hsW : 0 < sW) (hkV : 0 < kV) (hkW : 0 < kW)
    (hrowV : ∀ x g, (rowV x).1 g = (sV : ℂ) * (eV x).1 (PiTensorProduct.tprod ℂ d) ((castG hV).symm g))
    (hpairV : ∀ X ∈ MultT θ MV JV χV, ∀ (v : SmT MV) (x : NV),
      GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V' rV
        (fun g => star (X v ((castG hV).symm g)) * (eV x).1 (PiTensorProduct.tprod ℂ d) ((castG hV).symm g))
        (ipT MV νV 𝓕V (eV x).1 X * star (ellT MV (fun τ => (d τ : MV.H τ)) (inclT MV v))))
    (hrowW : ∀ y h, (rowW y).1 h = (sW : ℂ) * ((eW y).1 : SmT MW →ₗ[ℂ] (GA D W → ℂ)) (PiTensorProduct.tprod ℂ d') (κ.symm h)) :
    ∃ Φ : ThS ψ W' V', Φ ≠ 0 ∧ ∀ y : NW, ∃ L : GA D V' → ℂ,
      (∀ g, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt W' kW (fun h => Wf.ker W' V' χT χS Φ h g * (rowW y).1 h) (L g)) ∧
      ∀ x : NV, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V' kV (fun g => star (L g) * (rowV x).1 g) (inner ℂ (ioN y) x) := by
  subst hV
  obtain ⟨rW, hrW, hRW⟩ := quot_transport hκ hW' hqW
  obtain ⟨om', hom', hmv⟩ := hκ.2.2.2.2 ψ V χS χT om hom
  obtain ⟨f', hf', hf'0, hf'eq⟩ := hmv (pt φ) (hpt φ)
  obtain ⟨Φ0, hΦ0, hker⟩ := GlobalTheory.Mem.OrientedKer.ker_eq_thetaKO D ψ hom'.std Wf V W' χS χT hrk ⟨hrk.ne', hT, hS, hom'.resT, hom'.resS⟩ om' hom' f' hf'
  set a : ℝ := cV * rV * rW / (kV * kW * sV * sW) with ha
  have ha0 : 0 < a := by positivity
  refine ⟨(a : ℂ) • Φ0, smul_ne_zero (by exact_mod_cast ha0.ne') (hΦ0 (hf'0 hφ)), fun y => ?_⟩
  have hFm : ((eW y : CCs) : SmT MW →ₗ[ℂ] (GA D W → ℂ)) ∈ MultT θ MW JW χW := hCC (eW y).2
  refine ⟨fun g => (((kW / rW) * a * sW : ℝ) : ℂ) * ((io (eW y)).1 : SmT MV →ₗ[ℂ] (GA D V → ℂ)) (It φ (PiTensorProduct.tprod ℂ d')) g,
    fun g => ?_, fun x => ?_⟩
  · have hinv : ∀ γ ∈ GQ W, ∀ h, (fun h => thetaKO om g h (pt φ) * ((eW y : CCs) : SmT MW →ₗ[ℂ] (GA D W → ℂ)) (PiTensorProduct.tprod ℂ d') h) (γ * h) =
        (fun h => thetaKO om g h (pt φ) * ((eW y : CCs) : SmT MW →ₗ[ℂ] (GA D W → ℂ)) (PiTensorProduct.tprod ℂ d') h) h := by
      intro γ hγ h
      simp only [thetaKO_left hom (hpt φ) γ hγ g h, multT_left hFm _ γ hγ h]
    have hq := hRW _ hinv (hio.integ (eW y) φ (PiTensorProduct.tprod ℂ d') g)
    have hval := hio.eq (eW y) φ (PiTensorProduct.tprod ℂ d') g
    unfold Lift.liftInt at hval
    rw [hval] at hq
    have h2 := isQuotInt_const_mul ((a * sW : ℝ) : ℂ) (isQuotInt_rescale hrW.ne' kW hq)
    refine isQuotInt_congr (funext fun h => ?_) ?_ h2
    · rw [ker_smul, hker, hrowW, ← hf'eq g (κ.symm h), MulEquiv.apply_symm_apply]
      push_cast
      ring
    · push_cast
      ring
  · have hX := (io (eW y)).2
    have h3 := isQuotInt_const_mul ((((kW / rW) * a * sW : ℝ) : ℂ) * sV)
      (isQuotInt_rescale hrV.ne' kV (hpairV _ hX (It φ (PiTensorProduct.tprod ℂ d')) x))
    refine isQuotInt_congr (funext fun g => ?_) ?_ h3
    · rw [hrowV]
      simp only [castG_rfl, MulEquiv.refl_symm, MulEquiv.refl_apply, star_mul', Complex.star_def, Complex.conj_ofReal]
      ring
    · rw [h1, star_one, mul_one, ← inner_conj_symm, hioN,
        ipT_swap hP hθ MV JV χV hqV d hd (eV x).2 hX]
      have hnum : (kW / rW) * a * sW * sV * (kV / rV) = cV := by
        rw [ha]; field_simp
      rw [map_mul, Complex.conj_ofReal, ← Complex.star_def, ← hnum]
      push_cast
      ring

end GlobalTheory.Mem.OneTuple
end

noncomputable section
namespace GlobalTheory.Mem.OneTuple
variable {D : D7}

theorem tau_nonempty (D : D7) : Nonempty D.what₂.Tau :=
  Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]
    show 0 < 2 * D.R.n
    unfold Formalism.BasicNotions.Ranks.n
    positivity)

theorem pt_ne_zero {V W : HSp D} {S S' : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {M' : DSModel W S'}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {pt : PolF D W.rank V.rank → (WO V W → ℂ)}
    {It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M} (hI : IsItW θ M M' ω pt It) (hpt0 : pt 0 = 0)
    {φ : PolF D W.rank V.rank} {v : SmT M'} (hv : inclT M (It φ v) ≠ 0) : pt φ ≠ 0 := by
  intro h0
  obtain ⟨τ⟩ := tau_nonempty D
  have h1 : (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
    simp [Formalism.QuantumDeterminants.UH]
  have h := hI.eqK τ 1 h1 φ 0 (by rw [hpt0, h0, map_zero]) v
  rw [map_zero, LinearMap.zero_apply, map_zero] at h
  have hrep : M.rep τ 1 = 1 := by
    unfold DSModel.rep
    rw [mul_one, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ))]
    exact (M.ds τ).2.2.1.1.1
  have hid : actT M τ 1 = LinearMap.id := by
    classical
    unfold actT
    rw [hrep]
    have : Function.update (fun ρ => (LinearMap.id : M.H ρ →ₗ[ℂ] M.H ρ)) τ ((1 : M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ) =
        fun ρ => LinearMap.id := by
      funext ρ
      by_cases hρ : ρ = τ
      · subst hρ; simp; rfl
      · simp [Function.update_of_ne hρ]
    rw [this, PiTensorProduct.map_id]
  rw [hid, LinearMap.id_apply] at h
  exact hv h.symm

theorem isHC_inv {χ : IdC D} (h : IsHC D χ) : IsHC D χ⁻¹ := by
  refine ⟨⟨h.1.1.inv, fun x => by rw [MonoidHom.inv_apply, h.1.2 x, inv_one]⟩, fun τ => ?_⟩
  obtain ⟨a, ha⟩ := h.2 τ
  exact ⟨-a, GlobalTheory.Mem.HeckeExp.hasInfExp_inv ha⟩

theorem isHC_mu {T : Type} (L : LevCh D T) {μ0 : T} (hL : L.Is μ0) (t : T) (i : Fin D.R.m) :
    IsHC D (L.mu t ((i : ℕ) + 1)) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have h1 : IsHC D (L.mu0 ((i : ℕ) + 1)) := ⟨(hL.mu0 i).1, fun τ =>
    ⟨_, GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 i) (GlobalTheory.Chain.StepVac.hasInfQ_tau (L.C.isMu0 i).inf) τ⟩⟩
  have h2 : IsHC D (L.xi t) := ⟨(hL.xi t).1, fun τ => ⟨_, GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hL.xi t) hn ho τ⟩⟩
  exact h1.mul h2

theorem isHC_eta {T : Type} (L : LevCh D T) {μ0 : T} (hL : L.Is μ0) : IsHC D L.eta :=
  ⟨hL.eta.1, fun τ => ⟨_, GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
    (GlobalTheory.Chain.StepVac.hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, L.C.isEta.inf⟩) τ⟩⟩

theorem chrStep_eq {C : Type} [CommGroup C] (μ : ℕ → C) (η : C) (j : ℕ) :
    Lift.chrStep μ η (j + 1) = (if Even j then μ (j + 1) * η⁻¹ else μ (j + 1),
      if Even (j + 1) then μ (j + 1) * η⁻¹ else μ (j + 1)) := by
  unfold Lift.chrStep
  rcases Nat.even_or_odd j with h | h
  · have h1 : Odd (j + 1) := h.add_one
    have h2 : ¬ Even (j + 1) := Nat.not_even_iff_odd.2 h1
    simp [h, h1, h2]
  · have h1 : ¬ Odd (j + 1) := Nat.not_odd_iff_even.2 h.add_one
    have h2 : Even (j + 1) := h.add_one
    have h3 : ¬ Even j := Nat.not_even_iff_odd.2 h
    simp [h1, h2, h3]

theorem isHC_step {T : Type} (L : LevCh D T) {μ0 : T} (hL : L.Is μ0) (t : T) (j : ℕ) (hj : j < D.R.m) :
    IsHC D (if Even j then L.mu t (j + 1) * L.eta⁻¹ else L.mu t (j + 1)) ∧
      IsHC D (if Even (j + 1) then L.mu t (j + 1) * L.eta⁻¹ else L.mu t (j + 1)) := by
  have h1 := isHC_mu L hL t ⟨j, hj⟩
  have h2 := h1.mul (isHC_inv (isHC_eta L hL))
  constructor <;> split_ifs <;> assumption

end GlobalTheory.Mem.OneTuple
end

noncomputable section
namespace GlobalTheory.Mem.OneTuple
variable {D : D7}

theorem famCast_heq (Sp : ℕ → Type) [∀ j, NormedAddCommGroup (Sp j)] [∀ j, InnerProductSpace ℂ (Sp j)] {i j : ℕ}
    (h : i = j) (x : Sp i) : HEq x (famCast Sp h x) := by
  subst h
  rfl

@[simp] theorem famCast_rfl (Sp : ℕ → Type) [∀ j, NormedAddCommGroup (Sp j)] [∀ j, InnerProductSpace ℂ (Sp j)] {i : ℕ}
    (x : Sp i) : famCast Sp (rfl : i = i) x = x := rfl

theorem yc_eq (D : D7) {j : ℕ} (hj : j < D.R.m) : Yc D j = D.sp.Y j := by
  unfold Yc
  rw [min_eq_left hj.le]

theorem rank_lt (D : D7) {j : ℕ} (hj : j < D.R.m) : (D.sp.Y j).rank < (D.sp.Y (j + 1)).rank := by
  rw [D.sp.Y_rank j hj.le, D.sp.Y_rank (j + 1) hj]
  unfold Formalism.BasicNotions.Ranks.rankY
  have := D.R.t_odd.pos
  nlinarith

end GlobalTheory.Mem.OneTuple
end

noncomputable section
namespace GlobalTheory.Mem.OneTuple

set_option maxHeartbeats 1000000 in
theorem topRow (hP : GlobalTheory.Published.CuspRapidDecay) {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (hM : R.IsModels) (t : T) (μ : D.what₂.Tup)
    (eX : D.what₂.Mult μ D.R.m →ₗ[ℂ] LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) (J : Set (GA D D.sp.X'))
    (χ : GA D D.sp.X' → ℂ) (hJ : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) ≤ MultT R.θ R.MX J χ) {cX : ℝ}
    (hcX : 0 < cX) (H3 : ∀ x y, ⟪x, y⟫_ℂ = (cX : ℂ) * ipT R.MX (R.νX t) (R.fdX t) (eX y).1 (eX x).1) (dX : R.MX.Vec)
    (hdX : ∀ τ, ‖(dX τ : R.MX.H τ)‖ = 1) {k : ℝ} (hk : 0 < k) (j : ℕ) (hj : j = D.R.m) :
    ∃ κT : GA D D.sp.X' ≃* GA D (D.sp.Y j), Moves D.sp.X' (D.sp.Y j) κT ∧
      ∃ s : ℝ, 0 < s ∧ ∃ row : D.what₂.Mult μ j →ₗ[ℂ] CuspS R.θ (D.sp.Y j),
      (∀ x h, (row x).1 h = (s : ℂ) * (eX (famCast (D.what₂.Mult μ) hj x)).1 (PiTensorProduct.tprod ℂ dX) (κT.symm h)) ∧
      (∀ x y, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) k (fun h => star ((row x).1 h) * (row y).1 h) ⟪x, y⟫_ℂ) := by
  subst hj
  have hiso0 := GlobalTheory.T.exists_transport_groups_cuspForms_weilData_isometry D D.sp.X' (D.sp.Y D.R.m) D.sp.eYm
  have hiso1 := D.sp.eYm_isom
  have hiso2 := hiso0 hiso1
  obtain ⟨κT, hκT⟩ := hiso2
  have hκM : Moves D.sp.X' (D.sp.Y D.R.m) κT := hκT
  let eT : D.what₂.Mult μ D.R.m →ₗ[ℂ] MultT R.θ R.MX J χ := (Submodule.inclusion hJ) ∘ₗ eX
  have hT : ∀ x y, ⟪x, y⟫_ℂ = (cX : ℂ) * ipT R.MX (R.νX t) (R.fdX t) (eT y).1 (eT x).1 := H3
  have hqX : IsQuot D.sp.X' (R.νX t) (R.fdX t) := ⟨(hM.νX t).1.1, (hM.νX t).2⟩
  have hθ : IsInfFam R.θ := hM.inf
  have hsig := D.sp.Y_sig D.R.m
  have L0 := levelRow (N := D.what₂.Mult μ D.R.m) hP hθ hκM hsig R.MX J χ hqX eT hcX hT dX hdX hk
  obtain ⟨s, r, hs, hr, -, row, hrow, hiso, -⟩ := L0
  exact ⟨κT, hκM, s, hs, row, hrow, hiso⟩

end GlobalTheory.Mem.OneTuple
end

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Mem.OneTuple.rows_theta : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsChain → ∀ (t : T) (μ : D.what₂.Tup), (∃ (e : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] R.CC t j) (eX : D.what₂.Mult μ D.R.m →ₗ[ℂ] LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) (ν : ∀ j, Measure (GA D (Yc D j))) (𝓕 : ∀ j, Set (GA D (Yc D j))) (c : ℕ → ℝ) (cX : ℝ), (∀ j, j < D.R.m → IsQuot (Yc D j) (ν j) (𝓕 j) ∧ 0 < c j ∧ ∀ x y, ⟪x, y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (e j y).1 (e j x).1) ∧ (∃ J χ, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) ≤ MultT R.θ R.MX J χ) ∧ 0 < cX ∧ (∀ x y, ⟪x, y⟫_ℂ = (cX : ℂ) * ipT R.MX (R.νX t) (R.fdX t) (eX y).1 (eX x).1) ∧ (∀ j, j + 1 < D.R.m → ∀ x y, ⟪x, D.what₂.io μ j y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (R.ioY t j (e (j + 1) y)).1 (e j x).1) ∧ ∀ x (y : D.what₂.Mult μ (D.R.m - 1 + 1)) (y' : D.what₂.Mult μ D.R.m), HEq y y' → ⟪x, D.what₂.io μ (D.R.m - 1) y⟫_ℂ = (c (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1)) (ν (D.R.m - 1)) (𝓕 (D.R.m - 1)) (R.ioX t (eX y')).1 (e (D.R.m - 1) x).1) → ∀ (Wf : WeilFun D R.ψ) (κ : ℕ → ℝ), (∀ j, 0 < κ j) → ∃ (row : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] CuspS R.θ (D.sp.Y j)) (Phi : ∀ j, ThS R.ψ (D.sp.Y (j + 1)) (D.sp.Y j)), (∀ j, j < D.R.m → Phi j ≠ 0) ∧ (∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (κ j) (fun h => star ((row j x).1 h) * (row j y).1 h) (inner ℂ x y)) ∧ ∀ j, j < D.R.m → ∀ y : D.what₂.Mult μ (j + 1), ∃ L : GA D (D.sp.Y j) → ℂ, (∀ g, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y (j + 1)) (κ (j + 1)) (fun h => Wf.ker _ _ (if Even (j + 1) then R.toLevCh.mu t (j + 1) * R.eta⁻¹ else R.toLevCh.mu t (j + 1)) (if Even j then R.toLevCh.mu t (j + 1) * R.eta⁻¹ else R.toLevCh.mu t (j + 1)) (Phi j) h g * (row (j + 1) y).1 h) (L g)) ∧ ∀ x : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (κ j) (fun g => star (L g) * (row j x).1 g) (inner ℂ (D.what₂.io μ j y) x) := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R hL hM hC t μ hyp Wf κ hκ
  obtain ⟨e, eX, ν, 𝓕, c, cX, H1, ⟨J, χ, hJ⟩, hcX, H3, H4, H5⟩ := hyp
  have hθ : IsInfFam R.θ := hM.inf
  have hm2 := D.R.two_le_m
  have hsigY := D.sp.Y_sig
  obtain ⟨d, dX, φ, φX, hd, hdX, hφ, hφX⟩ :=
    GlobalTheory.T.exists_polynomial_frame_maps_bounded D G Pl0 T A Ks R (fun k hk => (hC.ItY t k hk).ne) (hC.ItX t).ne

  have hlow : ∀ j (hj : j < D.R.m), ∃ s r : ℝ, 0 < s ∧ 0 < r ∧ s ^ 2 * (κ j / r) = c j ∧
      ∃ row : D.what₂.Mult μ j →ₗ[ℂ] CuspS R.θ (D.sp.Y j),
      (∀ x h, (row x).1 h = (s : ℂ) * (e j x).1 (PiTensorProduct.tprod ℂ (d j))
        ((GlobalTheory.Mem.OneTuple.castG (GlobalTheory.Mem.OneTuple.yc_eq D hj)).symm h)) ∧
      (∀ x y, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (κ j) (fun h => star ((row x).1 h) * (row y).1 h) ⟪x, y⟫_ℂ) ∧
      ∀ X ∈ R.CC t j, ∀ (v : SmT (R.MY j)) (x : D.what₂.Mult μ j),
        GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) r
          (fun h => star (X v ((GlobalTheory.Mem.OneTuple.castG (GlobalTheory.Mem.OneTuple.yc_eq D hj)).symm h)) *
            (e j x).1 (PiTensorProduct.tprod ℂ (d j)) ((GlobalTheory.Mem.OneTuple.castG (GlobalTheory.Mem.OneTuple.yc_eq D hj)).symm h))
          (ipT (R.MY j) (ν j) (𝓕 j) (e j x).1 X * star (ellT (R.MY j) (fun τ => (d j τ : (R.MY j).H τ)) (inclT (R.MY j) v))) :=
    fun j hj => GlobalTheory.Mem.OneTuple.levelRow hP hθ (GlobalTheory.Mem.OneTuple.moves_castG (GlobalTheory.Mem.OneTuple.yc_eq D hj))
      (hsigY j) (R.MY j) _ _ (H1 j hj).1 (e j) (H1 j hj).2.1 (H1 j hj).2.2 (d j) (hd j hj) (hκ j)

  have htop := GlobalTheory.Mem.OneTuple.topRow hP R hM t μ eX J χ hJ hcX H3 dX hdX (hκ D.R.m)
  choose sL rL hsL hrL hsrL rowL hrowL hisoL hpairL using hlow
  have htop' : ∀ j (hj : j = D.R.m), ∃ κT : GA D D.sp.X' ≃* GA D (D.sp.Y j), GlobalTheory.Mem.OneTuple.Moves D.sp.X' (D.sp.Y j) κT ∧
      ∃ s : ℝ, 0 < s ∧ ∃ row : D.what₂.Mult μ j →ₗ[ℂ] CuspS R.θ (D.sp.Y j),
      (∀ x h, (row x).1 h = (s : ℂ) * (eX (famCast (D.what₂.Mult μ) hj x)).1 (PiTensorProduct.tprod ℂ dX) (κT.symm h)) ∧
      (∀ x y, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (κ j) (fun h => star ((row x).1 h) * (row y).1 h) ⟪x, y⟫_ℂ) := by
    intro j hj
    have := htop j hj
    subst hj
    exact this
  choose κT hκT sT hsT rowT hrowT hisoT using htop'
  let row : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] CuspS R.θ (D.sp.Y j) := fun j =>
    if hj : j < D.R.m then rowL j hj else if hj' : j = D.R.m then rowT j hj' else 0
  have row_low : ∀ j (hj : j < D.R.m), row j = rowL j hj := fun j hj => dif_pos hj
  have row_top : ∀ j (hj : j = D.R.m), row j = rowT j hj := fun j hj => by
    simp only [row, dif_neg (show ¬ j < D.R.m by omega), dif_pos hj]

  have hstep : ∀ j, j < D.R.m → ∃ Φ : ThS R.ψ (D.sp.Y (j + 1)) (D.sp.Y j), Φ ≠ 0 ∧
      ∀ y : D.what₂.Mult μ (j + 1), ∃ L : GA D (D.sp.Y j) → ℂ,
        (∀ g, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y (j + 1)) (κ (j + 1))
          (fun h => Wf.ker _ _ (if Even (j + 1) then R.toLevCh.mu t (j + 1) * R.eta⁻¹ else R.toLevCh.mu t (j + 1))
            (if Even j then R.toLevCh.mu t (j + 1) * R.eta⁻¹ else R.toLevCh.mu t (j + 1)) Φ h g * (row (j + 1) y).1 h) (L g)) ∧
        ∀ x : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (κ j) (fun g => star (L g) * (row j x).1 g)
          (inner ℂ (D.what₂.io μ j y) x) := by
    intro j hj
    obtain ⟨hS, hT⟩ := GlobalTheory.Mem.OneTuple.isHC_step R.toLevCh hL t j hj
    rw [row_low j hj]
    by_cases hA : j + 1 < D.R.m
    · rw [row_low (j + 1) hA]
      have hom := hC.ωY t j hA
      rw [GlobalTheory.Mem.OneTuple.chrStep_eq] at hom
      have hne : R.ptY t j (φ j) ≠ 0 := GlobalTheory.Mem.OneTuple.pt_ne_zero (hC.ItY t j hA)
        (by unfold RealDat.ptY; exact map_zero _) (v := PiTensorProduct.tprod ℂ (d (j + 1))) (fun h0 => by
          have := hφ j hA
          rw [h0, map_zero] at this
          exact zero_ne_one this)
      exact GlobalTheory.Mem.OneTuple.step hP hθ Wf (GlobalTheory.Mem.OneTuple.yc_eq D hj)
        (GlobalTheory.Mem.OneTuple.moves_castG (GlobalTheory.Mem.OneTuple.yc_eq D hA)) (hsigY _) (GlobalTheory.Mem.OneTuple.rank_lt D hj) hS hT hom
        (R.MY j) (R.MY (j + 1)) _ _ _ _ (R.CC t (j + 1)) le_rfl
        (GlobalTheory.Mem.Th.haar_chain hM.νY hM.νY' t (j + 1) hA) (H1 j hj).1 (hC.ptY t j hA)
        (hC.ioY t j (by omega)) (φ j) hne (d j) (hd j hj) (d (j + 1)) (hφ j hA)
        (D.what₂.io μ j) (e j) (e (j + 1)) (H1 j hj).2.1 (H4 j hA) (rowL j hj) (rowL (j + 1) hA)
        (hsL j hj) (hrL j hj) (hsL (j + 1) hA) (hκ j) (hκ (j + 1)) (hrowL j hj) (hpairL j hj) (hrowL (j + 1) hA)
    · obtain rfl : j = D.R.m - 1 := by omega
      rw [row_top (D.R.m - 1 + 1) (GlobalTheory.Mem.Th.pred_m_add_one D)]
      have hom := hC.ωX t
      have e1 : Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m = Lift.chrStep (R.toLevCh.mu t) R.eta (D.R.m - 1 + 1) := by
        rw [GlobalTheory.Mem.Th.pred_m_add_one]
      rw [e1, GlobalTheory.Mem.OneTuple.chrStep_eq] at hom
      have hne : R.ptX t φX ≠ 0 := GlobalTheory.Mem.OneTuple.pt_ne_zero (hC.ItX t)
        (by unfold RealDat.ptX; exact map_zero _) (v := PiTensorProduct.tprod ℂ dX) (fun h0 => by
          rw [h0, map_zero] at hφX
          exact zero_ne_one hφX)
      let eW : D.what₂.Mult μ (D.R.m - 1 + 1) →ₗ[ℂ] LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) :=
        eX ∘ₗ (famCast (D.what₂.Mult μ) (GlobalTheory.Mem.Th.pred_m_add_one D)).toLinearEquiv.toLinearMap
      exact GlobalTheory.Mem.OneTuple.step hP hθ Wf (GlobalTheory.Mem.OneTuple.yc_eq D hj)
        (hκT _ (GlobalTheory.Mem.Th.pred_m_add_one D)) (hsigY _) (GlobalTheory.Mem.OneTuple.rank_lt D hj) hS hT hom
        (R.MY (D.R.m - 1)) R.MX _ _ J χ _ hJ ⟨(hM.νX t).1.1, (hM.νX t).2⟩ (H1 _ hj).1 (hC.ptX t)
        (hC.ioX t) φX hne (d (D.R.m - 1)) (hd _ hj) dX hφX
        (D.what₂.io μ (D.R.m - 1)) (e (D.R.m - 1)) eW (H1 _ hj).2.1
        (fun x y => H5 x y _ (GlobalTheory.Mem.OneTuple.famCast_heq _ _ y)) (rowL _ hj) (rowT _ (GlobalTheory.Mem.Th.pred_m_add_one D))
        (hsL _ hj) (hrL _ hj) (hsT _ _) (hκ _) (hκ _) (hrowL _ hj) (hpairL _ hj) (hrowT _ _)
  choose PhiC hPhiC hL2 using hstep
  let Phi : ∀ j, ThS R.ψ (D.sp.Y (j + 1)) (D.sp.Y j) := fun j => if hj : j < D.R.m then PhiC j hj else 0
  refine ⟨row, Phi, fun j hj => ?_, fun j hj x y => ?_, fun j hj y => ?_⟩
  · simp only [Phi, dif_pos hj]
    exact hPhiC j hj
  · rcases hj.lt_or_eq with hj | hj
    · rw [row_low j hj]
      exact hisoL j hj x y
    · rw [row_top j hj]
      exact hisoT j hj x y
  · simp only [Phi, dif_pos hj]
    exact hL2 j hj y
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneTuple_rows_cuspForms_isometric_thetaLifts : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsChain → ∀ (t : T) (μ : D.what₂.Tup), (∃ (e : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] R.CC t j) (eX : D.what₂.Mult μ D.R.m →ₗ[ℂ] LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) (ν : ∀ j, Measure (GA D (Yc D j))) (𝓕 : ∀ j, Set (GA D (Yc D j))) (c : ℕ → ℝ) (cX : ℝ), (∀ j, j < D.R.m → IsQuot (Yc D j) (ν j) (𝓕 j) ∧ 0 < c j ∧ ∀ x y, ⟪x, y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (e j y).1 (e j x).1) ∧ (∃ J χ, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) ≤ MultT R.θ R.MX J χ) ∧ 0 < cX ∧ (∀ x y, ⟪x, y⟫_ℂ = (cX : ℂ) * ipT R.MX (R.νX t) (R.fdX t) (eX y).1 (eX x).1) ∧ (∀ j, j + 1 < D.R.m → ∀ x y, ⟪x, D.what₂.io μ j y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (R.ioY t j (e (j + 1) y)).1 (e j x).1) ∧ ∀ x (y : D.what₂.Mult μ (D.R.m - 1 + 1)) (y' : D.what₂.Mult μ D.R.m), HEq y y' → ⟪x, D.what₂.io μ (D.R.m - 1) y⟫_ℂ = (c (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1)) (ν (D.R.m - 1)) (𝓕 (D.R.m - 1)) (R.ioX t (eX y')).1 (e (D.R.m - 1) x).1) → ∀ (Wf : WeilFun D R.ψ) (κ : ℕ → ℝ), (∀ j, 0 < κ j) → ∃ (row : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] CuspS R.θ (D.sp.Y j)) (Phi : ∀ j, ThS R.ψ (D.sp.Y (j + 1)) (D.sp.Y j)), (∀ j, j < D.R.m → Phi j ≠ 0) ∧ (∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (κ j) (fun h => star ((row j x).1 h) * (row j y).1 h) (inner ℂ x y)) ∧ ∀ j, j < D.R.m → ∀ y : D.what₂.Mult μ (j + 1), ∃ L : GA D (D.sp.Y j) → ℂ, (∀ g, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y (j + 1)) (κ (j + 1)) (fun h => Wf.ker _ _ (if Even (j + 1) then R.toLevCh.mu t (j + 1) * R.eta⁻¹ else R.toLevCh.mu t (j + 1)) (if Even j then R.toLevCh.mu t (j + 1) * R.eta⁻¹ else R.toLevCh.mu t (j + 1)) (Phi j) h g * (row (j + 1) y).1 h) (L g)) ∧ ∀ x : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (κ j) (fun g => star (L g) * (row j x).1 g) (inner ℂ (D.what₂.io μ j y) x) := by
  atlas_forward_decl GlobalTheory.Mem.OneTuple.rows_theta
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.Mem.RowsTies

theorem isQuotInt_zero {D : D7} (V : HSp D) (hV : V.SigOK) (c : ℝ) {φ : GA D V → ℂ} (h : ∀ g, φ g = 0) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V c φ 0 := by
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨μ, hμ, -⟩ := GlobalTheory.Mem.VolMeasure.existsUnique_isVolMeasG D V hV
  obtain ⟨-, 𝓕, h𝓕⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ hμ.1
  have e : φ = fun _ => 0 := funext h
  subst e
  exact ⟨⟨(μ, 𝓕), ⟨hμ, h𝓕⟩⟩, fun m _ => ⟨integrableOn_zero, by simp⟩⟩

theorem rows_of_ties : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsChain → ∀ (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E) (U : Set D.what₂.Tup) (tupT : D.what₂.Tup → T), (∀ μ, ∃ n : ℕ, 0 < n ∧ (xi μ).OrderDvd n) → (∀ μ, (xi μ).TrivOn D.host.F) → (∀ μ ∈ U, R.xiH (tupT μ) = xi μ ∧ (∃ (e : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] R.CC (tupT μ) j) (eX : D.what₂.Mult μ D.R.m →ₗ[ℂ] LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e)) (ν : ∀ j, Measure (GA D (Yc D j))) (𝓕 : ∀ j, Set (GA D (Yc D j))) (c : ℕ → ℝ) (cX : ℝ), (∀ j, j < D.R.m → IsQuot (Yc D j) (ν j) (𝓕 j) ∧ 0 < c j ∧ ∀ x y, ⟪x, y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (e j y).1 (e j x).1) ∧ (∃ J χ, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e) ≤ MultT R.θ R.MX J χ) ∧ 0 < cX ∧ (∀ x y, ⟪x, y⟫_ℂ = (cX : ℂ) * ipT R.MX (R.νX (tupT μ)) (R.fdX (tupT μ)) (eX y).1 (eX x).1) ∧ (∀ j, j + 1 < D.R.m → ∀ x y, ⟪x, D.what₂.io μ j y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (R.ioY (tupT μ) j (e (j + 1) y)).1 (e j x).1) ∧ ∀ x (y : D.what₂.Mult μ (D.R.m - 1 + 1)) (y' : D.what₂.Mult μ D.R.m), HEq y y' → ⟪x, D.what₂.io μ (D.R.m - 1) y⟫_ℂ = (c (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1)) (ν (D.R.m - 1)) (𝓕 (D.R.m - 1)) (R.ioX (tupT μ) (eX y')).1 (e (D.R.m - 1) x).1)) → (∀ μ, μ ∉ U → ∀ j, j < D.R.m → D.what₂.io μ j = 0) → (∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) → ∀ Wf : WeilFun D ψ, ∃ Rc : RecFun D θ ψ, Rc.ChrIs R.C xi ∧ Rc.IoTie Wf ∧ ∀ μ ∈ U, ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (Rc.mY μ j * Rc.petC (D.sp.Y j)) (fun h => star ((Rc.row μ j x).1 h) * (Rc.row μ j y).1 h) (inner ℂ x y)) := by
  intro hD D G _ _ Pl0 T A Ks _ _ _ R hL hM hC xi U tupT hf ht hU hoff θ hθ ψ hψ Wf
  obtain rfl : θ = R.θ := (GlobalTheory.Mem.InfFamUnique.existsUnique_infFam D).unique hθ hM.inf
  obtain rfl : ψ = R.ψ := (GlobalTheory.StdAdelicChar.existsUnique_isStdChar D (-1) (Or.inr rfl)).unique hψ (hC.ωX A.μ0).std
  obtain ⟨Rc, hR⟩ := RecFun.exists_chrIs R.C xi hf ht R.θ R.ψ
  have hu := (GlobalTheory.ChrEqUnique.chrEq_unique D).2.1
  have he : Rc.eta = R.eta := hu _ _ _ hR.eta hL.eta
  have key : ∀ μ, ∃ (row : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] CuspS R.θ (D.sp.Y j)) (Phi : ∀ j, ThS R.ψ (D.sp.Y (j + 1)) (D.sp.Y j)),
      (∀ j, j < D.R.m → Phi j ≠ 0) ∧
      (μ ∈ U → ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j,
        GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (Rc.mY μ j * Rc.petC (D.sp.Y j))
          (fun h => star ((row j x).1 h) * (row j y).1 h) (inner ℂ x y)) ∧
      ∀ j, j < D.R.m → ∀ y : D.what₂.Mult μ (j + 1), ∃ L : GA D (D.sp.Y j) → ℂ,
        (∀ g, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y (j + 1)) (Rc.mY μ (j + 1) * Rc.petC (D.sp.Y (j + 1)))
          (fun h => Wf.ker _ _ (Rc.carY μ (j + 1) (j + 1)) (Rc.carY μ (j + 1) j) (Phi j) h g *
            (row (j + 1) y).1 h) (L g)) ∧
        ∀ x : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (Rc.mY μ j * Rc.petC (D.sp.Y j))
          (fun g => star (L g) * (row j x).1 g) (inner ℂ (D.what₂.io μ j y) x) := fun μ => by
    by_cases hμ : μ ∈ U
    · obtain ⟨hx, hT⟩ := hU μ hμ
      have hc : ∀ j, j < D.R.m → Rc.chr μ (j + 1) = R.toLevCh.mu (tupT μ) (j + 1) := fun j hj =>
        hu _ _ _ (hR.chr μ ⟨j, hj⟩) (hx ▸ GlobalTheory.Mem.TupChar.chrEq_mul (hL.mu0 ⟨j, hj⟩) (hL.xi (tupT μ)))
      obtain ⟨row, Phi, h1, h2, h3⟩ := GlobalTheory.T.oneTuple_rows_cuspForms_isometric_thetaLifts hD D G Pl0 T A Ks R hL hM hC (tupT μ) μ hT Wf
        (fun j => Rc.mY μ j * Rc.petC (D.sp.Y j)) fun j =>
          mul_pos (Rc.mY_pos _ _) (mul_pos (Rc.petF_pos _) (Finset.prod_pos fun _ _ => Rc.meas.petR_pos _ _))
      refine ⟨row, Phi, h1, fun _ => h2, fun j hj y => ?_⟩
      unfold RecFun.carY
      rw [hc j hj, he]
      exact h3 j hj y
    · refine ⟨0, Rc.Phi μ, Rc.Phi_ne hψ μ, fun h => absurd h hμ, fun j hj y => ⟨0, fun g => ?_, fun x => ?_⟩⟩
      · exact isQuotInt_zero _ (D.sp.Y_sig _) _ fun h => by simp
      · rw [hoff μ hμ j hj]
        simpa using isQuotInt_zero _ (D.sp.Y_sig _) _ fun h => by simp
  choose row Phi h1 h2 h3 using key
  exact ⟨{ Rc with row := row, Phi := Phi, Phi_ne := fun _ => h1 }, ⟨hR.chr, hR.eta⟩, h3, h2⟩

end GlobalTheory.Mem.RowsTies
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functionLevelData_of_equal_tuples_zero_intertwiners : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsChain → ∀ (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E) (U : Set D.what₂.Tup) (tupT : D.what₂.Tup → T), (∀ μ, ∃ n : ℕ, 0 < n ∧ (xi μ).OrderDvd n) → (∀ μ, (xi μ).TrivOn D.host.F) → (∀ μ ∈ U, R.xiH (tupT μ) = xi μ ∧ (∃ (e : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] R.CC (tupT μ) j) (eX : D.what₂.Mult μ D.R.m →ₗ[ℂ] LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e)) (ν : ∀ j, Measure (GA D (Yc D j))) (𝓕 : ∀ j, Set (GA D (Yc D j))) (c : ℕ → ℝ) (cX : ℝ), (∀ j, j < D.R.m → IsQuot (Yc D j) (ν j) (𝓕 j) ∧ 0 < c j ∧ ∀ x y, ⟪x, y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (e j y).1 (e j x).1) ∧ (∃ J χ, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e) ≤ MultT R.θ R.MX J χ) ∧ 0 < cX ∧ (∀ x y, ⟪x, y⟫_ℂ = (cX : ℂ) * ipT R.MX (R.νX (tupT μ)) (R.fdX (tupT μ)) (eX y).1 (eX x).1) ∧ (∀ j, j + 1 < D.R.m → ∀ x y, ⟪x, D.what₂.io μ j y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (R.ioY (tupT μ) j (e (j + 1) y)).1 (e j x).1) ∧ ∀ x (y : D.what₂.Mult μ (D.R.m - 1 + 1)) (y' : D.what₂.Mult μ D.R.m), HEq y y' → ⟪x, D.what₂.io μ (D.R.m - 1) y⟫_ℂ = (c (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1)) (ν (D.R.m - 1)) (𝓕 (D.R.m - 1)) (R.ioX (tupT μ) (eX y')).1 (e (D.R.m - 1) x).1)) → (∀ μ, μ ∉ U → ∀ j, j < D.R.m → D.what₂.io μ j = 0) → (∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) → ∀ Wf : WeilFun D ψ, ∃ Rc : RecFun D θ ψ, Rc.ChrIs R.C xi ∧ Rc.IoTie Wf ∧ ∀ μ ∈ U, ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (Rc.mY μ j * Rc.petC (D.sp.Y j)) (fun h => star ((Rc.row μ j x).1 h) * (Rc.row μ j y).1 h) (inner ℂ x y)) := by
  atlas_forward_decl GlobalTheory.Mem.RowsTies.rows_of_ties
end

section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.RecTie
open scoped InnerProductSpace

namespace GlobalTheory.RowTieRead

open GlobalTheory.HilbertLevels

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R)

theorem mem_cc (b : Bool) (μ : D.what₂.Tup) {k : ℕ} (hk : k < D.R.m) (x : SmT (R.MY k) →ₗ[ℂ] GA D (Yc D k) → ℂ) :
    x ∈ (toChainReal R F tupT hm hTop).CC b μ k ↔ x ∈ R.CC (tupT μ) k := by
  show x ∈ MultT R.θ (R.MY k) (if k < D.R.m then _ else Set.univ) (if k < D.R.m then _ else 0) ↔ _
  rw [if_pos hk, if_pos hk]

theorem ioC_coe (b : Bool) (μ : D.what₂.Tup) (k : ℕ) (hk : k + 1 < D.R.m)
    (z : (toChainReal R F tupT hm hTop).CC b μ (k + 1)) :
    (((toChainReal R F tupT hm hTop).ioC b μ k z).1 :
        SmT (R.MY k) →ₗ[ℂ] GA D (Yc D k) → ℂ) =
      (((R.ioY (tupT μ) k ⟨(z.1 : SmT (R.MY (k + 1)) →ₗ[ℂ] GA D (Yc D (k + 1)) → ℂ),
        (mem_cc R F tupT hm hTop b μ hk _).1 z.2⟩).1 : _)) := by
  simp only [toChainReal, dif_pos hk]
  rfl

theorem ioOK (hC : R.IsChain) (b : Bool) (μ : D.what₂.Tup) : (toChainReal R F tupT hm hTop).IoOK b μ := by
  refine ⟨fun k hk => ⟨fun Fz φ v g => ?_, fun Fz φ v g => ?_⟩, fun _ => ⟨fun Fz φ v g => ?_, fun Fz φ v g => ?_⟩⟩
  · exact (hC.ioY (tupT μ) k hk).integ ⟨Fz.1, (mem_cc R F tupT hm hTop b μ (by omega) _).1 Fz.2⟩ φ v g
  · rw [ioC_coe R F tupT hm hTop b μ k (by omega)]
    exact (hC.ioY (tupT μ) k hk).eq ⟨Fz.1, (mem_cc R F tupT hm hTop b μ (by omega) _).1 Fz.2⟩ φ v g
  · exact (hC.ioX (tupT μ)).integ ⟨Fz.1, (hTop (tupT μ)).symm ▸ Fz.2⟩ φ v g
  · exact (hC.ioX (tupT μ)).eq ⟨Fz.1, (hTop (tupT μ)).symm ▸ Fz.2⟩ φ v g

def nuW (t : T) : ∀ j, Measure (GA D (Yc D j))
  | 0 => ENNReal.ofReal (RealDat.nP F true)⁻¹ • R.ν0
  | j + 1 => R.νY t (j + 1)

def fdW (t : T) : ∀ j, Set (GA D (Yc D j))
  | 0 => R.fd0
  | j + 1 => R.fdY t (j + 1)

def cW : ℕ → ℝ
  | 0 => 1
  | _ + 1 => (RealDat.nP F true)⁻¹

def cXW : ℝ := (RealDat.nP F true)⁻¹ * ∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)

variable (I : RowIds (RowSide.sharp D) (toChainReal R F tupT hm hTop) true)

def eW (μ : D.what₂.Tup) (hμ : Used0 D μ) : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] R.CC (tupT μ) j
  | 0 => LinearMap.codRestrict (R.CC (tupT μ) 0)
      (((toChainReal R F tupT hm hTop).EEc true).subtype ∘ₗ I.jE.toLinearMap ∘ₗ
        (D.what₂.multZero μ).toLinearEquiv.toLinearMap)
      (fun x => (mem_cc R F tupT hm hTop true μ hm _).1 (eec_le_cc R F tupT hm hTop true μ (I.jE _).2))
  | j + 1 => if h : j + 1 ≤ D.R.m - 1 then
      LinearMap.codRestrict (R.CC (tupT μ) (j + 1))
        (((toChainReal R F tupT hm hTop).CCP true μ (j + 1)).subtype ∘ₗ
          (I.jM μ hμ (j + 1) (by omega) h).toLinearMap)
        (fun x => (mem_cc R F tupT hm hTop true μ (by omega) _).1
          (ccp_le R F tupT hm hTop true μ (by omega) (I.jM μ hμ (j + 1) (by omega) h x).2))
    else 0

def eXW (μ : D.what₂.Tup) (hμ : Used0 D μ) :
    D.what₂.Mult μ D.R.m →ₗ[ℂ] LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e) :=
  LinearMap.codRestrict (LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e))
    (((toChainReal R F tupT hm hTop).CCXP true μ).subtype ∘ₗ (I.jX μ hμ).toLinearMap)
    (fun x => (hTop (tupT μ)).symm ▸ ccxp_le R F tupT hm hTop true μ (I.jX μ hμ x).2)

theorem eW_pos (μ : D.what₂.Tup) (hμ : Used0 D μ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m - 1) (x : D.what₂.Mult μ j) :
    ((eW R F tupT hm hTop I μ hμ j x).1 : SmT (R.MY j) →ₗ[ℂ] GA D (Yc D j) → ℂ) = (I.jM μ hμ j h1 h2 x).1 := by
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp only [eW, dif_pos h2]
  rfl

theorem nuW_pos (t : T) (j : ℕ) (h1 : 1 ≤ j) : nuW R F t j = R.νY t j := by
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rfl

theorem fdW_pos (t : T) (j : ℕ) (h1 : 1 ≤ j) : fdW R t j = R.fdY t j := by
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rfl

theorem cW_pos (j : ℕ) (h1 : 1 ≤ j) : cW F j = (RealDat.nP F true)⁻¹ := by
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rfl

theorem eW_succ_eq (μ : D.what₂.Tup) (hμ : Used0 D μ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m - 1) (x : D.what₂.Mult μ j) :
    eW R F tupT hm hTop I μ hμ j x = ⟨(I.jM μ hμ j h1 h2 x).1, (mem_cc R F tupT hm hTop true μ (by omega) _).1
      (ccp_le R F tupT hm hTop true μ (by omega) (I.jM μ hμ j h1 h2 x).2)⟩ :=
  Subtype.ext (eW_pos R F tupT hm hTop I μ hμ j h1 h2 x)

theorem inner_io_cast (μ : D.what₂.Tup) {k k' : ℕ} (h : k = k') (x : D.what₂.Mult μ k) (y : D.what₂.Mult μ (k + 1)) :
    ⟪x, D.what₂.io μ k y⟫_ℂ = ⟪cast (congrArg (D.what₂.Mult μ) h) x,
      D.what₂.io μ k' (cast (congrArg (fun i => D.what₂.Mult μ (i + 1)) h) y)⟫_ℂ := by
  subst h; rfl

theorem rhs_cast (μ : D.what₂.Tup) (hμ : Used0 D μ) {k k' : ℕ} (h : k = k')
    (a : SmT (R.MY k) →ₗ[ℂ] GA D (Yc D k) → ℂ) (x : D.what₂.Mult μ k) :
    (cW F k : ℂ) * ipT (R.MY k) (nuW R F (tupT μ) k) (fdW R (tupT μ) k) a (eW R F tupT hm hTop I μ hμ k x).1 =
      (cW F k' : ℂ) * ipT (R.MY k') (nuW R F (tupT μ) k') (fdW R (tupT μ) k')
        (cast (congrArg (fun i => SmT (R.MY i) →ₗ[ℂ] GA D (Yc D i) → ℂ) h) a)
        (eW R F tupT hm hTop I μ hμ k' (cast (congrArg (D.what₂.Mult μ) h) x)).1 := by
  subst h; rfl

variable {n : ℕ} {bs : OrthonormalBasis (Fin n) ℂ D.what₂.EE} {ty : Fin n → D.what₂.FT}

theorem levels (hM : R.IsModels) (hRS : RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (j : ℕ) (hj : j < D.R.m) :
    IsQuot (Yc D j) (nuW R F (tupT μ) j) (fdW R (tupT μ) j) ∧ 0 < cW F j ∧ ∀ x y : D.what₂.Mult μ j,
      ⟪x, y⟫_ℂ = (cW F j : ℂ) * ipT (R.MY j) (nuW R F (tupT μ) j) (fdW R (tupT μ) j)
        (eW R F tupT hm hTop I μ hμ j y).1 (eW R F tupT hm hTop I μ hμ j x).1 := by
  cases j with
  | zero =>
    refine ⟨scaled (inv_pos.2 (nP_pos F true)) hM.ν0.1.1 hM.ν0.2, one_pos, fun x y => ?_⟩
    rw [← LinearIsometryEquiv.inner_map_map (D.what₂.multZero μ)]
    refine (hRS.ee _ _).trans ?_
    show _ = ((1 : ℝ) : ℂ) * _
    rw [Complex.ofReal_one, one_mul]
    rfl
  | succ j =>
    have h2 : j + 1 ≤ D.R.m - 1 := by omega
    refine ⟨measY R hM (tupT μ) h2 hm, inv_pos.2 (nP_pos F true), fun x y => ?_⟩
    refine (hRS.mult μ hμ (j + 1) (by omega) h2 x y).trans ?_
    rw [eW_pos R F tupT hm hTop I μ hμ (j + 1) (by omega) h2 x, eW_pos R F tupT hm hTop I μ hμ (j + 1) (by omega) h2 y]
    rfl

theorem ipT_eq {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (ν : Measure (GA D V)) (𝓕 : Set (GA D V))
    (a b : SmT M →ₗ[ℂ] GA D V → ℂ) : ipT M ν 𝓕 a b = ipMT M ν 𝓕 b a := rfl

theorem eW_zero_coe (μ : D.what₂.Tup) (hμ : Used0 D μ) (x : D.what₂.Mult μ 0) :
    ((eW R F tupT hm hTop I μ hμ 0 x).1 : SmT (R.MY 0) →ₗ[ℂ] GA D (Yc D 0) → ℂ) = (I.jE (D.what₂.multZero μ x)).1 := rfl

theorem ipE_eq (t : T) (a a' : SmT (R.MY 0) →ₗ[ℂ] GA D (Yc D 0) → ℂ) :
    (toChainReal R F tupT hm hTop).ipE true a a' = ipMT (R.MY 0) (nuW R F t 0) (fdW R t 0) a a' := rfl

theorem weightedInner_eq (μ : D.what₂.Tup) (j : ℕ) (a a' : SmT (R.MY j) →ₗ[ℂ] GA D (Yc D j) → ℂ) :
    (toChainReal R F tupT hm hTop).ipP true μ j a a' =
      (((RealDat.nP F true)⁻¹ : ℝ) : ℂ) * ipMT (R.MY j) (R.νY (tupT μ) j) (R.fdY (tupT μ) j) a a' := rfl

theorem ipXP_eq (μ : D.what₂.Tup) (a a' : SmT R.MX →ₗ[ℂ] GA D D.sp.X' → ℂ) :
    (toChainReal R F tupT hm hTop).ipXP true μ a a' =
      (((RealDat.nP F true)⁻¹ : ℝ) : ℂ) * ((((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) / 1 : ℝ) : ℂ) *
        ipMT R.MX (R.νX (tupT μ)) (R.fdX (tupT μ)) a a') := rfl

theorem top_pos : 0 < cXW R F := by
  have hdef : D.sp.X'.IsDefinite := (factXmDef D.R D.host.F D.sp).1
  exact mul_pos (inv_pos.2 (nP_pos F true))
    (Finset.prod_pos fun τ _ => by exact_mod_cast finrank_model_pos D.sp.X'_sig hdef R.MX τ)

theorem top_inner (hRS : RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (x y : D.what₂.Mult μ D.R.m) :
    ⟪x, y⟫_ℂ = (cXW R F : ℂ) * ipT R.MX (R.νX (tupT μ)) (R.fdX (tupT μ))
      (eXW R F tupT hm hTop I μ hμ y).1 (eXW R F tupT hm hTop I μ hμ x).1 := by
  rw [ipT_eq]
  refine (hRS.multX (by omega) μ hμ x y).trans ?_
  have key : ∀ (a b : ℝ) (c : ℂ), (a : ℂ) * (((b / 1 : ℝ)) * c) = ((a * b : ℝ) : ℂ) * c := by
    intro a b c; push_cast; ring
  exact (ipXP_eq R F tupT hm hTop μ _ _).trans ((key _ _ _).trans rfl)

theorem eW_incl (μ : D.what₂.Tup) (hμ : Used0 D μ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m - 1) (y : D.what₂.Mult μ j) :
    eW R F tupT hm hTop I μ hμ j y =
      ⟨((Submodule.inclusion (ccp_le R F tupT hm hTop true μ (by omega)) (I.jM μ hμ j h1 h2 y)).1 :
        SmT (R.MY j) →ₗ[ℂ] GA D (Yc D j) → ℂ), (mem_cc R F tupT hm hTop true μ (by omega) _).1
          (Submodule.inclusion (ccp_le R F tupT hm hTop true μ (by omega)) (I.jM μ hμ j h1 h2 y)).2⟩ := by
  have e1 : (((Submodule.inclusion (ccp_le R F tupT hm hTop true μ (by omega)) (I.jM μ hμ j h1 h2 y) :
      (toChainReal R F tupT hm hTop).CC true μ j)) : (toChainReal R F tupT hm hTop).Amb j) =
      ((I.jM μ hμ j h1 h2 y : (toChainReal R F tupT hm hTop).CCP true μ j) : (toChainReal R F tupT hm hTop).Amb j) :=
    Submodule.coe_inclusion _ _
  exact Subtype.ext ((eW_pos R F tupT hm hTop I μ hμ j h1 h2 y).trans e1.symm)

theorem eXW_val (μ : D.what₂.Tup) (hμ : Used0 D μ) (y : D.what₂.Mult μ D.R.m) :
    ((eXW R F tupT hm hTop I μ hμ y).1 : SmT R.MX →ₗ[ℂ] GA D D.sp.X' → ℂ) = (I.jX μ hμ y).1 := by
  simp only [eXW, LinearMap.codRestrict_apply]
  rfl

theorem eXW_incl (μ : D.what₂.Tup) (hμ : Used0 D μ) (y : D.what₂.Mult μ D.R.m) :
    eXW R F tupT hm hTop I μ hμ y =
      ⟨((Submodule.inclusion (ccxp_le R F tupT hm hTop true μ) (I.jX μ hμ y)).1 : SmT R.MX →ₗ[ℂ] GA D D.sp.X' → ℂ),
        (hTop (tupT μ)).symm ▸ (Submodule.inclusion (ccxp_le R F tupT hm hTop true μ) (I.jX μ hμ y)).2⟩ := by
  have e1 : (((Submodule.inclusion (ccxp_le R F tupT hm hTop true μ) (I.jX μ hμ y) :
      (toChainReal R F tupT hm hTop).CCX true μ)) : (toChainReal R F tupT hm hTop).AmbX) =
      ((I.jX μ hμ y : (toChainReal R F tupT hm hTop).CCXP true μ) : (toChainReal R F tupT hm hTop).AmbX) :=
    Submodule.coe_inclusion _ _
  exact Subtype.ext ((eXW_val R F tupT hm hTop I μ hμ y).trans e1.symm)

theorem ioX_coe (b : Bool) (μ : D.what₂.Tup) (z : (toChainReal R F tupT hm hTop).CCX b μ) :
    (((toChainReal R F tupT hm hTop).ioX b μ z).1 : SmT (R.MY (D.R.m - 1)) →ₗ[ℂ] GA D (Yc D (D.R.m - 1)) → ℂ) =
      ((R.ioX (tupT μ) ⟨(z.1 : SmT R.MX →ₗ[ℂ] GA D D.sp.X' → ℂ), (hTop (tupT μ)).symm ▸ z.2⟩).1 : _) := by
  simp only [toChainReal]
  rfl

theorem L0 (μ : D.what₂.Tup) (hj : 0 + 1 < D.R.m) (a : SmT (R.MY 0) →ₗ[ℂ] GA D (Yc D 0) → ℂ)
    (z : (toChainReal R F tupT hm hTop).CC true μ 1) :
    (toChainReal R F tupT hm hTop).ipE true a ((toChainReal R F tupT hm hTop).ioC true μ 0 z).1 =
      ipMT (R.MY 0) (nuW R F (tupT μ) 0) (fdW R (tupT μ) 0) a
        (R.ioY (tupT μ) 0 ⟨(z.1 : SmT (R.MY 1) →ₗ[ℂ] GA D (Yc D 1) → ℂ), (mem_cc R F tupT hm hTop true μ hj _).1 z.2⟩).1 :=
  (congrArg ((toChainReal R F tupT hm hTop).ipE true a) (ioC_coe R F tupT hm hTop true μ 0 hj z)).trans
    (ipE_eq R F tupT hm hTop (tupT μ) _ _)

theorem inner_io_zero (hC : R.IsChain)
    (hRS : RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (hj : 0 + 1 < D.R.m) (x : D.what₂.Mult μ 0) (y : D.what₂.Mult μ 1) :
    ⟪x, D.what₂.io μ 0 y⟫_ℂ = (cW F 0 : ℂ) * ipT (R.MY 0) (nuW R F (tupT μ) 0) (fdW R (tupT μ) 0)
      (R.ioY (tupT μ) 0 (eW R F tupT hm hTop I μ hμ 1 y)).1 (eW R F tupT hm hTop I μ hμ 0 x).1 := by
  have h1 : ((cW F 0 : ℝ) : ℂ) = 1 := by simp [cW]
  rw [eW_incl R F tupT hm hTop I μ hμ 1 le_rfl (by omega) y, ipT_eq, h1, one_mul,
    ← LinearIsometryEquiv.inner_map_map (D.what₂.multZero μ)]
  exact (hRS.io0 (by omega) μ hμ (ioOK R F tupT hm hTop hC true μ) (D.what₂.multZero μ x) y).trans
    ((L0 R F tupT hm hTop μ hj _ _).trans (congrArg (fun a => ipMT (R.MY 0) (nuW R F (tupT μ) 0) (fdW R (tupT μ) 0) a _)
      (eW_zero_coe R F tupT hm hTop I μ hμ x).symm))

theorem inner_io_succ (hC : R.IsChain)
    (hRS : RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (j : ℕ) (hj : j + 1 + 1 < D.R.m) (x : D.what₂.Mult μ (j + 1))
    (y : D.what₂.Mult μ (j + 1 + 1)) :
    ⟪x, D.what₂.io μ (j + 1) y⟫_ℂ = (cW F (j + 1) : ℂ) * ipT (R.MY (j + 1)) (nuW R F (tupT μ) (j + 1)) (fdW R (tupT μ) (j + 1))
      (R.ioY (tupT μ) (j + 1) (eW R F tupT hm hTop I μ hμ (j + 1 + 1) y)).1 (eW R F tupT hm hTop I μ hμ (j + 1) x).1 := by
  rw [nuW_pos R F (tupT μ) (j + 1) (by omega), fdW_pos R (tupT μ) (j + 1) (by omega), cW_pos F (j + 1) (by omega),
    ipT_eq, eW_incl R F tupT hm hTop I μ hμ (j + 1 + 1) (by omega) (by omega) y,
    eW_succ_eq R F tupT hm hTop I μ hμ (j + 1) (by omega) (by omega) x]
  exact (hRS.io μ hμ (ioOK R F tupT hm hTop hC true μ) (j + 1) (by omega) (by omega) x y).trans
    ((congrArg ((toChainReal R F tupT hm hTop).ipP true μ (j + 1) (I.jM μ hμ (j + 1) (by omega) (by omega) x).1)
      (ioC_coe R F tupT hm hTop true μ (j + 1) hj _)).trans (weightedInner_eq R F tupT hm hTop μ (j + 1) _ _))

theorem io_step (hC : R.IsChain)
    (hRS : RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (j : ℕ) (hj : j + 1 < D.R.m) (x : D.what₂.Mult μ j) (y : D.what₂.Mult μ (j + 1)) :
    ⟪x, D.what₂.io μ j y⟫_ℂ = (cW F j : ℂ) * ipT (R.MY j) (nuW R F (tupT μ) j) (fdW R (tupT μ) j)
      (R.ioY (tupT μ) j (eW R F tupT hm hTop I μ hμ (j + 1) y)).1 (eW R F tupT hm hTop I μ hμ j x).1 := by
  cases j with
  | zero => exact inner_io_zero R F tupT hm hTop I hC hRS μ hμ hj x y
  | succ j => exact inner_io_succ R F tupT hm hTop I hC hRS μ hμ j hj x y

theorem rhs_gen (t : T) (k : ℕ) (hk : 1 ≤ k) (a b : SmT (R.MY k) →ₗ[ℂ] GA D (Yc D k) → ℂ) :
    (cW F k : ℂ) * ipT (R.MY k) (nuW R F t k) (fdW R t k) a b =
      (((RealDat.nP F true)⁻¹ : ℝ) : ℂ) * ipMT (R.MY k) (R.νY t k) (R.fdY t k) b a := by
  obtain ⟨j, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  rfl

theorem rhs_zero (t : T) (a b : SmT (R.MY 0) →ₗ[ℂ] GA D (Yc D 0) → ℂ) :
    (cW F 0 : ℂ) * ipT (R.MY 0) (nuW R F t 0) (fdW R t 0) a b = ipMT (R.MY 0) (nuW R F t 0) (fdW R t 0) b a := by
  have h : ((cW F 0 : ℝ) : ℂ) = 1 := by simp [cW]
  rw [h, one_mul]
  rfl

theorem rowChain_intertwiner_top_second (hC : R.IsChain)
    (hRS : RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (h2 : 1 < D.R.m) (x : D.what₂.Mult μ (D.R.m - 1))
    (y' : D.what₂.Mult μ D.R.m) :
    ⟪x, D.what₂.io μ (D.R.m - 1) (cast (congrArg (D.what₂.Mult μ) (by omega : D.R.m = D.R.m - 1 + 1)) y')⟫_ℂ =
      (cW F (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1))
      (nuW R F (tupT μ) (D.R.m - 1)) (fdW R (tupT μ) (D.R.m - 1))
      (R.ioX (tupT μ) (eXW R F tupT hm hTop I μ hμ y')).1 (eW R F tupT hm hTop I μ hμ (D.R.m - 1) x).1 := by
  have h1m : 1 ≤ D.R.m - 1 := by omega
  refine (hRS.ioTop (by omega) μ hμ (ioOK R F tupT hm hTop hC true μ) x y').trans
    ((congrArg ((toChainReal R F tupT hm hTop).ipP true μ (D.R.m - 1) (I.jM μ hμ (D.R.m - 1) h1m le_rfl x).1)
      (ioX_coe R F tupT hm hTop true μ _)).trans ((weightedInner_eq R F tupT hm hTop μ (D.R.m - 1) _ _).trans
        (Eq.trans ?_ (rhs_gen R F (tupT μ) (D.R.m - 1) h1m _ _).symm)))
  exact congrArg₂ (fun a b => (((RealDat.nP F true)⁻¹ : ℝ) : ℂ) *
      ipMT (R.MY (D.R.m - 1)) (R.νY (tupT μ) (D.R.m - 1)) (R.fdY (tupT μ) (D.R.m - 1)) a b)
    (congrArg Subtype.val (eW_succ_eq R F tupT hm hTop I μ hμ (D.R.m - 1) h1m le_rfl x)).symm
    (congrArg (fun z => (R.ioX (tupT μ) z).1) (eXW_incl R F tupT hm hTop I μ hμ y')).symm

theorem rowChain_intertwiner_top_first (hC : R.IsChain)
    (hRS : RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (h1' : D.R.m = 1) (x : D.what₂.Mult μ (D.R.m - 1))
    (y : D.what₂.Mult μ (D.R.m - 1 + 1)) (y' : D.what₂.Mult μ D.R.m) (hy : HEq y y') :
    ⟪x, D.what₂.io μ (D.R.m - 1) y⟫_ℂ = (cW F (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1))
      (nuW R F (tupT μ) (D.R.m - 1)) (fdW R (tupT μ) (D.R.m - 1))
      (R.ioX (tupT μ) (eXW R F tupT hm hTop I μ hμ y')).1 (eW R F tupT hm hTop I μ hμ (D.R.m - 1) x).1 := by
  have hk : D.R.m - 1 = 0 := by omega
  have hIo := ioOK R F tupT hm hTop hC true μ
  have key : ∀ (a : D.what₂.Mult μ 1) (z : D.what₂.Mult μ D.R.m), HEq a z → ∀ w : D.what₂.Mult μ 0,
      ⟪D.what₂.multZero μ w, D.what₂.multZero μ (D.what₂.io μ 0 a)⟫_ℂ =
        (toChainReal R F tupT hm hTop).ipE true (I.jE (D.what₂.multZero μ w)).1
          (cast (congrArg (toChainReal R F tupT hm hTop).Amb (show D.R.m - 1 = 0 by omega))
            ((toChainReal R F tupT hm hTop).ioX true μ
              (Submodule.inclusion (hRS.lvlX μ hμ) (I.jX μ hμ z))).1) := by
    intro a z haz w
    obtain rfl : z = cast (congrArg ((RowSide.sharp D).Mult μ) h1'.symm) a := (cast_eq_iff_heq.2 haz).symm
    exact hRS.io0X h1' μ hμ hIo _ a
  refine (inner_io_cast μ hk x y).trans ((LinearIsometryEquiv.inner_map_map (D.what₂.multZero μ) _ _).symm.trans
    ((key _ y' ((cast_heq _ _).trans hy) _).trans ((ipE_eq R F tupT hm hTop (tupT μ) _ _).trans
      ((Eq.trans ?_ (rhs_zero R F (tupT μ) _ _).symm).trans (rhs_cast R F tupT hm hTop I μ hμ hk _ x).symm))))
  exact congrArg₂ (ipMT (R.MY 0) (nuW R F (tupT μ) 0) (fdW R (tupT μ) 0))
    (eW_zero_coe R F tupT hm hTop I μ hμ _).symm
    (congrArg (fun w => cast (congrArg (fun i => SmT (R.MY i) →ₗ[ℂ] GA D (Yc D i) → ℂ) hk) w)
      ((ioX_coe R F tupT hm hTop true μ _).trans
        (congrArg (fun z => (R.ioX (tupT μ) z).1) (eXW_incl R F tupT hm hTop I μ hμ y')).symm))

theorem io_top (hC : R.IsChain)
    (hRS : RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (x : D.what₂.Mult μ (D.R.m - 1)) (y : D.what₂.Mult μ (D.R.m - 1 + 1))
    (y' : D.what₂.Mult μ D.R.m) (hy : HEq y y') :
    ⟪x, D.what₂.io μ (D.R.m - 1) y⟫_ℂ = (cW F (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1))
      (nuW R F (tupT μ) (D.R.m - 1)) (fdW R (tupT μ) (D.R.m - 1))
      (R.ioX (tupT μ) (eXW R F tupT hm hTop I μ hμ y')).1 (eW R F tupT hm hTop I μ hμ (D.R.m - 1) x).1 := by
  by_cases h2 : 1 < D.R.m
  · have hyy : cast (congrArg (D.what₂.Mult μ) (by omega : D.R.m = D.R.m - 1 + 1)) y' = y :=
      cast_eq_iff_heq.2 hy.symm
    exact (congrArg (fun z => ⟪x, D.what₂.io μ (D.R.m - 1) z⟫_ℂ) hyy.symm).trans
      (rowChain_intertwiner_top_second R F tupT hm hTop I hC hRS μ hμ h2 x y')
  · exact rowChain_intertwiner_top_first R F tupT hm hTop I hC hRS μ hμ (by omega) x y y' hy

theorem weak_tie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) (I : RowIds (RowSide.sharp D) (toChainReal R F tupT hm hTop) true) (n : ℕ) (bs : OrthonormalBasis (Fin n) ℂ D.what₂.EE) (ty : Fin n → D.what₂.FT), R.IsModels → R.IsChain → RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty → ∀ μ, Used0 D μ → (∃ (e : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] R.CC (tupT μ) j) (eX : D.what₂.Mult μ D.R.m →ₗ[ℂ] LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e)) (ν : ∀ j, Measure (GA D (Yc D j))) (𝓕 : ∀ j, Set (GA D (Yc D j))) (c : ℕ → ℝ) (cX : ℝ), (∀ j, j < D.R.m → IsQuot (Yc D j) (ν j) (𝓕 j) ∧ 0 < c j ∧ ∀ x y, ⟪x, y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (e j y).1 (e j x).1) ∧ (∃ J χ, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e) ≤ MultT R.θ R.MX J χ) ∧ 0 < cX ∧ (∀ x y, ⟪x, y⟫_ℂ = (cX : ℂ) * ipT R.MX (R.νX (tupT μ)) (R.fdX (tupT μ)) (eX y).1 (eX x).1) ∧ (∀ j, j + 1 < D.R.m → ∀ x y, ⟪x, D.what₂.io μ j y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (R.ioY (tupT μ) j (e (j + 1) y)).1 (e j x).1) ∧ ∀ x (y : D.what₂.Mult μ (D.R.m - 1 + 1)) (y' : D.what₂.Mult μ D.R.m), HEq y y' → ⟪x, D.what₂.io μ (D.R.m - 1) y⟫_ℂ = (c (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1)) (ν (D.R.m - 1)) (𝓕 (D.R.m - 1)) (R.ioX (tupT μ) (eX y')).1 (e (D.R.m - 1) x).1) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop I n bs ty hM hC hRS μ hμ
  exact ⟨eW R F tupT hm hTop I μ hμ, eXW R F tupT hm hTop I μ hμ, nuW R F (tupT μ), fdW R (tupT μ), cW F, cXW R F,
    fun j hj => levels R F tupT hm hTop I hM hRS μ hμ j hj, ⟨_, _, (hTop (tupT μ)).le⟩, top_pos R F,
    top_inner R F tupT hm hTop I hRS μ hμ, fun j hj x y => io_step R F tupT hm hTop I hC hRS μ hμ j hj x y,
    fun x y y' hy => io_top R F tupT hm hTop I hC hRS μ hμ x y y' hy⟩

end GlobalTheory.RowTieRead

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.RecTie
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weakCompatibility_of_realRowSide_adelicChain : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) (I : RowIds (RowSide.sharp D) (toChainReal R F tupT hm hTop) true) (n : ℕ) (bs : OrthonormalBasis (Fin n) ℂ D.what₂.EE) (ty : Fin n → D.what₂.FT), R.IsModels → R.IsChain → RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty → ∀ μ, Used0 D μ → (∃ (e : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] R.CC (tupT μ) j) (eX : D.what₂.Mult μ D.R.m →ₗ[ℂ] LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e)) (ν : ∀ j, Measure (GA D (Yc D j))) (𝓕 : ∀ j, Set (GA D (Yc D j))) (c : ℕ → ℝ) (cX : ℝ), (∀ j, j < D.R.m → IsQuot (Yc D j) (ν j) (𝓕 j) ∧ 0 < c j ∧ ∀ x y, ⟪x, y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (e j y).1 (e j x).1) ∧ (∃ J χ, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e) ≤ MultT R.θ R.MX J χ) ∧ 0 < cX ∧ (∀ x y, ⟪x, y⟫_ℂ = (cX : ℂ) * ipT R.MX (R.νX (tupT μ)) (R.fdX (tupT μ)) (eX y).1 (eX x).1) ∧ (∀ j, j + 1 < D.R.m → ∀ x y, ⟪x, D.what₂.io μ j y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (R.ioY (tupT μ) j (e (j + 1) y)).1 (e j x).1) ∧ ∀ x (y : D.what₂.Mult μ (D.R.m - 1 + 1)) (y' : D.what₂.Mult μ D.R.m), HEq y y' → ⟪x, D.what₂.io μ (D.R.m - 1) y⟫_ℂ = (c (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1)) (ν (D.R.m - 1)) (𝓕 (D.R.m - 1)) (R.ioX (tupT μ) (eX y')).1 (e (D.R.m - 1) x).1) := by
  atlas_forward_decl GlobalTheory.RowTieRead.weak_tie
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThetaRecordTrue

theorem recFun_of_rows (hR : GlobalTheory.Published.CuspRapidDecay) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (what₂ : RowsT K w Z Wt p0) {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch)
    (hio : ∀ μ, ¬ Formalism.IndefR.RecTie.Used0 (w.D Z) μ → ∀ j, j < (w.D Z).R.m → (w.D Z).what₂.io μ j = 0) :
    ∀ θ : InfF (w.D Z), IsInfFam θ → ∀ ψ, IsStdChar (w.D Z) ψ (-1) → ∀ Wf : WeilFun (w.D Z) ψ,
      ∃ Rc : RecFun (w.D Z) θ ψ, Rc.ChrIs (TC.cf w.I w.l Z) n.tp.xi ∧ Rc.IoTie Wf ∧ ∀ μ ∈ {μ | Formalism.IndefR.RecTie.Used0 (w.D Z) μ}, ∀ j, j ≤ (w.D Z).R.m → ∀ x y : (w.D Z).what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt ((w.D Z).sp.Y j) (Rc.mY μ j * Rc.petC ((w.D Z).sp.Y j)) (fun h => star ((Rc.row μ j x).1 h) * (Rc.row μ j y).1 h) (inner ℂ x y) := by
  intro θ hθ ψ hψ Wf
  letI : Algebra what₂.r.z.core.Q.c.F (w.D Z).what₂.LL := what₂.r.z.alg
  have h3 := Formalism.IndefR.Links.RealDat3.characterisation_of_weak what₂.r.z.pins.char what₂.exAt
  have hC : what₂.r.z.R.toRealDat.C = TC.cf w.I w.l Z := what₂.r.z.lev.C
  obtain ⟨Rc, h1, h2, h4⟩ := GlobalTheory.T.functionLevelData_of_equal_tuples_zero_intertwiners hR (w.D Z) _ _ _ _ _ what₂.r.z.R.toRealDat h3.lev h3.models h3.chain n.tp.xi
    {μ | Formalism.IndefR.RecTie.Used0 (w.D Z) μ} what₂.r.Y.tupT n.tp.xi_fin n.tp.xi_triv
    (fun μ hμ => ⟨by
        rw [what₂.r.z.lev.xiH, ← what₂.r.tup_ix, what₂.r.Y.tupTie μ hμ, ← n.xi]; rfl,
      GlobalTheory.T.weakCompatibility_of_realRowSide_adelicChain (w.D Z) _ _ _ _ _ what₂.r.z.R.toRealDat what₂.r.z.F.lv2 what₂.r.Y.tupT what₂.r.Y.hm what₂.r.Y.hTop what₂.r.Y.Ish _
        (w.D Z).what₂.onb (w.D Z).what₂.ft h3.models h3.chain what₂.r.Y.tied.sharp μ hμ⟩)
    (fun μ hμ => hio μ hμ) θ hθ ψ hψ Wf
  rw [hC] at h1
  exact ⟨Rc, h1, h2, h4⟩

set_option maxHeartbeats 1000000 in

theorem thEx_main : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ) → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)) → (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam) → ∀ 𝒮 : Slots, (∀ K B f T (w : ColW B f T) (Z : w.Lt) Wt p0 (t : RowsT K w Z Wt p0), 𝒮.Rx K B f T w Z Wt p0 t → ∀ μ, ¬ Formalism.IndefR.RecTie.Used0 (w.D Z) μ → ∀ j, j < (w.D Z).R.m → (w.D Z).what₂.io μ j = 0) → ThEx 𝒮 := by
  intro hW hR _ _ hDS hDSu hDSR 𝒮 hio
  refine StepW.of_all fun K B f T w _ _ _ Z l => ?_
  obtain ⟨X, hio', -, A, a, heq, hchr⟩ := GlobalTheory.Mem.Th.exists_allTied_eqTied_on hW hR hDS hDSu hDSR (w.D Z) (TC.cf w.I w.l Z) l.n.tp.xi
    {μ | Formalism.IndefR.RecTie.Used0 (w.D Z) μ} l.real (recFun_of_rows hR l.what₂ l.n (hio K B f T w Z l.Wt l.p0 l.what₂ l.rx))
  obtain ⟨H, hH⟩ := hchr l.nch l.n.tp rfl
  exact ⟨X, ⟨⟨A, a, GlobalTheory.Mem.Th.weilTiedEq_of_eqTied _ _ _ _ heq, H,
    GlobalTheory.SameChrFin.sameChr_of_chrEq _ _ _ _ _ _ _ hH, a.W.ψ_std, hio'⟩⟩⟩

end GlobalTheory.ThetaRecordTrue

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaData_trueRowsColumns_allCompatible : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ) → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)) → (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam) → ∀ 𝒮 : Slots, (∀ K B f T (w : ColW B f T) (Z : w.Lt) Wt p0 (t : RowsT K w Z Wt p0), 𝒮.Rx K B f T w Z Wt p0 t → ∀ μ, ¬ Formalism.IndefR.RecTie.Used0 (w.D Z) μ → ∀ j, j < (w.D Z).R.m → (w.D Z).what₂.io μ j = 0) → ThEx 𝒮 := by
  atlas_forward_decl GlobalTheory.ThetaRecordTrue.thEx_main
end
