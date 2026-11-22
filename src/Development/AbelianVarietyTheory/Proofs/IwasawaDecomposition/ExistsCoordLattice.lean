module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleOfValued
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorsInvHeckeElementSplitPlace

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix Formalism.L2.Theta
  Formalism.IndefR.Mult
open scoped TensorProduct NumberField.AdeleRing

namespace GlobalTheory.SplitHeckeLabel

section Generic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem evalV_singleV_same (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) : evalV F v (singleV F v y) = y := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y

theorem evalV_singleV_ne (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    evalV F w (singleV F v y) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) y hw

theorem af_ext {a b : 𝔸ᶠ[F]} (h : ∀ w, evalV F w a = evalV F w b) : a = b :=
  RestrictedProduct.ext _ _ h

theorem singleV_mem_intAf (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletionIntegers F) :
    singleV F v (y : Fv F v) ∈ intAf F := fun w => by
  by_cases hw : w = v
  · subst hw; rw [evalV_singleV_same]; exact y.2
  · rw [evalV_singleV_ne v _ hw]; exact zero_mem _

variable (F E) in
def intA : AddSubgroup (𝔸ᶠ[F] ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

theorem mul_mem_intAf {a b : 𝔸ᶠ[F]} (ha : a ∈ intAf F) (hb : b ∈ intAf F) : a * b ∈ intAf F := fun w => by
  rw [map_mul]; exact mul_mem (ha w) (hb w)

theorem one_mem_intAf : (1 : 𝔸ᶠ[F]) ∈ intAf F := fun w => by rw [map_one]; exact one_mem _

theorem tmul_mem_intA {a : 𝔸ᶠ[F]} (ha : a ∈ intAf F) (x : 𝓞 E) : a ⊗ₜ[F] (x : E) ∈ intA F E :=
  AddSubgroup.subset_closure ⟨a, ha, x, rfl⟩

theorem mul_mem_intA {x y : 𝔸ᶠ[F] ⊗[F] E} (hx : x ∈ intA F E) (hy : y ∈ intA F E) : x * y ∈ intA F E := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intA F E) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    exact tmul_mem_intA (mul_mem_intAf ha hb) (u * v)
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem smul_mem_latHat {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) {x : 𝔸ᶠ[F] ⊗[F] E} {y : Fin n → 𝔸ᶠ[F] ⊗[F] E}
    (hx : x ∈ intA F E) (hy : y ∈ latHat F E (L : Set (Fin n → E))) :
    x • y ∈ latHat F E (L : Set (Fin n → E)) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, u, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨b, hb, w, hw, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a * b, mul_mem_intAf ha hb, u • w, L.smul_mem u hw, ?_⟩
      funext i
      rw [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul]
      rfl
    | zero => rw [smul_zero]; exact zero_mem _
    | add y z _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
    | neg y _ h => rw [smul_neg]; exact neg_mem h
  | zero => rw [zero_smul]; exact zero_mem _
  | add y z _ _ h1 h2 => rw [add_smul]; exact add_mem h1 h2
  | neg y _ h => rw [neg_smul]; exact neg_mem h

theorem trace_tmul (R : Type) [CommRing R] [Algebra F R] (a : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
  have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

theorem trace_mem_intAf {z : 𝔸ᶠ[F] ⊗[F] E} (hz : z ∈ intA F E) (v : HeightOneSpectrum (𝓞 F)) :
    evalV F v (Algebra.trace 𝔸ᶠ[F] (𝔸ᶠ[F] ⊗[F] E) z) ∈ v.adicCompletionIntegers F := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, u, rfl⟩ := hx
    rw [trace_tmul, map_mul, AlgHom.commutes]
    refine mul_mem (ha v) ?_
    have hi : IsIntegral ℤ (Algebra.trace F E (u : E)) := Algebra.isIntegral_trace u.isIntegral_coe
    exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v (⟨_, hi⟩ : 𝓞 F)
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add y z _ _ h1 h2 => rw [map_add (f := _), map_add (f := _)]; exact add_mem h1 h2
  | neg y _ h => rw [map_neg, map_neg]; exact neg_mem h

theorem exists_local_lattice {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) (v : HeightOneSpectrum (𝓞 F))
    (φ : 𝔸ᶠ[F] ⊗[F] E →+* Fv F v) (hφa : ∀ a : 𝔸ᶠ[F], φ (algebraMap 𝔸ᶠ[F] _ a) = evalV F v a)
    (hφi : ∀ x ∈ intA F E, φ x ∈ v.adicCompletionIntegers F) :
    ∃ Λ : Submodule (v.adicCompletionIntegers F) (Fin n → Fv F v), Λ.FG ∧
      Submodule.span (Fv F v) (Λ : Set (Fin n → Fv F v)) = ⊤ ∧
      ∀ w, w ∈ Λ ↔ ∃ y ∈ latHat F E (L : Set (Fin n → E)), w = φ ∘ y := by
  classical
  set ψ : E →+* Fv F v := φ.comp (inclR 𝔸ᶠ[F]) with hψ
  have hψi : ∀ x : 𝓞 E, ψ (x : E) ∈ v.adicCompletionIntegers F := fun x => hφi _ (tmul_mem_intA one_mem_intAf x)
  have htm : ∀ (a : 𝔸ᶠ[F]) (x : E), φ (a ⊗ₜ[F] x) = evalV F v a * ψ x := fun a x => by
    rw [← hφa]
    change _ = φ (a ⊗ₜ[F] 1) * φ (1 ⊗ₜ[F] x)
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  obtain ⟨T, hT⟩ := hfg
  set Λ := Submodule.span (v.adicCompletionIntegers F) ((fun x : Fin n → E => ψ ∘ x) '' (T : Set (Fin n → E)))
    with hΛ
  have hL : ∀ x ∈ L, ψ ∘ x ∈ Λ := by
    intro x hx
    rw [← hT] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      have : ψ ∘ (0 : Fin n → E) = 0 := funext fun i => map_zero ψ
      rw [this]; exact zero_mem _
    | add x y _ _ h1 h2 =>
      have : ψ ∘ (x + y) = ψ ∘ x + ψ ∘ y := funext fun i => map_add ψ _ _
      rw [this]; exact add_mem h1 h2
    | smul r x _ h =>
      have : ψ ∘ (r • x) = (⟨ψ r, hψi r⟩ : v.adicCompletionIntegers F) • (ψ ∘ x) := funext fun i => map_mul ψ _ _
      rw [this]; exact Λ.smul_mem _ h
  refine ⟨Λ, Submodule.fg_span (T.finite_toSet.image _), ?_, fun w => ⟨fun hw => ?_, ?_⟩⟩
  · have key : ∀ x : Fin n → E, ψ ∘ x ∈ Submodule.span (Fv F v) (Λ : Set (Fin n → Fv F v)) := by
      intro x
      have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := hsp ▸ Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (hL x hx)
      | zero =>
        have : ψ ∘ (0 : Fin n → E) = 0 := funext fun i => map_zero ψ
        rw [this]; exact zero_mem _
      | add x y _ _ h1 h2 =>
        have : ψ ∘ (x + y) = ψ ∘ x + ψ ∘ y := funext fun i => map_add ψ _ _
        rw [this]; exact add_mem h1 h2
      | smul r x _ h =>
        have : ψ ∘ (r • x) = ψ r • (ψ ∘ x) := funext fun i => map_mul ψ _ _
        rw [this]; exact Submodule.smul_mem _ _ h
    rw [eq_top_iff, ← (Pi.basisFun (Fv F v) (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : Pi.basisFun (Fv F v) (Fin n) i = ψ ∘ (Pi.single i 1 : Fin n → E) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    rw [this]
    exact key _
  · induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx, rfl⟩ := hw
      exact ⟨fun i => (1 : 𝔸ᶠ[F]) ⊗ₜ[F] x i,
        AddSubgroup.subset_closure ⟨1, one_mem_intAf, x, hT ▸ Submodule.subset_span hx, rfl⟩, rfl⟩
    | zero => exact ⟨0, zero_mem _, funext fun i => (map_zero φ).symm⟩
    | add x y _ _ h1 h2 =>
      obtain ⟨x', hx', rfl⟩ := h1
      obtain ⟨y', hy', rfl⟩ := h2
      exact ⟨x' + y', add_mem hx' hy', funext fun i => (map_add φ _ _).symm⟩
    | smul r x _ h =>
      obtain ⟨x', hx', rfl⟩ := h
      refine ⟨(singleV F v (r : Fv F v) ⊗ₜ[F] ((1 : 𝓞 E) : E)) • x',
        smul_mem_latHat L (tmul_mem_intA (singleV_mem_intAf v r) 1) hx', funext fun i => ?_⟩
      change (r : Fv F v) * φ (x' i) = φ ((singleV F v (r : Fv F v) ⊗ₜ[F] (1 : E)) * x' i)
      rw [map_mul, htm, map_one, mul_one, evalV_singleV_same]
  · rintro ⟨y, hy, rfl⟩
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      have : (φ ∘ fun i => a ⊗ₜ[F] x i) = (⟨evalV F v a, ha v⟩ : v.adicCompletionIntegers F) • (ψ ∘ x) :=
        funext fun i => htm a (x i)
      rw [this]; exact Λ.smul_mem _ (hL x hx)
    | zero =>
      have : φ ∘ (0 : Fin n → 𝔸ᶠ[F] ⊗[F] E) = 0 := funext fun i => map_zero φ
      rw [this]; exact zero_mem _
    | add x y _ _ h1 h2 =>
      have : φ ∘ (x + y) = φ ∘ x + φ ∘ y := funext fun i => map_add φ _ _
      rw [this]; exact add_mem h1 h2
    | neg x _ h =>
      have : φ ∘ (-x) = -(φ ∘ x) := funext fun i => map_neg φ _
      rw [this]; exact neg_mem h

end Generic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_coord_lattice {D : D7} (V : HSp D) : ∃ L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E),
    (L : Set (Fin V.rank → D.host.E)) = L0c D V ∧ L.FG ∧
      Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
  let ι := V.frame.equivFun
  refine ⟨V.L0.map (ι.restrictScalars (𝓞 D.host.E)).toLinearMap, ?_, V.standardTuple_isLattice.fg.map _, ?_⟩
  · ext x
    rw [SetLike.mem_coe, Submodule.mem_map_equiv]
    change ι.symm x ∈ V.L0 ↔ ∑ i, x i • V.frame i ∈ V.L0
    rw [Module.Basis.equivFun_symm_apply]
  · have hspan : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra hW
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (ι.trans (starLinearEquiv D.host.E)).trans ι.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt hW
      obtain ⟨x, hx, hx₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e x ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
          Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
        intro y hy
        have hxy : V.hT (e x) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩)
            (LinearMap.mem_ker.mp hx)
        have hyx : V.hT y (e x) = 0 := by
          rw [(V.herm.eq (e x) y).symm, hxy, map_zero]
        simp [hyx]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (R := 𝓞 D.host.E) (S := D.host.E)
          (FaithfulSMul.algebraMap_injective _ _) (Field.toIsField _))
    have : ((V.L0.map (ι.restrictScalars (𝓞 D.host.E)).toLinearMap : Submodule _ _) : Set _) =
        ι.toLinearMap '' (V.L0 : Set V.V) := rfl
    rw [this, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]

theorem divAt_inv {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D) (P : HeightOneSpectrum (𝓞 D.host.E))
    (he : Formalism.L2.NTheta.IsIdemAt e P) (ϖ : 𝓞 D.host.E) (hϖ : ϖ ∈ P.asIdeal) (hϖ2 : ϖ ∉ P.asIdeal ^ 2) (k : ℕ)
    (hk : k ≤ V.rank) (α : GA D V) (hα : Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k α) :
    DivAt V e (ϖ : D.host.E) (splitLab V.rank k) α⁻¹ :=
  GlobalTheory.SplitDivisors.divAt_inv_of_isHeckeElt V P e ϖ k α he hϖ hϖ2 hk hα

end GlobalTheory.SplitHeckeLabel
