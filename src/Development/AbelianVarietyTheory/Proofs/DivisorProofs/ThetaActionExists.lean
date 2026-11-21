import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryCommutingHeisenbergActsFibrewise
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicAddCharNontrivialFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEqStatement
import BuildAid.ForwardExisting

section
section
open Topology Filter

namespace GlobalTheory

theorem span_finiteDimensional_of_bounded_forms {V : Type} [AddCommGroup V] [Module ℂ V]
    (s : Set V) (hs : ∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C) :
    FiniteDimensional ℂ (Submodule.span ℂ s) := by
  classical
  obtain ⟨t, hts, hspan, hli⟩ := exists_linearIndependent ℂ s
  have ht : t.Finite := by
    by_contra hinf
    have hinf' : t.Infinite := hinf
    let e : ℕ ↪ t := hinf'.natEmbedding
    have hli' : LinearIndepOn ℂ id t := hli
    let b := Module.Basis.extend hli'
    let v : (hli'.extend (Set.subset_univ t)) → ℂ := fun i =>
      if h : ∃ k : ℕ, ((e k : t) : V) = (i : V) then (h.choose : ℂ) else 0
    obtain ⟨C, hC⟩ := hs (b.constr ℂ v)
    have key : ∀ k : ℕ, b.constr ℂ v ((e k : t) : V) = (k : ℂ) := by
      intro k
      have hmem : ((e k : t) : V) ∈ hli'.extend (Set.subset_univ t) :=
        hli'.subset_extend _ (e k).2
      have hb : b ⟨_, hmem⟩ = ((e k : t) : V) := by simp [b, Module.Basis.coe_extend]
      rw [← hb, Module.Basis.constr_basis]
      have h : ∃ j : ℕ, ((e j : t) : V) = ((⟨_, hmem⟩ : hli'.extend (Set.subset_univ t)) : V) :=
        ⟨k, rfl⟩
      simp only [v, dif_pos h]
      have hj : h.choose = k := e.injective (Subtype.ext h.choose_spec)
      rw [hj]
    obtain ⟨k, hk⟩ := exists_nat_gt C
    have hle := hC _ (hts (e k).2)
    rw [key, Complex.norm_natCast] at hle
    linarith
  have hfd : FiniteDimensional ℂ (Submodule.span ℂ t) := FiniteDimensional.span_of_finite ℂ ht
  rw [hspan] at hfd
  exact hfd

end GlobalTheory
end

open Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_span_of_forall_linear_bounded : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (s : Set V),
    (∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C) → FiniteDimensional ℂ (Submodule.span ℂ s) := by
  atlas_forward_decl GlobalTheory.span_finiteDimensional_of_bounded_forms
end

section
section
open Topology Filter

namespace GlobalTheory.SmoothFix

theorem eq_one_of_pow_norm_sub_one_le_half {A : Type} [NormedRing A] [NormedAlgebra ℂ A] {x : A}
    (h : ∀ m : ℕ, ‖x ^ m - 1‖ ≤ 1 / 2) : x = 1 := by
  have h1 : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖x - 1‖ ≤ ‖x ^ (2 ^ k) - 1‖ := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨y, hy⟩ : ∃ y, y = x ^ (2 ^ k) - 1 := ⟨_, rfl⟩
      have e : (2 : ℂ) • y = (x ^ (2 ^ (k + 1)) - 1) - y * y := by
        rw [pow_succ 2, pow_mul, hy, two_smul, sq]; noncomm_ring
      have h2 : 2 * ‖y‖ ≤ ‖x ^ (2 ^ (k + 1)) - 1‖ + ‖y‖ * ‖y‖ := by
        have := norm_sub_le (x ^ (2 ^ (k + 1)) - 1) (y * y)
        rw [← e, norm_smul, Complex.norm_ofNat] at this
        linarith [norm_mul_le y y]
      have h3 : ‖y‖ * ‖y‖ ≤ 1 / 2 * ‖y‖ := mul_le_mul_of_nonneg_right (hy ▸ h _) (norm_nonneg y)
      rw [← hy] at ih
      rw [pow_succ]
      linarith
  by_contra hz
  have hp : 0 < ‖x - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖x - 1‖⁻¹) (show (1 : ℝ) < 3 / 2 by norm_num)
  have h4 := (h1 k).trans (h _)
  have h5 := mul_lt_mul_of_pos_right hk hp
  rw [inv_mul_cancel₀ hp.ne'] at h5
  linarith

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exists_nhds_fix : (∀ {V : Type} [AddCommGroup V] [Module ℂ V] (s : Set V),
    (∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C) → FiniteDimensional ℂ (Submodule.span ℂ s)) →
  ∀ {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G) {V : Type} [AddCommGroup V] [Module ℂ V]
    (S : G → Module.End ℂ V), (∀ x ∈ H, ∀ y ∈ H, S (x * y) = S x * S y) → S 1 = 1 →
    (∀ (l : V →ₗ[ℂ] ℂ) (w : V), ContinuousOn (fun x => l (S x w)) (H : Set G)) →
    (∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, K ≤ H ∧ IsCompact (K : Set G) ∧
      (∃ O : Set G, IsOpen O ∧ (1 : G) ∈ O ∧ ∀ x ∈ O, x ∈ H → x ∈ K) ∧ (K : Set G) ⊆ U) →
    ∀ v : V, ∃ U ∈ 𝓝 (1 : G), ∀ x ∈ U, x ∈ H → S x v = v := by
  intro hfd G _ _ H V _ _ S hmul h1 hcont hsmall v
  obtain ⟨K₀, hK₀H, hK₀c, ⟨O₀, hO₀o, hO₀1, hO₀K⟩, -⟩ := hsmall Set.univ univ_mem
  let s : Set V := (fun k => S k v) '' (K₀ : Set G)
  have hb : ∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C := by
    intro l
    obtain ⟨C, hC⟩ := hK₀c.exists_bound_of_continuousOn ((hcont l v).mono hK₀H)
    exact ⟨C, by rintro _ ⟨k, hk, rfl⟩; exact hC k hk⟩
  haveI : FiniteDimensional ℂ (Submodule.span ℂ s) := hfd s hb
  set W := Submodule.span ℂ s with hW
  have hinv : ∀ k ∈ K₀, ∀ w ∈ W, S k w ∈ W := by
    intro k hk w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k', hk', rfl⟩ := hx
      show S k (S k' v) ∈ W
      rw [← Module.End.mul_apply, ← hmul k (hK₀H hk) k' (hK₀H hk')]
      exact Submodule.subset_span ⟨k * k', K₀.mul_mem hk hk', rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact W.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact W.smul_mem c hx
  let R : K₀ → Module.End ℂ W := fun k => (S k).restrict (hinv k.1 k.2)
  have hRv : ∀ (k : K₀) (w : W), (R k w : V) = S k w := fun _ _ => rfl
  have hRpow : ∀ (k : K₀) (m : ℕ), R (k ^ m) = R k ^ m := by
    intro k m
    induction m with
    | zero =>
      ext w
      simp [hRv, h1]
    | succ m ih =>
      ext w
      rw [pow_succ, pow_succ, Module.End.mul_apply, ← ih, hRv, hRv, hRv]
      have hm : ((k ^ m : K₀) : G) ∈ H := hK₀H (k ^ m).2
      simp only [Subgroup.coe_mul]
      rw [hmul _ hm _ (hK₀H k.2), Module.End.mul_apply]
  let b := Module.finBasis ℂ W
  choose c hc using fun i => LinearMap.exists_extend (b.coord i)
  let M : G → Matrix (Fin (Module.finrank ℂ W)) (Fin (Module.finrank ℂ W)) ℂ := fun x i j => c i (S x (b j))
  have hMR : ∀ k : K₀, LinearMap.toMatrixAlgEquiv b (R k) = M k := by
    intro k
    ext i j
    rw [LinearMap.toMatrixAlgEquiv_apply]
    have := LinearMap.congr_fun (hc i) (R k (b j))
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coord_apply] at this
    rw [← this, hRv]
  have hR1 : R 1 = 1 := by
    ext w
    simp [hRv, h1]
  have hM1 : M 1 = 1 := by
    have := hMR 1
    rw [hR1, map_one] at this
    simpa using this.symm
  have hM : ContinuousOn M (H : Set G) :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => hcont (c i) (b j)
  have hN : ContinuousWithinAt (fun x => ‖M x - 1‖) (H : Set G) 1 :=
    ((hM 1 H.one_mem).sub continuousWithinAt_const).norm
  have hev : {x | ‖M x - 1‖ < 1 / 2} ∈ 𝓝[(H : Set G)] 1 :=
    hN (Iio_mem_nhds (by show ‖M 1 - 1‖ < 1 / 2; rw [hM1, sub_self, norm_zero]; norm_num))
  obtain ⟨u, hu, h1u, hsub⟩ := mem_nhdsWithin.1 hev
  obtain ⟨K, hKH, -, ⟨O, hOo, hO1, hOK⟩, hKU⟩ :=
    hsmall (u ∩ O₀) (Filter.inter_mem (hu.mem_nhds h1u) (hO₀o.mem_nhds hO₀1))
  have hvW : v ∈ W := Submodule.subset_span ⟨1, K₀.one_mem, by simp [h1]⟩
  refine ⟨O, hOo.mem_nhds hO1, fun x hxO hxH => ?_⟩
  have hxK : x ∈ K := hOK x hxO hxH
  have hxK₀ : x ∈ K₀ := hO₀K x (hKU hxK).2 (hKH hxK)
  let kk : K₀ := ⟨x, hxK₀⟩
  have hpow : ∀ m : ℕ, ‖(LinearMap.toMatrixAlgEquiv b (R kk)) ^ m - 1‖ ≤ 1 / 2 := by
    intro m
    rw [← map_pow, ← hRpow, hMR]
    have hm : x ^ m ∈ K := K.pow_mem hxK m
    have := hsub ⟨(hKU hm).1, hKH hm⟩
    exact le_of_lt (by simpa using this)
  have hone := eq_one_of_pow_norm_sub_one_le_half hpow
  rw [← map_one (LinearMap.toMatrixAlgEquiv b)] at hone
  have hRk := (LinearMap.toMatrixAlgEquiv b).injective hone
  have := congrArg Subtype.val (LinearMap.congr_fun hRk ⟨v, hvW⟩)
  simpa [hRv] using this

end GlobalTheory.SmoothFix
end

open Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nhds_fix_of_continuous_coefficients : (∀ {V : Type} [AddCommGroup V] [Module ℂ V] (s : Set V),
    (∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C) → FiniteDimensional ℂ (Submodule.span ℂ s)) →
  ∀ {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G) {V : Type} [AddCommGroup V] [Module ℂ V]
    (S : G → Module.End ℂ V), (∀ x ∈ H, ∀ y ∈ H, S (x * y) = S x * S y) → S 1 = 1 →
    (∀ (l : V →ₗ[ℂ] ℂ) (w : V), ContinuousOn (fun x => l (S x w)) (H : Set G)) →
    (∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, K ≤ H ∧ IsCompact (K : Set G) ∧
      (∃ O : Set G, IsOpen O ∧ (1 : G) ∈ O ∧ ∀ x ∈ O, x ∈ H → x ∈ K) ∧ (K : Set G) ⊆ U) →
    ∀ v : V, ∃ U ∈ 𝓝 (1 : G), ∀ x ∈ U, x ∈ H → S x v = v := by
  atlas_forward_decl GlobalTheory.SmoothFix.exists_nhds_fix
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix Filter Topology
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SmallAtPlace

open IsDedekindDomain NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in

theorem smul_tens_single (v : HeightOneSpectrum (𝓞 F)) {u : AF F} (hu : evFin F v u = 0)
    (h1 : ∀ a b : Af F, (LinearMap.inr F (Ainf F) (Af F) (a * b) : AF F) =
      LinearMap.inr F (Ainf F) (Af F) a * LinearMap.inr F (Ainf F) (Af F) b)
    (z : Fv F v ⊗[F] E) :
    u • GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (E := E) (R' := AF F) (LinearMap.inr F (Ainf F) (Af F)) h1
      (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (singleFin v) (singleFin_mul v) z) = 0 := by
  have key : ∀ b : AF F, u * b = 0 → ∀ e : E, u • (b ⊗ₜ[F] e : AF F ⊗[F] E) = 0 := fun b hb e => by
    rw [TensorProduct.smul_tmul', smul_eq_mul, hb, TensorProduct.zero_tmul]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, smul_add, hx, hy, add_zero]
  | tmul a e =>
    let b : AF F := LinearMap.inr F (Ainf F) (Af F) (singleFin v a)
    have hb : u * b = 0 := by
      refine Prod.ext (mul_zero _) ?_
      show u.2 * singleFin v a = 0
      refine af_ext fun t => ?_
      rw [map_mul, map_zero]
      by_cases ht : t = v
      · subst ht
        have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F t u.2 = 0 := hu
        rw [this, zero_mul]
      · rw [evalV_singleFin_ne ht, mul_zero]
    exact key b hb e

omit [NumberField E] in

theorem smul_mat_emb_sub_one (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (x : GLoc σ J v) {u : AF F} (hu : evFin F v u = 0) :
    u • ((HA.mat (AF F) σ J (emb σ J v x)).1 - 1) = 0 := by
  ext r s
  rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply]
  have h1 : ∀ a b : Af F, (LinearMap.inr F (Ainf F) (Af F) (a * b) : AF F) =
      LinearMap.inr F (Ainf F) (Af F) a * LinearMap.inr F (Ainf F) (Af F) b :=
    fun _ _ => Prod.ext (mul_zero _).symm rfl
  have hm := GlobalTheory.AutFunCompare.mat_extH σ J (R' := AF F) (LinearMap.inr F (Ainf F) (Af F)) h1
    (embLocFin σ J v x) r s
  have hm2 := GlobalTheory.AutFunCompare.mat_extH σ J (singleFin v) (singleFin_mul v) x r s
  have e1 : (HA.mat (AF F) σ J (emb σ J v x)).1 r s = _ := hm
  have e2 : (HA.mat (Af F) σ J (embLocFin σ J v x)).1 r s = _ := hm2
  rw [e1, e2]
  set T1 := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (E := E) (R' := AF F) (LinearMap.inr F (Ainf F) (Af F)) h1
  set T2 := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (E := E) (singleFin v) (singleFin_mul v)
  have key : ∀ z, u • T1 (T2 z) = 0 := smul_tens_single v hu h1
  have : (1 - T1 1) * (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) r s +
      T1 ((1 - T2 1) * (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) r s + T2 ((HA.mat _ σ J x).1 r s)) -
      (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) r s =
      T1 (T2 ((HA.mat _ σ J x).1 r s - (1 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) r s)) := by
    by_cases h : r = s
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, Matrix.one_apply_eq, mul_one, mul_one, map_add, map_sub, map_sub, map_sub]
      abel
    · simp only [Matrix.one_apply_ne h, mul_zero, zero_add, sub_zero, map_zero]
  rw [this]
  exact key _

omit [NumberField E] in
theorem map_smul_of_eq_one {R : Type} [CommRing R] [Algebra F R] (ψ : AF F →ₐ[F] R) {a : AF F} (ha : ψ a = 1)
    (y : AF F ⊗[F] E) :
    Algebra.TensorProduct.map ψ (AlgHom.id F E) (a • y) = Algebra.TensorProduct.map ψ (AlgHom.id F E) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy]
  | tmul b e =>
    rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, smul_eq_mul,
      map_mul, ha, one_mul]

omit [NumberField E] in
theorem mapH_eq_one_of_smul (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {R : Type} [CommRing R]
    [Algebra F R] (ψ : AF F →ₐ[F] R) {a : AF F} (ha : ψ a = 1) {g : GAd σ J}
    (hg : a • ((HA.mat (AF F) σ J g).1 - 1) = 0) : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapH σ J ψ g = 1 := by
  refine GlobalTheory.AutFunCompare.HA_ext σ J fun r s => ?_
  rw [GlobalTheory.AutFunCompare.mat_mapH]
  have h := congrArg (Algebra.TensorProduct.map ψ (AlgHom.id F E)) (congrFun (congrFun hg r) s)
  rw [Matrix.smul_apply, Matrix.sub_apply, map_smul_of_eq_one ψ ha, map_sub, Matrix.zero_apply, map_zero, sub_eq_zero] at h
  rw [h]
  show _ = (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) r s
  by_cases e : r = s
  · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, map_zero]

omit [NumberField E] in

theorem eq_emb_proj_of_smul (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    {g : GAd σ J} (hg : ∀ u : AF F, evFin F v u = 0 → u • ((HA.mat (AF F) σ J g).1 - 1) = 0) :
    g = emb σ J v (proj σ J v g) := by
  refine GAd_ext σ J (fun w => ?_) (fun u => ?_)
  · rw [projArch_emb]
    let a : AF F := ((1 : Ainf F), (0 : Af F))
    have h1 : evInf F w a = 1 := by
      show (GlobalTheory.AutFunCompare.evW w) (1 : Ainf F) = 1
      exact map_one _
    have h0 : evFin F v a = 0 := by
      show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (0 : Af F) = 0
      exact map_zero _
    exact mapH_eq_one_of_smul σ J (evInf F w) h1 (hg a h0)
  · by_cases h : u = v
    · subst h; rw [proj_emb_self]
    · rw [proj_emb_ne σ J h]
      let a : AF F := ((0 : Ainf F), singleFin u 1)
      have h1 : evFin F u a = 1 := evalV_singleFin_self u 1
      have h0 : evFin F v a = 0 := evalV_singleFin_ne (Ne.symm h) 1
      exact mapH_eq_one_of_smul σ J (evFin F u) h1 (hg a h0)

theorem exists_compact_subgroup_at_place : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E},
    (∀ x, σ (σ x) = x) → ∀ {n : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (U : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)), U ∈ 𝓝 (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J) →
    ∃ K : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J), (∀ g ∈ K, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (GlobalTheory.AdelicU.evFin F v)) ∧
      IsCompact (K : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)) ∧
      (∃ O : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J), IsOpen O ∧ (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J) ∈ O ∧
        ∀ g ∈ O, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (GlobalTheory.AdelicU.evFin F v) → g ∈ K) ∧ (K : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)) ⊆ U := by
  intro F E _ _ _ _ _ σ hσ n X v U hU
  have heq : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) = HR (AF F) σ (X.J.map σ) := by
    have h := GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := X.J) hσ one_ne_zero
    rw [one_smul] at h
    exact h
  let e : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J ≃* GAd σ (X.J.map σ) := MulEquiv.subgroupCongr heq
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _
  let f : GLoc σ (X.J.map σ) v →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J := e.symm.toMonoidHom.comp (emb σ (X.J.map σ) v)
  have hf : Continuous f := he'.comp (continuous_emb σ (X.J.map σ) v)
  have hW : f ⁻¹' U ∈ 𝓝 (1 : GLoc σ (X.J.map σ) v) :=
    hf.continuousAt.preimage_mem_nhds (by rw [map_one]; exact hU)
  haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GLoc σ (X.J.map σ) v
  obtain ⟨V₀, hV₀⟩ := NonarchimedeanGroup.is_nonarchimedean _ hW
  haveI := isLattice_stdLattice (E := E) (n := n)
  let V₁ : Subgroup (GLoc σ (X.J.map σ) v) := (V₀ : Subgroup _) ⊓ stabLoc σ (X.J.map σ) (stdLattice E n) v
  have hV₁o : IsOpen (V₁ : Set (GLoc σ (X.J.map σ) v)) :=
    V₀.isOpen.inter (isOpen_stabLoc σ (X.J.map σ) (stdLattice E n) v)
  have hV₁c : IsCompact (V₁ : Set (GLoc σ (X.J.map σ) v)) :=
    (isCompact_stabLoc σ (X.J.map σ) (stdLattice E n) v).inter_left V₀.isClosed
  have hmat : ∀ g, (HA.mat (AF F) σ (X.J.map σ) (e g)).1 = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g := fun g => rfl
  refine ⟨V₁.map f, ?_, ?_, ⟨(proj σ (X.J.map σ) v ∘ e) ⁻¹' (V₁ : Set _),
    hV₁o.preimage ((continuous_proj σ (X.J.map σ) v).comp he), ?_, ?_⟩, ?_⟩
  · rintro _ ⟨x, -, rfl⟩ u hu
    have h := smul_mat_emb_sub_one σ (X.J.map σ) v x hu
    have h2 : (HA.mat (AF F) σ (X.J.map σ) (e (f x))).1 = (HA.mat (AF F) σ (X.J.map σ) (emb σ (X.J.map σ) v x)).1 := by
      simp [f]
    rw [← hmat, h2]
    exact h
  · rw [Subgroup.coe_map]
    exact hV₁c.image hf
  · show proj σ (X.J.map σ) v (e 1) ∈ V₁
    rw [map_one, map_one]
    exact one_mem _
  · intro g hg hgv
    refine ⟨proj σ (X.J.map σ) v (e g), hg, ?_⟩
    have h : e g = emb σ (X.J.map σ) v (proj σ (X.J.map σ) v (e g)) :=
      eq_emb_proj_of_smul σ (X.J.map σ) v fun u hu => by rw [hmat]; exact hgv u hu
    show e.symm (emb σ (X.J.map σ) v (proj σ (X.J.map σ) v (e g))) = g
    rw [← h, MulEquiv.symm_apply_apply]
  · rintro _ ⟨x, hx, rfl⟩
    exact hV₀ hx.1

end GlobalTheory.SmallAtPlace
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix Filter Topology
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compactSubgroup_unitaryPoints_supportedAtPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E},
    (∀ x, σ (σ x) = x) → ∀ {n : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (U : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)), U ∈ 𝓝 (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J) →
    ∃ K : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J), (∀ g ∈ K, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (GlobalTheory.AdelicU.evFin F v)) ∧
      IsCompact (K : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)) ∧
      (∃ O : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J), IsOpen O ∧ (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J) ∈ O ∧
        ∀ g ∈ O, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (GlobalTheory.AdelicU.evFin F v) → g ∈ K) ∧ (K : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)) ⊆ U := by
  first | exact @GlobalTheory.SmallAtPlace.exists_compact_subgroup_at_place | exact GlobalTheory.SmallAtPlace.exists_compact_subgroup_at_place | (intros; apply GlobalTheory.SmallAtPlace.exists_compact_subgroup_at_place <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix Filter Topology
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SmoothAtPlace

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem one_mem_uAt {σ : E →ₐ[F] E} {n : ℕ} (X : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) :
    (1 : UA σ X.J) ∈ UAt σ X ev := by
  intro u _
  show u • ((1 : Matrix (Fin n) (Fin n) (AE F E)) - 1) = 0
  simp

theorem mul_mem_uAt {σ : E →ₐ[F] E} {n : ℕ} (X : Spc F E n) {R : Type} [Zero R] (ev : AF F → R)
    {g h : UA σ X.J} (hg : g ∈ UAt σ X ev) (hh : h ∈ UAt σ X ev) : g * h ∈ UAt σ X ev := by
  intro u hu
  have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
    show mat g * mat h - 1 = _
    noncomm_ring
  rw [e, smul_add, ← Matrix.smul_mul, hg u hu, hh u hu, Matrix.zero_mul, add_zero]

theorem inv_mem_uAt {σ : E →ₐ[F] E} {n : ℕ} (X : Spc F E n) {R : Type} [Zero R] (ev : AF F → R)
    {g : UA σ X.J} (hg : g ∈ UAt σ X ev) : g⁻¹ ∈ UAt σ X ev := by
  intro u hu
  have h1 : mat g⁻¹ * mat g = 1 := by
    show ((g⁻¹ * g : UA σ X.J) : GL (Fin n) (AE F E)).1 = 1
    rw [inv_mul_cancel]; rfl
  have e : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by
    rw [Matrix.mul_sub, h1, Matrix.mul_one]; abel
  rw [e, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]

end GlobalTheory.SmoothAtPlace

namespace GlobalTheory.SmoothAtPlace

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def locGrp {σ : E →ₐ[F] E} {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) :
    Subgroup (UA σ X.J × UA σ W.J) where
  carrier := {x | x.1 ∈ UAt σ X (evFin F v) ∧ x.2 ∈ UAt σ W (evFin F v)}
  one_mem' := ⟨one_mem_uAt X _, one_mem_uAt W _⟩
  mul_mem' ha hb := ⟨mul_mem_uAt X _ ha.1 hb.1, mul_mem_uAt W _ ha.2 hb.2⟩
  inv_mem' ha := ⟨inv_mem_uAt X _ ha.1, inv_mem_uAt W _ ha.2⟩

def tensL {κ : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (R : (κ → AF F) → ℂ) : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun φ := tens (evFin F v) φ R
  map_add' φ ψ := funext fun x => by simp [tens, add_mul]
  map_smul' c φ := funext fun x => by simp [tens, mul_assoc]

def locOp {κ : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (R : (κ → AF F) → ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)) :
    Module.End ℂ ((κ → Fv F v) → ℂ) :=
  (R 0)⁻¹ • (LinearMap.funLeft ℂ ℂ (fun (t : κ → Fv F v) i => GlobalTheory.LatVac.liftV v (t i)) ∘ₗ T ∘ₗ tensL v R)

theorem tens_liftV {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {R : (κ → AF F) → ℂ} (φ : (κ → Fv F v) → ℂ)
    (hR : Rest (evFin F v) φ R) (t : κ → Fv F v) :
    tens (evFin F v) φ R (fun i => GlobalTheory.LatVac.liftV v (t i)) = φ t * R 0 := by
  have h1 := hR.1 0 (fun i => GlobalTheory.LatVac.liftV v (t i)) fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v (t i) u hu
  rw [zero_add] at h1
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, h1]

theorem locOp_eq {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {R : (κ → AF F) → ℂ} (hR0 : R 0 ≠ 0) {φ φ₁ : (κ → Fv F v) → ℂ}
    (hR : Rest (evFin F v) φ R) (hR₁ : Rest (evFin F v) φ₁ R) {T : Module.End ℂ ((κ → AF F) → ℂ)}
    (h : Acts (evFin F v) T φ φ₁) : locOp v R T φ = φ₁ := by
  funext t
  have := h R hR
  simp only [locOp, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply]
  change (R 0)⁻¹ • T (tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)) = φ₁ t
  rw [this, tens_liftV v φ₁ hR₁ t, smul_eq_mul]
  field_simp

end GlobalTheory.SmoothAtPlace

namespace GlobalTheory.SmoothAtPlace

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem liftV_fst (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (a : Fv F v) : (GlobalTheory.LatVac.liftV v a).1 = 0 := rfl

open scoped Classical in

theorem continuous_locOp {σ : E →ₐ[F] E} {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    {χX χW : Chr F E} {om : Rep σ X W} (hW : M.IsWeil B.ψ χX χW om) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (R : (Fin n × Fin d → AF F) → ℂ) (φ : (Fin n × Fin d → Fv F v) → ℂ)
    (hΦ : tens (evFin F v) φ R ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d))
    (lam : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ) :
    Continuous fun x : UA σ X.J × UA σ W.J => lam (locOp v R (om x) φ) := by
  let L : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin d → Fv F v) → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun (t : Fin n × Fin d → Fv F v) i => GlobalTheory.LatVac.liftV v (t i))
  have hl : lam ∘ₗ L ∈ (GlobalTheory.WeilM.adeleClass F).adm (Fin n × Fin d) := by
    intro g _
    refine ⟨lam (fun t => g (fun i => (GlobalTheory.LatVac.liftV v (t i)).2)) •
      ((BoundedContinuousFunction.evalCLM ℂ 0).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
    have e : L (GlobalTheory.WeilM.pureA F f g) = f 0 • (fun t => g (fun i => (GlobalTheory.LatVac.liftV v (t i)).2)) := by
      funext t
      simp only [L, LinearMap.funLeft_apply, GlobalTheory.WeilM.pureA, liftV_fst, map_zero, Pi.smul_apply, smul_eq_mul]
      rfl
    rw [LinearMap.comp_apply, e, map_smul, smul_eq_mul, _root_.smul_apply, smul_eq_mul, mul_comm]
    rfl
  have hc := hW.2.2 (lam ∘ₗ L) hl _ hΦ
  have h2 : Continuous fun x : UA σ X.J × UA σ W.J => (R 0)⁻¹ * (lam ∘ₗ L) (om x (tens (evFin F v) φ R)) :=
    continuous_const.mul hc
  refine h2.congr fun x => ?_
  simp only [locOp, LinearMap.smul_apply, LinearMap.comp_apply, map_smul, smul_eq_mul]
  rfl

end GlobalTheory.SmoothAtPlace

namespace GlobalTheory.SmoothAtPlace

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem weil_smooth_at : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F,
    (∀ x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J, x.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v) →
      x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (evFin F v) → ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v),
        ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om x) φ φ₁) →
    ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), ∃ U ∈ 𝓝 (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J),
      ∀ x ∈ U, x.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v) → x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (evFin F v) →
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om x) φ φ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v hActs φ hφ
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hP.base.cm
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin n × Fin d) v
  let H := locGrp (σ := σ) X W v
  let V := GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)
  have key : ∀ x ∈ H, ∀ ψ ∈ V, locOp v R (om x) ψ ∈ V ∧ Acts (evFin F v) (om x) ψ (locOp v R (om x) ψ) := by
    intro x hx ψ hψ
    obtain ⟨ψ₁, hψ₁, hA⟩ := hActs x hx.1 hx.2 ψ hψ
    rw [locOp_eq v hR0 (hR ψ hψ) (hR ψ₁ hψ₁) hA]
    exact ⟨hψ₁, hA⟩
  classical
  let S : UA σ X.J × UA σ W.J → Module.End ℂ V := fun x =>
    if hx : x ∈ H then (locOp v R (om x)).restrict (fun ψ hψ => (key x hx ψ hψ).1) else LinearMap.id
  have hS : ∀ x (hx : x ∈ H) (ψ : V), ((S x ψ : V) : (Fin n × Fin d → Fv F v) → ℂ) = locOp v R (om x) ψ := by
    intro x hx ψ
    simp only [S, dif_pos hx]
    rfl
  have hmul : ∀ x ∈ H, ∀ y ∈ H, S (x * y) = S x * S y := by
    intro x hx y hy
    ext ψ : 1
    apply Subtype.ext
    rw [hS _ (H.mul_mem hx hy), Module.End.mul_apply, hS _ hx, hS _ hy]
    have h1 := key y hy ψ ψ.2
    have h2 := key x hx _ h1.1
    refine locOp_eq v hR0 (hR ψ ψ.2) (hR _ h2.1) fun r hr => ?_
    have hr' : Rest (evFin F v) (locOp v R (om y) ψ) r := ⟨hr.1, by
      rw [← h1.2 r hr]
      exact (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hP.weil).pres y _ hr.2⟩
    rw [map_mul, Module.End.mul_apply, h1.2 r hr, h2.2 r hr']
  have hone : S 1 = 1 := by
    ext ψ : 1
    apply Subtype.ext
    rw [hS 1 H.one_mem]
    exact locOp_eq v hR0 (hR ψ ψ.2) (hR ψ ψ.2) fun r _ => by rw [map_one]; rfl
  have hcont : ∀ (l : V →ₗ[ℂ] ℂ) (w : V), ContinuousOn (fun x => l (S x w)) (H : Set (UA σ X.J × UA σ W.J)) := by
    intro l w
    obtain ⟨lam, hlam⟩ := LinearMap.exists_extend l
    refine (continuous_locOp hP.weil v R w.1 (hR w.1 w.2).2 lam).continuousOn.congr fun x hx => ?_
    have : S x w = ⟨locOp v R (om x) w, (key x hx w w.2).1⟩ := Subtype.ext (hS x hx w)
    rw [this, ← hlam]
    rfl
  have hbasis : ∀ U ∈ 𝓝 (1 : UA σ X.J × UA σ W.J), ∃ K : Subgroup (UA σ X.J × UA σ W.J), K ≤ H ∧
      IsCompact (K : Set (UA σ X.J × UA σ W.J)) ∧
      (∃ O : Set (UA σ X.J × UA σ W.J), IsOpen O ∧ (1 : UA σ X.J × UA σ W.J) ∈ O ∧ ∀ x ∈ O, x ∈ H → x ∈ K) ∧
      (K : Set (UA σ X.J × UA σ W.J)) ⊆ U := by
    intro U hU
    rw [show (1 : UA σ X.J × UA σ W.J) = (1, 1) from rfl, nhds_prod_eq] at hU
    obtain ⟨U1, hU1, U2, hU2, hsub⟩ := Filter.mem_prod_iff.1 hU
    obtain ⟨K1, hK1H, hK1c, ⟨O1, hO1, h1O1, hO1K⟩, hK1U⟩ := GlobalTheory.T.exists_compactSubgroup_unitaryPoints_supportedAtPlace hσ X v U1 hU1
    obtain ⟨K2, hK2H, hK2c, ⟨O2, hO2, h1O2, hO2K⟩, hK2U⟩ := GlobalTheory.T.exists_compactSubgroup_unitaryPoints_supportedAtPlace hσ W v U2 hU2
    refine ⟨K1.prod K2, fun x hx => ⟨hK1H _ hx.1, hK2H _ hx.2⟩, ?_,
      ⟨O1 ×ˢ O2, hO1.prod hO2, ⟨h1O1, h1O2⟩, fun x hx hxH => ⟨hO1K _ hx.1 hxH.1, hO2K _ hx.2 hxH.2⟩⟩,
      fun x hx => hsub ⟨hK1U hx.1, hK2U hx.2⟩⟩
    rw [Subgroup.coe_prod]
    exact hK1c.prod hK2c
  obtain ⟨U, hU, hfix⟩ := GlobalTheory.T.exists_nhds_fix_of_continuous_coefficients GlobalTheory.T.finiteDimensional_span_of_forall_linear_bounded H S hmul hone hcont hbasis ⟨φ, hφ⟩
  refine ⟨U, hU, fun x hxU hx1 hx2 => ?_⟩
  have hx : x ∈ H := ⟨hx1, hx2⟩
  have e := congrArg Subtype.val (hfix x hxU hx)
  rw [hS x hx] at e
  have := (key x hx φ hφ).2
  rwa [e] at this

end GlobalTheory.SmoothAtPlace
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix Filter Topology
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_smooth_at_finitePlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F,
    (∀ x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J, x.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v) →
      x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (evFin F v) → ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v),
        ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om x) φ φ₁) →
    ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), ∃ U ∈ 𝓝 (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J),
      ∀ x ∈ U, x.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v) → x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (evFin F v) →
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om x) φ φ := by
  atlas_forward_decl GlobalTheory.SmoothAtPlace.weil_smooth_at
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix Filter Topology
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ThK.LocalOps

theorem comm_off {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E} {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    {M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W} {χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W}
    {r s r' s' : ℕ} (hP : GlobalTheory.ThK.IsPair B M χX χW om r s r' s') (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)
    (hx1 : x.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v)) (hx2 : x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (evFin F v))
    (u : AF F) (hu : evFin F v u = 0) (p q : Fin n × Fin d → AF F) (Φ : (Fin n × Fin d → AF F) → ℂ)
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d)) :
    om x (GlobalTheory.WeilM.schr B.ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr B.ψ (u • p, u • q) (om x Φ) := by
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hP.weil
  set w := M.co.e.symm (p, q) with hw
  have he : M.co.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have h1 : u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.1 - 1) = 0 := hx1 u hu
  have h2 : u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.2 - 1) = 0 := hx2 u hu
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.1 * (u • w) = u • w := by
    have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.1 * (u • w) - u • w = (u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.1 - 1)) * w := by
      rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_smul, smul_sub]
    rw [h1, Matrix.zero_mul, sub_eq_zero] at this
    exact this
  have e2 : (u • w) * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.2)ᵀ = u • w := by
    have : (u • w) * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.2)ᵀ - u • w = w * (u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.2 - 1))ᵀ := by
      rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.mul_sub, Matrix.mul_one, smul_sub]
    rw [h2, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this
    exact this
  have hact : GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) x (u • w) = u • w := by
    simp only [GlobalTheory.WeilM.actAB]
    have := e1
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat] at this e2
    rw [this, e2]
  have h3 := hW.impl x (u • w) Φ hΦ
  simp only [GlobalTheory.WeilM.Darboux.rho, he, hact] at h3
  exact h3

theorem liftV_one_mul {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (b : AF F) :
    GlobalTheory.LatVac.liftV v 1 * b = GlobalTheory.LatVac.liftV v (evFin F v b) := by
  refine Prod.ext ?_ ?_
  · exact zero_mul _
  · change GlobalTheory.AdelicU.singleFin v 1 * b.2 = GlobalTheory.AdelicU.singleFin v (evFin F v b)
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul]
      rfl
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw, GlobalTheory.AdelicU.evalV_singleFin_ne hw, zero_mul]

theorem schr_trans {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ]
    (w : κ → AF F) (Φ : (κ → AF F) → ℂ) : GlobalTheory.WeilM.schr ψ (w, 0) Φ = fun y => Φ (y + w) := by
  funext y
  simp [GlobalTheory.WeilM.schr]

theorem acts_exists {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E} {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    {M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W} {χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W}
    {r s r' s' : ℕ} (hP : GlobalTheory.ThK.IsPair B M χX χW om r s r' s') (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)
    (hx1 : x.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v)) (hx2 : x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (evFin F v))
    (φ : (Fin n × Fin d → Fv F v) → ℂ) (hφ : φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) :
    ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om x) φ φ₁ := by
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hP.weil
  set T := om x with hTdef
  have hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), T Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun Φ hΦ => hW.pres x Φ hΦ
  have hcomm := comm_off hP v x hx1 hx2
  have hfib := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v B.ψ T hP.base.std (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace B.ψ hP.base.std) hkeep
    (fun μ hμ Φ hΦ => hW.unit μ hμ x Φ hΦ) hcomm
  have htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : Fin n × Fin d → AF F,
      ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p) := by
    intro u hu p Φ hΦ
    have h := hcomm u hu p 0 Φ hΦ
    rw [smul_zero, schr_trans, schr_trans] at h
    exact h
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin n × Fin d) v
  refine ⟨(R 0)⁻¹ • fun t => T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)), ?_, ?_⟩
  · exact (GlobalTheory.WeilM.SB _).smul_mem (R 0)⁻¹ (GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ (hkeep _ (hR φ hφ).2))
  · intro r hr
    funext y
    set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef
    have hu : evFin F v u = 0 := by simp [hudef, GlobalTheory.LatVac.evFin_liftV]
    set p : Fin n × Fin d → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef
    have hyp : y + u • (-y) = p := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]
      rw [← liftV_one_mul]
      ring
    have hpat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) p := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    set Φ₀ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R with hΦ₀
    set Φ₁ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r with hΦ₁
    set Φ₂ : (Fin n × Fin d → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
    have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR φ hφ).2
    have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (GlobalTheory.T.adelicSchwartzSpace_translate_mem_of_mem _ _ hm₀)
    have hfz : ∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y := hr.1 y z hz
      have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
      have hpz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (p + z) := fun u' hu' => by
        rw [smul_add, hpat u' hu', hz u' hu', add_zero]
      have e3 : R (p + z) = R 0 := by simpa using (hR φ hφ).1 0 (p + z) hpz
      have e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp [hu]
      simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
      rw [e4, e2, e3, e1]
      field_simp
      ring
    have h0 := hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
    have h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p := by
      rw [hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]
    rw [h0, h2]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, hpdef, Pi.smul_apply, smul_eq_mul]
    field_simp

theorem acts_unique {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) {φ φ₁ φ₂ : (κ → Fv F v) → ℂ} (hφ : φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v))
    (h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) T φ φ₁) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ :=
  GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ φ₁ φ₂ hφ fun r hr => (h1 r hr).symm.trans (h2 r hr)

end GlobalTheory.ThK.LocalOps

namespace GlobalTheory.ThK.LocalOps

theorem actsEx (_hP : GlobalTheory.FunPr.Hypotheses₂) : GlobalTheory.ThK.ActsEx := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v
  have hex : ∀ x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J, x.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v) →
      x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (evFin F v) → ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v),
        ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om x) φ φ₁ :=
    fun x hx1 hx2 φ hφ => acts_exists hP v x hx1 hx2 φ hφ
  refine ⟨fun g hg h hh φ hφ => ?_, fun u hu φ hφ => ?_, GlobalTheory.T.weilRep_smooth_at_finitePlace B X W M χX χW om r s r' s' hP v hex⟩
  · obtain ⟨φ₁, h1, h2⟩ := hex (g, h) hg hh φ hφ
    exact ⟨φ₁, ⟨h1, h2⟩, fun φ₂ hφ₂ => acts_unique v _ hφ hφ₂.2 h2⟩
  · refine ⟨GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u) φ,
      ⟨GlobalTheory.SchrSB.schr_mem_SB B.ψ hP.base.std.1 v _ φ hφ, GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v u hu φ⟩,
      fun φ₂ hφ₂ => acts_unique v _ hφ hφ₂.2 (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v u hu φ)⟩

end GlobalTheory.ThK.LocalOps

namespace GlobalTheory.ThK.LocalOps

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem acts_comp (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {T₁ T₂ : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ}
    (h₁ : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T₁ Φ ∈ GlobalTheory.WeilM.schA F κ) {φ φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (a : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) T₁ φ φ₁) (b : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) T₂ φ₁ φ₂) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (T₂ ∘ T₁) φ φ₂ := by
  intro r hr
  have hr1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) φ₁ r := ⟨hr.1, by rw [← a r hr]; exact h₁ _ hr.2⟩
  show T₂ (T₁ _) = _
  rw [a r hr, b r hr1]

theorem acts_mul (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {T₁ T₂ : Module.End ℂ ((κ → AF F) → ℂ)}
    (h₁ : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T₁ Φ ∈ GlobalTheory.WeilM.schA F κ) {φ φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (a : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) T₁ φ φ₁) (b : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) T₂ φ₁ φ₂) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (T₂ * T₁) φ φ₂ :=
  acts_comp v h₁ a b

theorem acts_lin (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hex : ∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) T φ φ₁)
    {φ ψ φ₁ ψ₁ : (κ → Fv F v) → ℂ} (hφ : φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) (hψ : ψ ∈ GlobalTheory.WeilM.SB (κ → Fv F v))
    (h₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) T φ φ₁) (h₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) T ψ ψ₁) (a b : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) T (a • φ + b • ψ) (a • φ₁ + b • ψ₁) := by
  have hs : a • φ + b • ψ ∈ GlobalTheory.WeilM.SB (κ → Fv F v) :=
    add_mem ((GlobalTheory.WeilM.SB _).smul_mem a hφ) ((GlobalTheory.WeilM.SB _).smul_mem b hψ)
  obtain ⟨χ, -, hχ⟩ := hex _ hs
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v
  have e : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) (a • φ + b • ψ) R =
      a • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R + b • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) ψ R := by
    funext x; simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have e' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) (a • φ₁ + b • ψ₁) R =
      a • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ₁ R + b • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) ψ₁ R := by
    funext x; simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have key : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) χ R = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) (a • φ₁ + b • ψ₁) R := by
    rw [← hχ R (hR _ hs), e, map_add, map_smul, map_smul, h₁ R (hR φ hφ), h₂ R (hR ψ hψ), e']
  have hχe : χ = a • φ₁ + b • ψ₁ := by
    funext t
    have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i)) := by
      intro u' hu'; funext i; exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    have hRz : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by
      simpa using (hR φ hφ).1 0 _ hz
    have := congrFun key (fun i => GlobalTheory.LatVac.liftV v (t i))
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, GlobalTheory.LatVac.evFin_liftV, hRz] at this
    exact mul_right_cancel₀ hR0 this
  rw [← hχe]
  exact hχ

end GlobalTheory.ThK.LocalOps

namespace GlobalTheory.ThK.LocalOps

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem evI_of_at {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {z : AF F} (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F z = 0 := by
  have h := hz ((1 : Ainf F), (0 : Af F)) (by
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (0 : Af F) = 0
    exact map_zero _)
  have h1 : (1 : Ainf F) * z.1 = 0 := congrArg Prod.fst h
  rw [one_mul] at h1
  show InfiniteAdeleRing.ringEquiv_mixedSpace F z.1 = 0
  rw [h1, map_zero]

theorem evI_add (a b : AF F) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (a + b) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F a + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evFin_of_at {v w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (hwv : w ≠ v) {z : AF F} (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z) :
    evFin F w z = 0 := by
  have h := hz (GlobalTheory.LatVac.liftV w 1) (by
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (GlobalTheory.AdelicU.singleFin w 1) = 0
    exact GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hwv) 1)
  have := congrArg (evFin F w) h
  rw [smul_eq_mul, map_mul, GlobalTheory.LatVac.evFin_liftV, one_mul, map_zero] at this
  exact this

open Classical in

theorem pure_split (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (φ ρ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F w) → ℂ) (x : κ → AF F)
    (hfin : (Function.mulSupport fun w => φ w fun i => evFin F w (x i)).Finite) (hρ : ∀ w, w ≠ v → ρ w = φ w) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f ρ x =
      ρ v (fun i => evFin F v (x i)) * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v fun _ => 1) x := by
  classical
  set s : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) := insert v hfin.toFinset with hs
  have hv : v ∈ s := Finset.mem_insert_self _ _
  have h1 : Function.mulSupport (fun w => ρ w fun i => evFin F w (x i)) ⊆ (s : Set _) := by
    intro w hw
    by_cases hwv : w = v
    · subst hwv; exact hv
    · refine Finset.mem_coe.2 (Finset.mem_insert_of_mem ((Set.Finite.mem_toFinset _).2 ?_))
      simpa [hρ w hwv] using hw
  have h2 : Function.mulSupport (fun w => (Function.update φ v (fun _ => 1) : ∀ w, (κ → Fv F w) → ℂ) w
      fun i => evFin F w (x i)) ⊆ (s : Set _) := by
    intro w hw
    by_cases hwv : w = v
    · subst hwv; exact hv
    · refine Finset.mem_coe.2 (Finset.mem_insert_of_mem ((Set.Finite.mem_toFinset _).2 ?_))
      simpa [Function.update_of_ne hwv] using hw
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
  rw [finprod_eq_prod_of_mulSupport_subset _ h1, finprod_eq_prod_of_mulSupport_subset _ h2,
    ← Finset.mul_prod_erase s _ hv, ← Finset.mul_prod_erase s _ hv]
  have e : ∏ w ∈ s.erase v, (ρ w fun i => evFin F w (x i)) =
      ∏ w ∈ s.erase v, ((Function.update φ v (fun _ => 1) : ∀ w, (κ → Fv F w) → ℂ) w fun i => evFin F w (x i)) := by
    refine Finset.prod_congr rfl fun w hw => ?_
    have hwv := Finset.ne_of_mem_erase hw
    rw [hρ w hwv, Function.update_of_ne hwv]
  rw [e, Function.update_self]
  ring

open Classical in

theorem acts_pure (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ)
    (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F w) → ℂ) (φ₁ : (κ → Fv F v) → ℂ)
    (hpure : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ GlobalTheory.WeilM.schA F κ)
    (hfin : ∀ x : κ → AF F, (Function.mulSupport fun w => φ w fun i => evFin F w (x i)).Finite)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) T (φ v) φ₁) :
    T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v φ₁) := by
  classical
  set r : (κ → AF F) → ℂ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v fun _ => 1) with hr
  have e0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) (φ v) r := by
    funext x
    rw [pure_split v f φ φ x (hfin x) fun _ _ => rfl]
    rfl
  have hrest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) (φ v) r := by
    refine ⟨fun x z hz => ?_, e0 ▸ hpure⟩
    have hzi : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (z i) := fun i u hu => congrFun (hz u hu) i
    simp only [hr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    congr 1
    · congr 1
      funext i
      rw [Pi.add_apply, evI_add, evI_of_at (hzi i), add_zero]
    · congr 1
      funext w
      by_cases hwv : w = v
      · subst hwv; simp [Function.update_self]
      · simp only [Function.update_of_ne hwv, Pi.add_apply, map_add, evFin_of_at hwv (hzi _), add_zero]
  rw [e0, h r hrest]
  funext x
  rw [pure_split v f φ (Function.update φ v φ₁) x (hfin x) fun w hw => Function.update_of_ne hw _ _,
    Function.update_self]
  rfl

end GlobalTheory.ThK.LocalOps
end
end
