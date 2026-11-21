import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplitting
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSelfDualLatticeOfMemAllLatticeCompletionsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittCoreProjectionMemLatticeOfSplits
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalMatrixSandwichMemCompletedHomLatticeSelf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalMatrixSandwichMemCompletedIdealLatticeHo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletedHomLatticeModulusDepthMemShift

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt intAt latV latA)

noncomputable section
namespace GlobalTheory.RatLat

theorem dual_gens {A K W : Type} [CommRing A] [IsDomain A] [IsDedekindDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] [AddCommGroup W] [Module K W] [Module A W] [IsScalarTower A K W] (M : Submodule A W)
    (hfg : M.FG) (hden : ∀ v : W, ∃ d : A, d ≠ 0 ∧ d • v ∈ M) :
    ∃ (m : ℕ) (g : Fin m → W) (Φ : Fin m → W →ₗ[K] K), (∀ i, g i ∈ M) ∧
      (∀ i, ∀ x ∈ M, Φ i x ∈ (algebraMap A K).range) ∧ ∀ x, x = ∑ i, Φ i x • g i := by
  classical
  haveI hfin : Module.Finite A M := Module.Finite.iff_fg.2 hfg
  have hcancel : ∀ (d : A) (x : W), d ≠ 0 → d • x = 0 → x = 0 := by
    intro d x hd h
    rw [← IsScalarTower.algebraMap_smul K d x] at h
    exact (smul_eq_zero.1 h).resolve_left ((map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hd)
  haveI hflat : Module.Flat A M := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨d, hd⟩
    have : (d : A) • (x : W) = 0 := congrArg Subtype.val hd
    exact Subtype.ext (hcancel d x (nonZeroDivisors.coe_ne_zero d) this)
  haveI hfp : Module.FinitePresentation A M := Module.finitePresentation_of_finite _ _
  haveI hproj : Module.Projective A M := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, π, hπ⟩ := Module.Finite.exists_fin' A M
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let g : Fin m → W := fun i => (π (Pi.single i 1) : W)
  have hg : ∀ i, g i ∈ M := fun i => (π (Pi.single i 1)).2
  have hexp : ∀ x : M, (x : W) = ∑ i, (algebraMap A K (σ x i)) • g i := by
    intro x
    have h1 : π (σ x) = x := LinearMap.congr_fun hσ x
    conv_lhs => rw [← h1, LinearMap.pi_apply_eq_sum_univ π (σ x)]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, IsScalarTower.algebraMap_smul]
    congr 2
    congr 1
    funext j
    simp [Pi.single_apply, eq_comm]
  have hsp : Submodule.span K (M : Set W) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨d, hd, hv⟩ := hden v
    have hd' : algebraMap A K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hd
    have : v = (algebraMap A K d)⁻¹ • (d • v) := by
      rw [← IsScalarTower.algebraMap_smul K d v, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hv)
  have hunitW : ∀ x : nonZeroDivisors A, IsUnit (algebraMap A (Module.End A W) x) :=
    (isLocalizedModule_id (nonZeroDivisors A) W K).map_units
  have hunitK : ∀ x : nonZeroDivisors A, IsUnit (algebraMap A (Module.End A K) x) :=
    (isLocalizedModule_id (nonZeroDivisors A) K K).map_units
  haveI hloc : IsLocalizedModule (nonZeroDivisors A) M.subtype := by
    refine ⟨hunitW, fun v => ?_, fun {x y} h => ⟨1, by simpa using Subtype.ext h⟩⟩
    obtain ⟨d, hd, hv⟩ := hden v
    exact ⟨(⟨d • v, hv⟩, ⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩), rfl⟩
  let φ : Fin m → M →ₗ[A] K := fun i => (Algebra.linearMap A K) ∘ₗ (LinearMap.proj i) ∘ₗ σ
  let Φ0 : Fin m → W →ₗ[A] K := fun i => IsLocalizedModule.lift (nonZeroDivisors A) M.subtype (φ i) hunitK
  have hΦ0 : ∀ i (x : M), Φ0 i (x : W) = algebraMap A K (σ x i) := fun i x =>
    IsLocalizedModule.lift_apply _ M.subtype (φ i) hunitK x
  let Φ : Fin m → W →ₗ[K] K := fun i => (Φ0 i).extendScalarsOfIsLocalization (nonZeroDivisors A) K
  have hΦ : ∀ i (x : M), Φ i (x : W) = algebraMap A K (σ x i) := fun i x => hΦ0 i x
  refine ⟨m, g, Φ, hg, fun i x hx => ⟨σ ⟨x, hx⟩ i, (hΦ i ⟨x, hx⟩).symm⟩, fun x => ?_⟩
  have hL : (LinearMap.id : W →ₗ[K] W) = ∑ i, (LinearMap.smulRight (Φ i) (g i)) := by
    refine LinearMap.ext_on hsp fun y hy => ?_
    rw [LinearMap.id_apply, LinearMap.sum_apply]
    simp only [LinearMap.smulRight_apply]
    refine (hexp ⟨y, hy⟩).trans (Finset.sum_congr rfl fun i _ => ?_)
    exact congrArg (· • g i) (hΦ i ⟨y, hy⟩).symm
  have := LinearMap.congr_fun hL x
  simpa using this

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem coe_mem_int_iff {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (f : F) :
    algebraMap F (Fv F v) f ∈ v.adicCompletionIntegers F ↔ v.valuation F f ≤ 1 := by
  rw [mem_adicCompletionIntegers]
  exact Iff.of_eq (congrArg (· ≤ 1) (valuedAdicCompletion_eq_valuation' v f))

theorem int_of_intAf {F : Type} [Field F] [NumberField F] (f : F) (h : algebraMap F (Af F) f ∈ intAf F) :
    f ∈ (algebraMap (𝓞 F) F).range := by
  refine mem_integers_of_valuation_le_one F f fun v => ?_
  have := h v
  rw [AlgHom.commutes] at this
  exact (coe_mem_int_iff v f).1 this

theorem smul_intAf {F : Type} [Field F] [NumberField F] (c : 𝓞 F) {α : Af F} (hα : α ∈ intAf F) :
    (algebraMap (𝓞 F) F c) • α ∈ intAf F := by
  intro v
  rw [map_smul, Algebra.smul_def]
  refine mul_mem ((coe_mem_int_iff v _).2 (valuation_le_one v c)) (hα v)

def extF {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (ψ : E →ₗ[F] F) : AF F ⊗[F] E →ₗ[F] AF F :=
  (TensorProduct.rid F (AF F)).toLinearMap ∘ₗ LinearMap.lTensor (AF F) ψ

theorem extF_tmul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (ψ : E →ₗ[F] F) (a : AF F) (e : E) :
    extF ψ (a ⊗ₜ[F] e) = ψ e • a := by
  simp [extF]

def extV {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (Φ : (Fin n → E) →ₗ[F] F)
    (y : Fin n → AF F ⊗[F] E) : AF F :=
  ∑ j, extF (Φ ∘ₗ LinearMap.single F (fun _ : Fin n => E) j) (y j)

theorem extV_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (Φ : (Fin n → E) →ₗ[F] F)
    (a : AF F) (x : Fin n → E) : extV Φ (fun i => a ⊗ₜ[F] x i) = Φ x • a := by
  classical
  simp only [extV, extF_tmul, LinearMap.comp_apply, ← Finset.sum_smul, ← map_sum]
  congr 2
  exact Finset.univ_sum_single x

theorem extV_add {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (Φ : (Fin n → E) →ₗ[F] F)
    (y y' : Fin n → AF F ⊗[F] E) : extV Φ (y + y') = extV Φ y + extV Φ y' := by
  simp [extV, map_add, Finset.sum_add_distrib]

theorem extV_neg {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (Φ : (Fin n → E) →ₗ[F] F)
    (y : Fin n → AF F ⊗[F] E) : extV Φ (-y) = -extV Φ y := by
  simp [extV, map_neg, Finset.sum_neg_distrib]

theorem extV_zero {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (Φ : (Fin n → E) →ₗ[F] F) :
    extV Φ (0 : Fin n → AF F ⊗[F] E) = 0 := by
  simp [extV]

theorem smul_pairA {F : Type} [Field F] [NumberField F] (f : F) (α : Af F) :
    f • pairA F 0 α = pairA F 0 (f • α) :=
  Prod.ext (smul_zero f) rfl

theorem coord_int {D : D7} {S : HSp D} (L : Lat S) (Φ : (Fin S.rank → D.host.E) →ₗ[D.host.F] D.host.F)
    (hΦ : ∀ x ∈ L, Φ x ∈ (algebraMap (𝓞 D.host.F) D.host.F).range) (z : Fin S.rank → D.host.E)
    (hz : (fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i) ∈ latV S L (fun _ => True)) :
    Φ z ∈ (algebraMap (𝓞 D.host.F) D.host.F).range := by
  have key : ∀ y ∈ latV S L (fun _ => True), ∃ β ∈ intAf D.host.F, extV Φ y = pairA D.host.F 0 β := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hαi, -, a, ha, x, hx, rfl⟩ := hy
      rw [Set.mem_singleton_iff] at ha
      subst ha
      simp only [one_mul]
      obtain ⟨c, hc⟩ := hΦ x hx
      refine ⟨algebraMap (𝓞 D.host.F) D.host.F c • α, smul_intAf c hαi, ?_⟩
      rw [extV_gen, ← hc, smul_pairA]
    | zero => exact ⟨0, fun v => by rw [map_zero]; exact zero_mem _, by rw [extV_zero]; rfl⟩
    | add y y' _ _ hy hy' =>
      obtain ⟨β, hβ, e⟩ := hy
      obtain ⟨β', hβ', e'⟩ := hy'
      exact ⟨β + β', fun v => by rw [map_add]; exact add_mem (hβ v) (hβ' v),
        by rw [extV_add, e, e', GlobalTheory.FinPlLoc.pairA_add]⟩
    | neg y _ hy =>
      obtain ⟨β, hβ, e⟩ := hy
      exact ⟨-β, fun v => by rw [map_neg]; exact neg_mem (hβ v), by rw [extV_neg, e, GlobalTheory.FinPlLoc.pairA_neg]⟩
  obtain ⟨β, hβ, e⟩ := key _ hz
  rw [extV_gen, smul_pairA] at e
  have hb : Φ z • (1 : Af D.host.F) = β := congrArg Prod.snd e
  apply int_of_intAf
  rw [Algebra.algebraMap_eq_smul_one, hb]
  exact hβ

theorem mem_of_mem_latV : ∀ (D : D7) (S : HSp D) (L : Lat S), Submodule.IsLattice D.host.E L → ∀ z : Fin S.rank → D.host.E, (fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i) ∈ latV S L (fun _ => True) → z ∈ L := by
  intro D S L hL z hz
  classical
  let M : Submodule (𝓞 D.host.F) (Fin S.rank → D.host.E) := L.restrictScalars (𝓞 D.host.F)
  obtain ⟨t, g0, hg0, hgen⟩ := GlobalTheory.FinPlLoc.exists_gens L hL.fg
  have hMfg : M.FG := by
    refine ⟨Finset.univ.image g0, ?_⟩
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hg0 k
    · intro x hx
      obtain ⟨c, rfl⟩ := hgen x hx
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [← Int.cast_smul_eq_zsmul (𝓞 D.host.F)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 D.host.E) (nonZeroDivisors (𝓞 D.host.F)))
      D.host.E := IsIntegralClosure.isLocalization (𝓞 D.host.F) D.host.F D.host.E (𝓞 D.host.E)
  have hden : ∀ v : Fin S.rank → D.host.E, ∃ d : 𝓞 D.host.F, d ≠ 0 ∧ d • v ∈ M := by
    intro v
    have hv : v ∈ Submodule.span D.host.E (L : Set (Fin S.rank → D.host.E)) := by
      rw [hL.span_eq_top]; trivial
    obtain ⟨⟨_, a, ha, rfl⟩, hs⟩ := multiple_mem_span_of_mem_localization_span
      (Algebra.algebraMapSubmonoid (𝓞 D.host.E) (nonZeroDivisors (𝓞 D.host.F))) D.host.E _ v hv
    rw [Submodule.span_eq] at hs
    refine ⟨a, nonZeroDivisors.coe_ne_zero ⟨a, ha⟩, ?_⟩
    show a • v ∈ L
    rw [← IsScalarTower.algebraMap_smul (𝓞 D.host.E) a v]
    exact hs
  obtain ⟨m, g, Φ, hg, hΦ, hid⟩ := dual_gens (K := D.host.F) M hMfg hden
  rw [hid z]
  refine Submodule.sum_mem _ fun k _ => ?_
  obtain ⟨c, hc⟩ := coord_int L (Φ k) (hΦ k) z hz
  rw [← hc, IsScalarTower.algebraMap_smul D.host.F c (g k)]
  exact (M.smul_mem c (hg k) : c • g k ∈ M)

end GlobalTheory.RatLat
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt intAt latV latA)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_lattice_of_rational_mem_completion_all_places : ∀ (D : D7) (S : HSp D) (L : Lat S), Submodule.IsLattice D.host.E L → ∀ z : Fin S.rank → D.host.E, (fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i) ∈ latV S L (fun _ => True) → z ∈ L := by
  atlas_forward_decl GlobalTheory.RatLat.mem_of_mem_latV
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.CoreComp

variable {D : D7}

def finV {n : ℕ} (z : Fin n → D.host.E) : Fin n → AE D := fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i

theorem rat_entry {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) (i : Fin m) (j : Fin n) :
    (rat A : Mx D m n) i j = (1 : AF D.host.F) ⊗ₜ[D.host.F] A i j := rfl

theorem rat_mulVec_finV {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) (z : Fin n → D.host.E) :
    (rat A : Mx D m n) *ᵥ finV z = finV (A *ᵥ z) := by
  funext i
  simp only [finV, mulVec, dotProduct, TensorProduct.tmul_sum, rat_entry, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem finV_mem {S : HSp D} {L : Lat S} {z : Fin S.rank → D.host.E} (hz : z ∈ L) :
    finV z ∈ latV S L (fun _ => True) :=
  AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, fun v hv => absurd trivial hv, 1, rfl, z, hz,
    by funext i; simp [finV]⟩

theorem mem_of_finV (S : HSp D) (L : Lat S) (hL : Submodule.IsLattice D.host.E L) (z : Fin S.rank → D.host.E)
    (hz : finV z ∈ latV S L (fun _ => True)) : z ∈ L := GlobalTheory.T.mem_lattice_of_rational_mem_completion_all_places D S L hL z hz

theorem loc_iff {S : HSp D} {L : Lat S} (hL : Submodule.IsLattice D.host.E L) (y : Fin S.rank → AE D) :
    y ∈ latV S L (fun _ => True) ↔ (∀ i, y i ∈ idAt D (fun _ => True)) ∧
      ∀ v, ∀ e ∈ intAt D (· = v), e • y ∈ latV S L (· = v) := by
  have := ((GlobalTheory.FinPl.localComponents D (fun _ => True)).2 S).2.2.2 L y hL
  simpa using this

end GlobalTheory.CoreComp

namespace GlobalTheory.CoreComp

variable {D : D7}

theorem mulVec_mem_idAt {m n : ℕ} (M : Mx D m n) {y : Fin n → AE D} (hy : ∀ i, y i ∈ idAt D (fun _ => True)) (i : Fin m) :
    (M *ᵥ y) i ∈ idAt D (fun _ => True) := mulVec_idAt M hy i

theorem witt_core_inclusion_maps_split_lattices {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}
    (hL : Submodule.IsLattice D.host.E L) (hL₀ : Submodule.IsLattice D.host.E L₀) (hM : ∀ v, MonoAt d L L₀ v)
    {z : Fin S₀.rank → D.host.E} (hz : z ∈ L₀) : d.i₀ *ᵥ z ∈ L := by
  apply mem_of_finV S L hL
  rw [← rat_mulVec_finV]
  have hz' := (loc_iff hL₀ _).1 (finV_mem hz)
  refine (loc_iff hL _).2 ⟨mulVec_mem_idAt _ hz'.1, fun v e he => ?_⟩
  have h1 := hz'.2 v e he
  rw [← Matrix.mulVec_smul]
  refine (hM v _).2 ⟨fun i => ?_, fun i => ?_, ?_⟩
  · have e0 : (d.pX *ᵥ ((rat d.i₀ : Mx D S.rank S₀.rank) *ᵥ e • finV z)) i = 0 := by
      rw [Matrix.mulVec_mulVec, show (rat d.i₀ : Mx D S.rank S₀.rank) = d.j0 from rfl, HypDec.pX_j0, Matrix.zero_mulVec]; rfl
    rw [e0]
    have : GlobalTheory.FinPl.colMul d.jX i 0 = 0 := by funext k; simp [GlobalTheory.FinPl.colMul]
    rw [this]; exact zero_mem _
  · have e0 : (d.pY *ᵥ ((rat d.i₀ : Mx D S.rank S₀.rank) *ᵥ e • finV z)) i = 0 := by
      rw [Matrix.mulVec_mulVec, show (rat d.i₀ : Mx D S.rank S₀.rank) = d.j0 from rfl, HypDec.pY_j0, Matrix.zero_mulVec]; rfl
    rw [e0]
    have : GlobalTheory.FinPl.colMul d.jY i 0 = 0 := by funext k; simp [GlobalTheory.FinPl.colMul]
    rw [this]; exact zero_mem _
  · rw [Matrix.mulVec_mulVec, show (rat d.i₀ : Mx D S.rank S₀.rank) = d.j0 from rfl, HypDec.p0_j0, Matrix.one_mulVec]
    exact h1

theorem witt_core_projection_maps_split_lattices {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}
    (hL : Submodule.IsLattice D.host.E L) (hL₀ : Submodule.IsLattice D.host.E L₀) (hM : ∀ v, MonoAt d L L₀ v)
    {y : Fin S.rank → D.host.E} (hy : y ∈ L) : d.q0 *ᵥ y ∈ L₀ := by
  apply mem_of_finV S₀ L₀ hL₀
  rw [← rat_mulVec_finV]
  have hy' := (loc_iff hL _).1 (finV_mem hy)
  refine (loc_iff hL₀ _).2 ⟨mulVec_mem_idAt _ hy'.1, fun v e he => ?_⟩
  rw [← Matrix.mulVec_smul]
  exact ((hM v _).1 (hy'.2 v e he)).2.2

theorem qA_maps {S A B : HSp D} (o : OrthDec S A B) {L : Lat S} {LA : Lat A} {LB : Lat B}
    (hL : Submodule.IsLattice D.host.E L) (hLA : Submodule.IsLattice D.host.E LA) (hO : ∀ v, OrthAt o L LA LB v)
    {y : Fin S.rank → D.host.E} (hy : y ∈ L) : o.qA *ᵥ y ∈ LA := by
  apply mem_of_finV A LA hLA
  rw [← rat_mulVec_finV]
  have hy' := (loc_iff hL _).1 (finV_mem hy)
  refine (loc_iff hLA _).2 ⟨mulVec_mem_idAt _ hy'.1, fun v e he => ?_⟩
  rw [← Matrix.mulVec_smul]
  exact ((hO v _).1 (hy'.2 v e he)).1

theorem rat_mulVec_mem_latA {S T : HSp D} (m : Matrix (Fin T.rank) (Fin S.rank) D.host.E) {L : Lat S} {L' : Lat T}
    (h : ∀ x ∈ L, m *ᵥ x ∈ L') {P : GlobalTheory.FinPl.Pl D → Prop} {y : Fin S.rank → AE D} (hy : y ∈ latA S L P) :
    (rat m : Mx D T.rank S.rank) *ᵥ y ∈ latA T L' P := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hα', a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨α, hα, hα', a, ha, m *ᵥ x, h x hx, ?_⟩
    funext i
    simp only [mulVec, dotProduct, Finset.mul_sum, TensorProduct.tmul_sum, rat_entry, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1; ring
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [mulVec_neg]; exact neg_mem hx

theorem latO_sandwich {S T S' T' : HSp D} {ΛS : Lat S} {ΛT : Lat T} {ΛS' : Lat S'} {ΛT' : Lat T'}
    (M : Matrix (Fin T'.rank) (Fin T.rank) D.host.E) (N : Matrix (Fin S.rank) (Fin S'.rank) D.host.E)
    (hS : IsSelfDualC S ΛS) (hS' : IsSelfDualC S' ΛS') (hT' : IsSelfDualC T' ΛT')
    (hN : ∀ y ∈ ΛS', N *ᵥ y ∈ ΛS) (hM : ∀ y ∈ ΛT, M *ᵥ y ∈ ΛT') {u : WO S T}
    (hu : u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) :
    ((rat M : Mx D T'.rank T.rank) * u * (rat N : Mx D S.rank S'.rank) : WO S' T') ∈
      latO S' T' (ΛS' : Set _) (ΛT' : Set _) fun _ => True := by
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S' T' ΛS' ΛT' hS' hT']
  refine ⟨fun i j => ?_, fun y hy => ?_⟩
  · simp only [Matrix.mul_apply]
    exact sum_mem fun l _ => Ideal.mul_mem_right _ _
      (sum_mem fun k _ => Ideal.mul_mem_left _ _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu k l))
  · show ((rat M : Mx D T'.rank T.rank) * u * (rat N : Mx D S.rank S'.rank)) *ᵥ y ∈ _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact rat_mulVec_mem_latA M hM
      (GlobalTheory.FinPl.LatMem.latO_maps hS hu (GlobalTheory.OrthSumLat.rat_mulVec_mem_latV N hN hy))

theorem hatMx_sandwich {S T S' T' : HSp D} {ΛS : Lat S} {ΛT : Lat T} {ΛS' : Lat S'} {ΛT' : Lat T'}
    (M : Matrix (Fin T'.rank) (Fin T.rank) D.host.E) (N : Matrix (Fin S.rank) (Fin S'.rank) D.host.E)
    (hN : ∀ y ∈ ΛS', N *ᵥ y ∈ ΛS) (hM : ∀ y ∈ ΛT, M *ᵥ y ∈ ΛT') (I : Ideal (𝓞 D.host.E))
    {z : Mx D T.rank S.rank} (hz : z ∈ hatMx (I • homLat ΛS ΛT)) :
    (rat M : Mx D T'.rank T.rank) * z * (rat N : Mx D S.rank S'.rank) ∈ hatMx (I • homLat ΛS' ΛT') := by
  have key : ∀ X ∈ I • homLat ΛS ΛT, M * X * N ∈ I • homLat ΛS' ΛT' := by
    intro X hX
    refine Submodule.smul_induction_on hX (fun r hr Y hY => ?_) (fun a b ha hb => ?_)
    · have e : M * (r • Y) * N = r • (M * Y * N) := by rw [Matrix.mul_smul, Matrix.smul_mul]
      rw [e]
      refine Submodule.smul_mem_smul hr ?_
      intro y hy
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact hM _ (hY _ (hN y hy))
    · rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem ha hb
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, X, hX, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, M * X * N, key X hX, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul, TensorProduct.tmul_sum, rat_entry,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  | zero => rw [Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg, Matrix.neg_mul]; exact neg_mem hx

end GlobalTheory.CoreComp

namespace GlobalTheory.CoreComp

theorem core_mem_latCore : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    ∀ u ∈ (pcFB W F σ h h').Γ₀, ((F.oB σ h').resT _ u).1 ∈ latCore G (2 * σ + 2) := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h' u hu
  have I := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hq T L μ0 hL sc G W M hM F hF
  have sd : ∀ X : Node, X.InRange D.R.m → (∀ j, X ≠ .grid 0 j) → IsSelfDualC (G.V X) (G.Λ X) :=
    fun X h1 h2 => (G.isV h1 h2).sd
  have sdG3 : IsSelfDualC (G.V (.grid (2 * σ + 2 + 1) 0)) (G.Λ (.grid (2 * σ + 2 + 1) 0)) :=
    sd _ ⟨by omega, Nat.zero_le _⟩ (fun j e => by cases e)
  have sdG2 : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    sd _ ⟨h', Nat.zero_le _⟩ (fun j e => by cases e)
  have sdC3 : IsSelfDualC (G.V (.core (2 * σ + 2 + 1))) (G.Λ (.core (2 * σ + 2 + 1))) :=
    sd (.core (2 * σ + 2 + 1)) (show 2 * σ + 2 + 1 ≤ D.R.m by omega) (fun j e => by cases e)
  have sdC2 : IsSelfDualC (G.V (.core (2 * σ + 2))) (G.Λ (.core (2 * σ + 2))) :=
    sd (.core (2 * σ + 2)) (show 2 * σ + 2 ≤ D.R.m by omega) (fun j e => by cases e)
  have sd0 : IsSelfDualC (F.V₀ σ) (lat0 F σ h') := (I.2.1 σ h').1
  have hMJ : ∀ v, MonoAt (F.dJ (σ + 1) h) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.core (2 * (σ + 1) + 1))) v :=
    fun v => ((I.2.1 (σ + 1) h).2.1 v).2
  have hMB : ∀ v, MonoAt (F.dB σ h') (G.Λ (.grid (2 * σ + 2) 0)) (lat0 F σ h') v := fun v => ((I.2.1 σ h').2.1 v).1
  have hOB := (I.2.1 σ h').2.2.2

  have hN : ∀ y ∈ G.Λ (.core (2 * σ + 2 + 1)), (F.dJ (σ + 1) h).i₀ *ᵥ y ∈ G.Λ (.grid (2 * σ + 2 + 1) 0) :=
    fun y hy => witt_core_inclusion_maps_split_lattices (F.dJ (σ + 1) h) sdG3.1 sdC3.1 hMJ hy
  have hMm : ∀ y ∈ G.Λ (.grid (2 * σ + 2) 0),
      ((F.oB σ h').qA * (F.dB σ h').q0) *ᵥ y ∈ G.Λ (.core (2 * σ + 2)) := fun y hy => by
    rw [← Matrix.mulVec_mulVec]
    exact qA_maps (F.oB σ h') sd0.1 sdC2.1 hOB (witt_core_projection_maps_split_lattices (F.dB σ h') sdG2.1 sd0.1 hMB hy)
  have hx := AddSubgroup.mem_comap.1 hu
  set x := ((F.dJ (σ + 1) h).ext0 _).comp ((F.dB σ h').inc0 _) u with hxdef
  have hc : ((F.oB σ h').resT _ u).1 =
      (rat ((F.oB σ h').qA * (F.dB σ h').q0) : Mx D _ _) * x * (rat (F.dJ (σ + 1) h).i₀ : Mx D _ _) := by
    rw [OrthDec.resT_apply, rat_mul, hxdef]
    change (F.oB σ h').pA * u = (F.oB σ h').pA * (F.dB σ h').p0 * ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) *
      (F.dJ (σ + 1) h).j0
    have e1 : (F.dB σ h').p0 * (F.dB σ h').j0 = 1 := HypDec.p0_j0 _
    have e2 : (F.dJ (σ + 1) h).p0 * (F.dJ (σ + 1) h).j0 = 1 := HypDec.p0_j0 _
    calc (F.oB σ h').pA * u = (F.oB σ h').pA * (((F.dB σ h').p0 * (F.dB σ h').j0) * u *
          ((F.dJ (σ + 1) h).p0 * (F.dJ (σ + 1) h).j0)) := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [hc]
  refine ⟨?_, fun e he => ?_⟩
  · exact latO_sandwich _ _ (isSelfDualC_neg sdG3) (isSelfDualC_neg sdC3) sdC2 hN hMm hx.1
  · rw [← Matrix.smul_mul, ← Matrix.mul_smul]
    exact hatMx_sandwich _ _ hN hMm _ (hx.2 e he)

end GlobalTheory.CoreComp
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobi_step_core_component_mem_core_depth_lattice : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ u ∈ (pcFB W F σ h h').Γ₀, ((F.oB σ h').resT _ u).1 ∈ latCore G (2 * σ + 2) := by
  atlas_forward_decl GlobalTheory.CoreComp.core_mem_latCore
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.WittCoreLat

open GlobalTheory.FinPl.LatMem

variable {D : D7}

theorem rat_mulVec_tmul {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (c : AF D.host.F) (z : Fin n → D.host.E) :
    rat M *ᵥ (fun i => c ⊗ₜ[D.host.F] z i) = fun k => c ⊗ₜ[D.host.F] (M *ᵥ z) k := by
  funext k
  simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply]
  rw [TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show ((1 : AF D.host.F) ⊗ₜ[D.host.F] M k j) * (c ⊗ₜ[D.host.F] z j) = c ⊗ₜ[D.host.F] (M k j * z j)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem i₀_mulVec_mem {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}
    (hL : ∀ z : Fin S.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV S L (· = v)) → z ∈ L)
    (hmono : ∀ v, MonoAt d L L₀ v) : ∀ y ∈ L₀, d.i₀ *ᵥ y ∈ L := by
  intro y hy
  have hX : d.qX * d.i₀ = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.pX_j0)
  have hY : d.qY * d.i₀ = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.pY_j0)
  have h0 : d.q0 * d.i₀ = 1 := rat_injective (by rw [rat_mul, rat_one]; exact d.p0_j0)
  refine hL _ fun v => ?_
  set c : AF D.host.F := pairA D.host.F 0 (indP D.host.F (· = v))
  refine (hmono v _).2 ⟨fun i => ?_, fun i => ?_, ?_⟩
  · have : d.pX *ᵥ (fun i => c ⊗ₜ[D.host.F] (d.i₀ *ᵥ y) i) = 0 := by
      rw [HypDec.pX, rat_mulVec_tmul, Matrix.mulVec_mulVec, hX, Matrix.zero_mulVec]
      funext k; exact TensorProduct.tmul_zero _ _
    rw [this]
    have h' : GlobalTheory.FinPl.colMul d.jX i ((0 : Fin ρ → AE D) i) = 0 := by
      funext k; simp [GlobalTheory.FinPl.colMul]
    rw [h']; exact zero_mem _
  · have : d.pY *ᵥ (fun i => c ⊗ₜ[D.host.F] (d.i₀ *ᵥ y) i) = 0 := by
      rw [HypDec.pY, rat_mulVec_tmul, Matrix.mulVec_mulVec, hY, Matrix.zero_mulVec]
      funext k; exact TensorProduct.tmul_zero _ _
    rw [this]
    have h' : GlobalTheory.FinPl.colMul d.jY i ((0 : Fin ρ → AE D) i) = 0 := by
      funext k; simp [GlobalTheory.FinPl.colMul]
    rw [h']; exact zero_mem _
  · rw [HypDec.p0, rat_mulVec_tmul, Matrix.mulVec_mulVec, h0, Matrix.one_mulVec]
    exact AddSubgroup.subset_closure ⟨indP D.host.F (· = v), indicatorAdele_mem_integralAdeles' _ _, indicatorAdele_supported _ _, 1, rfl, y, hy,
      by funext k; rw [one_mul]⟩

end GlobalTheory.WittCoreLat
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittCoreEmbedding_mulVec_mem_lattice_of_splits : ∀ {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}, (∀ z : Fin S.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV S L (· = v)) → z ∈ L) → (∀ v, MonoAt d L L₀ v) → ∀ y ∈ L₀, d.i₀ *ᵥ y ∈ L := by
  atlas_forward_decl GlobalTheory.WittCoreLat.i₀_mulVec_mem
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.q0_mulVec_mem_of_splits : ∀ {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}, (∀ z : Fin S₀.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV S₀ L₀ (· = v)) → z ∈ L₀) → (∀ v, MonoAt d L L₀ v) → ∀ t ∈ L, d.q0 *ᵥ t ∈ L₀ := by
  first | exact @GlobalTheory.FinPl.CoreProj.wittCoreProjection_mem_lattice_of_splits | exact GlobalTheory.FinPl.CoreProj.wittCoreProjection_mem_lattice_of_splits | (intros; apply GlobalTheory.FinPl.CoreProj.wittCoreProjection_mem_lattice_of_splits <;> assumption)
end
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

open GlobalTheory.FinPl.LatMem in

theorem GlobalTheory.FinPl.projB_mem_of_orthAt : ∀ {D : D7} {S A B : HSp D} (o : OrthDec S A B) {L : Lat S} {LA : Lat A} {LB : Lat B}, (∀ z : Fin B.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV B LB (· = v)) → z ∈ LB) → (∀ v, OrthAt o L LA LB v) → ∀ t ∈ L, o.qB *ᵥ t ∈ LB := by
  intro D S A B o L LA LB hLG hO t ht
  apply hLG
  intro v
  have hY : (fun i => pairA D.host.F 0 (indP D.host.F (· = v)) ⊗ₜ[D.host.F] (1 * t i)) ∈ latV S L (· = v) :=
    AddSubgroup.subset_closure ⟨indP D.host.F (· = v), indicatorAdele_mem_integralAdeles' _ _, indicatorAdele_supported _ _, 1, rfl, t, ht, rfl⟩
  have h2 := ((hO v _).1 hY).2
  convert h2 using 1
  funext i
  simp only [OrthDec.pB, rat, Matrix.mulVec, dotProduct, Matrix.map_apply, one_mul]
  rw [TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show _ = (1 : AF D.host.F) ⊗ₜ[D.host.F] (o.qB i j) * _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonalSummandProjection_mem_lattice_of_splits : ∀ {D : D7} {S A B : HSp D} (o : OrthDec S A B) {L : Lat S} {LA : Lat A} {LB : Lat B}, (∀ z : Fin B.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV B LB (· = v)) → z ∈ LB) → (∀ v, OrthAt o L LA LB v) → ∀ t ∈ L, o.qB *ᵥ t ∈ LB := by
  atlas_forward_decl GlobalTheory.FinPl.projB_mem_of_orthAt
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalMatrix_sandwich_mem_completed_ideal_latticeHom : ∀ {D : D7} {m n m' n' : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {M : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)} {M' : Submodule (𝓞 D.host.E) (Fin m' → D.host.E)} (𝔪 : Ideal (𝓞 D.host.E)) (j : Matrix (Fin n) (Fin n') D.host.E) (q : Matrix (Fin m') (Fin m) D.host.E), (∀ y ∈ M, j *ᵥ y ∈ Λ) → (∀ t ∈ Λ', q *ᵥ t ∈ M') → ∀ x : Mx D m n, x ∈ hatMx (𝔪 • homLat Λ Λ') → rat q * x * rat j ∈ hatMx (𝔪 • homLat M M') := by
  first | exact @GlobalTheory.TwistHatMx.rat_conj_mem_hatMx | exact GlobalTheory.TwistHatMx.rat_conj_mem_hatMx | (intros; apply GlobalTheory.TwistHatMx.rat_conj_mem_hatMx <;> assumption)
end
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.LineFB

theorem latO_negSp_le' {D : D7} (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (negSp S) T LS LT P ≤ latO S T LS LT P := by
  unfold latO
  rw [AddSubgroup.closure_le]
  rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  rw [← neg_neg (Matrix.of _)]
  refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem line_mem : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    ∀ u ∈ (pcFB W F σ h h').Γ₀, ((F.oB σ h').resT _ u).2 ∈ lineLat F (σ + 1) := by
  intro D hD T L μ0 hL sc G W M hM F hF σ h h' u hu
  obtain ⟨-, hfr, hline⟩ := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hD T L μ0 hL sc G W M hM F hF
  have hx := AddSubgroup.mem_comap.1 hu
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply] at hx
  have hSc : IsSelfDualC (G.V (.core (2 * (σ + 1) + 1))) (G.Λ (.core (2 * (σ + 1) + 1))) :=
    (G.isV (X := .core (2 * (σ + 1) + 1)) (by simp [Node.InRange]; omega) (fun j e => Node.noConfusion e)).sd
  have hSg : IsSelfDualC (G.V (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) :=
    (G.isV (X := .grid (2 * (σ + 1) + 1) 0) (by simp [Node.InRange]; omega) (fun j e => by simp at e)).sd
  have hTg : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    (G.isV (X := .grid (2 * σ + 2) 0) (by simp [Node.InRange]; omega) (fun j e => by simp at e)).sd
  have hℓ := (hfr σ h').2.2.1
  have hℓ' := hline (σ + 1)
  have h0 := (hfr σ h').1
  have hj : ∀ y ∈ G.Λ (.core (2 * (σ + 1) + 1)), (F.dJ (σ + 1) h).i₀ *ᵥ y ∈ G.Λ (.grid (2 * (σ + 1) + 1) 0) :=
    GlobalTheory.T.wittCoreEmbedding_mulVec_mem_lattice_of_splits _ (GlobalTheory.T.mem_selfDualLattice_of_mem_all_latticeCompletions hSg) fun v => ((hfr (σ + 1) h).2.1 v).2
  have hq : ∀ t ∈ G.Λ (.grid (2 * σ + 2) 0), ((F.oB σ h').qB * (F.dB σ h').q0) *ᵥ t ∈
      idLat (G.pl.stA sc ^ (σ + 1) * (G.pl.stAbar sc ^ (σ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) := by
    intro t ht
    rw [← Matrix.mulVec_mulVec]
    exact GlobalTheory.T.orthogonalSummandProjection_mem_lattice_of_splits _ (GlobalTheory.T.mem_selfDualLattice_of_mem_all_latticeCompletions hℓ) (hfr σ h').2.2.2 _
      (GlobalTheory.T.q0_mulVec_mem_of_splits _ (GlobalTheory.T.mem_selfDualLattice_of_mem_all_latticeCompletions h0) (fun v => ((hfr σ h').2.1 v).1) t ht)
  have key : ((F.oB σ h').resT _ u).2 =
      rat ((F.oB σ h').qB * (F.dB σ h').q0) * ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) * rat (F.dJ (σ + 1) h).i₀ := by
    rw [OrthDec.resT_apply, rat_mul]
    change _ = (F.oB σ h').pB * (F.dB σ h').p0 * ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) * (F.dJ (σ + 1) h).j0
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (F.dB σ h').p0, HypDec.p0_j0, Matrix.one_mul, HypDec.p0_j0, Matrix.mul_one]
  rw [key]
  have hz := GlobalTheory.T.rationalMatrix_sandwich_mem_completed_homLattice_selfDual hSg hSc hℓ _ _ hj hq _ (latO_negSp_le' _ _ _ _ _ hx.1)
  obtain ⟨e, he, -⟩ := W.cosVec_is
  have hd := GlobalTheory.T.rationalMatrix_sandwich_mem_completed_ideal_latticeHom G.modul _ ((F.oB σ h').qB * (F.dB σ h').q0) hj hq _ (hx.2 e he)
  refine GlobalTheory.T.completedHomLattice_modulus_depth_mem_shift hD μ0 hL G _ _ _ hSc hℓ hℓ' _ hz ⟨e, he, ?_⟩
  rwa [Matrix.mul_smul, Matrix.smul_mul] at hd

end GlobalTheory.LineFB

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobi_depth_lattice_line_components_mem : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ u ∈ (pcFB W F σ h h').Γ₀, ((F.oB σ h').resT _ u).2 ∈ lineLat F (σ + 1) := by
  atlas_forward_decl GlobalTheory.LineFB.line_mem
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.BoxFB

theorem isHalf_mul_left {D : D7} {k m n : ℕ} {e : AE D} (a : Mx D k m) {u : Mx D m n} (hu : IsHalf e u) :
    IsHalf e (a * u) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_left_comm, hu l j]

theorem vacG_boxT {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {T A B S : HSp D} (d : OrthDec T A B)
    {Γ : AddSubgroup (WO S T)} {ΓA : AddSubgroup (WO S A)} {ΓB : AddSubgroup (WO S B)}
    (hA : ∀ u ∈ Γ, (d.resT S u).1 ∈ ΓA) (hB : ∀ u ∈ Γ, (d.resT S u).2 ∈ ΓB)
    {fA : WO S A → ℂ} {fB : WO S B → ℂ} (vA : VacG ψ S A ΓA fA) (vB : VacG ψ S B ΓB fB) :
    VacG ψ S T Γ (d.boxT S fA fB) := by
  refine ⟨d.isThetaFunO_boxT vA.1 vB.1, fun u hu => ?_, fun e he u hu hh => ?_⟩
  · rw [d.heisO_boxT, map_nsmul, Prod.smul_fst, Prod.smul_snd, vA.2.1 _ (hA u hu), vB.2.1 _ (hB u hu)]
  · rw [d.heisO_boxT, vA.2.2 e he _ (hA u hu) (by rw [d.resT_apply]; exact isHalf_mul_left _ hh),
      vB.2.2 e he _ (hB u hu) (by rw [d.resT_apply]; exact isHalf_mul_left _ hh)]

end GlobalTheory.BoxFB

namespace GlobalTheory.BoxFB

theorem core_mem : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ u ∈ (pcFB W F σ h h').Γ₀, ((F.oB σ h').resT _ u).1 ∈ latCore G (2 * σ + 2) := GlobalTheory.T.jacobi_step_core_component_mem_core_depth_lattice

theorem line_mem : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ u ∈ (pcFB W F σ h h').Γ₀, ((F.oB σ h').resT _ u).2 ∈ lineLat F (σ + 1) := GlobalTheory.T.fourierJacobi_depth_lattice_line_components_mem

theorem vacG_boxT_fb : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ Ξ₁ Φ₀, VacG W.ψ _ _ (latCore G (2 * σ + 2)) Ξ₁ → VacG W.ψ _ _ (lineLat F (σ + 1)) Φ₀ → VacG W.ψ _ _ (pcFB W F σ h h').Γ₀ ((F.oB σ h').boxT _ Ξ₁ Φ₀) := by
  intro D hD T L μ0 hL sc G W M hM F hF σ h h' Ξ₁ Φ₀ hΞ hΦ
  exact vacG_boxT (F.oB σ h') (core_mem D hD T L μ0 hL sc G W M hM F hF σ h h')
    (line_mem D hD T L μ0 hL sc G W M hM F hF σ h h') hΞ hΦ

end GlobalTheory.BoxFB

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobi_depthDatum_mul_lineVacuum_isVacuum : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ Ξ₁ Φ₀, VacG W.ψ _ _ (latCore G (2 * σ + 2)) Ξ₁ → VacG W.ψ _ _ (lineLat F (σ + 1)) Φ₀ → VacG W.ψ _ _ (pcFB W F σ h h').Γ₀ ((F.oB σ h').boxT _ Ξ₁ Φ₀) := by
  atlas_forward_decl GlobalTheory.BoxFB.vacG_boxT_fb
end
