import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiRegularAlongOfEtale
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountSt
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.InhabSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndepBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HermTools

open ReciprocityTheory.GeometryOfNumbersTheory Matrix NumberField
open scoped ComplexOrder ComplexConjugate

variable {K E : Type*} [Field K] [Field E] {V V' : Type*} [AddCommGroup V] [Module K V]

def biadd (h : HermFam K V) (σ : K →+* ℂ) : V →+ V →+ ℂ :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (h.form σ x) (h.add_right σ x))
    fun x x' => AddMonoidHom.ext fun y => h.form_add_left σ x x' y

theorem ext_form {h h' : HermFam K V} (e : ∀ σ x y, h.form σ x y = h'.form σ x y) : h = h' := by
  obtain ⟨f, _⟩ := h
  obtain ⟨f', _⟩ := h'
  obtain rfl : f = f' := funext fun σ => funext₂ (e σ)
  rfl

section Complex

variable (h : HermFam K V) (σ : K →+* ℂ) {ι : Type*} [Fintype ι]

def csq (c : ι → ℂ) (v : ι → V) : ℝ := (∑ i, ∑ k, conj (c i) * c k * h.form σ (v i) (v k)).re

def cnrm (c : ι → ℂ) (v : ι → V) : ℝ := Real.sqrt (csq h σ c v)

theorem csq_map (a : ι → K) (v : ι → V) :
    csq h σ (fun i => σ (a i)) v = (h.form σ (∑ i, a i • v i) (∑ i, a i • v i)).re := by
  rw [csq, h.form_sum_left]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [h.form_sum_right]
  exact Finset.sum_congr rfl fun k _ => by rw [h.form_smul_left, h.smul_right, mul_assoc]

theorem cnrm_map (a : ι → K) (v : ι → V) : cnrm h σ (fun i => σ (a i)) v = h.nrm σ (∑ i, a i • v i) :=
  congrArg Real.sqrt (csq_map h σ a v)


theorem csq_comb {κ : Type*} [Fintype κ] (c : ι → ℂ) (a : ι → κ → K) (b : κ → V) :
    csq h σ c (fun i => ∑ k, a i k • b k) = csq h σ (fun k => ∑ i, c i * σ (a i k)) b := by
  simp only [csq, h.form_sum_left, h.form_sum_right, h.form_smul_left, h.smul_right, map_sum, map_mul,
    Finset.mul_sum, Finset.sum_mul]
  refine congrArg _ ?_
  simp only [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv ⟨fun t => (t.2.2.1, t.2.2.2, t.2.1, t.1), fun t => (t.2.2.2, t.2.2.1, t.1, t.2.1),
    fun _ => rfl, fun _ => rfl⟩ _ _ fun t => by simp only [Equiv.coe_fn_mk]; ring

theorem csq_nonneg (c : ι → ℂ) (v : ι → V) : 0 ≤ csq h σ c v := by
  let S := Submodule.span K (Set.range v)
  have : FiniteDimensional K S := FiniteDimensional.span_of_finite K (Set.finite_range v)
  let b := Module.finBasis K S
  have e : v = fun i => ∑ k, b.repr ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ k • (b k : V) := funext fun i => by
    exact (congrArg S.subtype (b.sum_repr ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩).symm).trans (map_sum _ _ _)
  rw [e, csq_comb]
  generalize (fun k => ∑ i, c i * σ _) = x
  have := (h.posDef σ _ _ (b.linearIndependent.map' S.subtype S.ker_subtype)).posSemidef.dotProduct_mulVec_nonneg x
  refine (Complex.nonneg_iff.1 this).1.trans_eq (congrArg _ ?_)
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]


theorem nrm_pos {x : V} (hx : x ≠ 0) : 0 < h.nrm σ x := by
  have := (h.posDef σ 1 ![x] (by simpa using hx)).diag_pos (i := 0)
  exact Real.sqrt_pos.2 (Complex.pos_iff.1 this).1

end Complex

def ofCoords {P : (K →+* ℂ) → Type*} [∀ σ, Fintype (P σ)] (φ : ∀ σ, V →ₛₗ[σ] (P σ → ℂ))
    (G : ∀ σ, Matrix (P σ) (P σ) ℂ) (hG : ∀ σ, (G σ).PosDef)
    (hφ : ∀ σ n (v : Fin n → V), LinearIndependent K v → LinearIndependent ℂ fun i => φ σ (v i)) :
    HermFam K V where
  form σ x y := star (φ σ x) ⬝ᵥ G σ *ᵥ φ σ y
  add_right σ x y z := by rw [map_add, mulVec_add, dotProduct_add]
  smul_right σ a x y := by rw [map_smulₛₗ, mulVec_smul, dotProduct_smul, smul_eq_mul]
  conj_symm σ x y := by
    rw [starRingEnd_apply, ← star_dotProduct_star, star_star, star_mulVec, (hG σ).1.eq, ← dotProduct_mulVec]
  posDef σ n v hv := by
    classical
    have := (hG σ).conjTranspose_mul_mul_same (B := Matrix.of fun p i => φ σ (v i) p)
      (Matrix.mulVec_injective_iff.2 (hφ σ n v hv))
    convert this using 1
    ext i j
    simp [dotProduct, mulVec, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm

def comap [AddCommGroup V'] [Module K V'] (h : HermFam K V) (f : V' →ₗ[K] V) (hf : Function.Injective f) :
    HermFam K V' where
  form σ x y := h.form σ (f x) (f y)
  add_right σ x y z := by rw [map_add, h.add_right]
  smul_right σ a x y := by rw [map_smul, h.smul_right]
  conj_symm σ x y := h.conj_symm σ _ _
  posDef σ n v hv := h.posDef σ n _ (hv.map' f (LinearMap.ker_eq_bot.2 hf))

@[simp] theorem nrm_comap [AddCommGroup V'] [Module K V'] (h : HermFam K V) (f : V' →ₗ[K] V)
    (hf : Function.Injective f) (σ : K →+* ℂ) (x : V') : (comap h f hf).nrm σ x = h.nrm σ (f x) := rfl

theorem isConjInv_comap [AddCommGroup V'] [Module K V'] {h : HermFam K V} (hh : h.IsConjInv) (f : V' →ₗ[K] V)
    (hf : Function.Injective f) : (comap h f hf).IsConjInv := fun σ _ _ => hh σ _ _

def scale (h : HermFam K V) (c : (K →+* ℂ) → ℝ) (hc : ∀ σ, 0 < c σ) : HermFam K V where
  form σ x y := (c σ ^ 2 : ℝ) * h.form σ x y
  add_right σ x y z := by rw [h.add_right, mul_add]
  smul_right σ a x y := by rw [h.smul_right, mul_left_comm]
  conj_symm σ x y := by rw [map_mul, h.conj_symm, Complex.conj_ofReal]
  posDef σ n v hv := (h.posDef σ n v hv).smul (a := ((c σ ^ 2 : ℝ) : ℂ))
    (Complex.zero_lt_real.2 (pow_pos (hc σ) 2))

@[simp] theorem nrm_scale (h : HermFam K V) (c : (K →+* ℂ) → ℝ) (hc : ∀ σ, 0 < c σ) (σ : K →+* ℂ) (x : V) :
    (scale h c hc).nrm σ x = c σ * h.nrm σ x := by
  rw [HermFam.nrm, scale, Complex.re_ofReal_mul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hc σ).le, HermFam.nrm]

def basisCoords {n : Type*} [Finite n] (b : Module.Basis n K V) (σ : K →+* ℂ) : V →ₛₗ[σ] (n → ℂ) where
  toFun x i := σ (b.repr x i)
  map_add' x y := funext fun i => by simp
  map_smul' a x := funext fun i => by simp

theorem linearIndependent_basisCoords {n ι : Type*} [Finite n] (b : Module.Basis n K V) (σ : K →+* ℂ) {v : ι → V}
    (hv : LinearIndependent K v) : LinearIndependent ℂ fun i => basisCoords b σ (v i) :=
  letI := σ.toAlgebra
  linearIndependent_algebraMap_comp_iff.2 (hv.map' b.equivFun.toLinearMap b.equivFun.ker)

def ofGram {n : Type*} [Fintype n] (b : Module.Basis n K V) (G : (K →+* ℂ) → Matrix n n ℂ)
    (hG : ∀ σ, (G σ).PosDef) : HermFam K V :=
  ofCoords (P := fun _ => n) (basisCoords b) G hG fun σ _ _ => linearIndependent_basisCoords b σ

theorem form_ofGram {n : Type*} [Fintype n] (b : Module.Basis n K V) (G : (K →+* ℂ) → Matrix n n ℂ)
    (hG : ∀ σ, (G σ).PosDef) (σ : K →+* ℂ) (i j : n) : (ofGram b G hG).form σ (b i) (b j) = G σ i j := by
  classical
  simp [ofGram, ofCoords, basisCoords, dotProduct, mulVec, Finsupp.single_apply, apply_ite]

theorem isConjInv_ofGram {n : Type*} [Fintype n] (b : Module.Basis n K V) {G : (K →+* ℂ) → Matrix n n ℂ}
    (hG : ∀ σ, (G σ).PosDef) (hc : ∀ σ i j, G (ComplexEmbedding.conjugate σ) i j = conj (G σ i j)) :
    (ofGram b G hG).IsConjInv := fun σ x y => by
  simp [ofGram, ofCoords, basisCoords, dotProduct, mulVec, hc]

def ofBasis {n : Type*} [Fintype n] [DecidableEq n] (b : Module.Basis n K V) : HermFam K V :=
  ofGram b (fun _ => 1) fun _ => PosDef.one

theorem nrm_ofBasis {n : Type*} [Fintype n] [DecidableEq n] (b : Module.Basis n K V) (σ : K →+* ℂ) (i : n) :
    (ofBasis b).nrm σ (b i) = 1 := by
  simp [HermFam.nrm, ofBasis, form_ofGram]

theorem isConjInv_ofBasis {n : Type*} [Fintype n] [DecidableEq n] (b : Module.Basis n K V) :
    (ofBasis b).IsConjInv := isConjInv_ofGram b _ fun _ i j => by simp [Matrix.one_apply, apply_ite]

section Extend

variable [AddCommGroup V'] [Module E V'] {j : K →+* E}

structure IsExtension (ι : V →ₛₗ[j] V') : Prop where

  indep : ∀ (n : ℕ) (v : Fin n → V), LinearIndependent K v → LinearIndependent E fun i => ι (v i)

  span : Submodule.span E (Set.range ι) = ⊤

variable {ι : V →ₛₗ[j] V'} (hι : IsExtension ι)

def IsExtension.basis {n : ℕ} (b : Module.Basis (Fin n) K V) : Module.Basis (Fin n) E V' :=
  Module.Basis.mk (hι.indep n b b.linearIndependent) (hι.span.ge.trans (Submodule.span_le.2 (by
    rintro _ ⟨x, rfl⟩
    rw [← b.sum_repr x, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))))

@[simp] theorem IsExtension.basis_apply {n : ℕ} (b : Module.Basis (Fin n) K V) (i : Fin n) :
    hι.basis b i = ι (b i) := Module.Basis.mk_apply _ _ _

variable [FiniteDimensional K V]

include hι in

theorem IsExtension.finrank_eq : Module.finrank E V' = Module.finrank K V :=
  (Module.finrank_eq_card_basis (hι.basis (Module.finBasis K V))).trans (Fintype.card_fin _)

def extend (h : HermFam K V) : HermFam E V' :=
  ofGram (hι.basis (Module.finBasis K V)) (fun τ => h.gram (τ.comp j) (Module.finBasis K V))
    fun _ => h.posDef _ _ _ (Module.finBasis K V).linearIndependent

theorem form_extend (h : HermFam K V) (τ : E →+* ℂ) (x y : V) :
    (extend hι h).form τ (ι x) (ι y) = h.form (τ.comp j) x y := by
  let b := Module.finBasis K V
  have e (i k) : (extend hι h).form τ (ι (b i)) (ι (b k)) = h.form (τ.comp j) (b i) (b k) := by
    rw [← hι.basis_apply, ← hι.basis_apply]
    exact form_ofGram _ _ _ τ i k
  rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [map_sum, map_smulₛₗ, HermFam.form_sum_left, HermFam.form_sum_right, HermFam.form_smul_left,
    HermFam.smul_right, e, RingHom.comp_apply]

theorem nrm_extend (h : HermFam K V) (τ : E →+* ℂ) (x : V) : (extend hι h).nrm τ (ι x) = h.nrm (τ.comp j) x :=
  congrArg (fun z : ℂ => Real.sqrt z.re) (form_extend hι h τ x x)

theorem isConjInv_extend {h : HermFam K V} (hh : h.IsConjInv) : (extend hι h).IsConjInv :=
  isConjInv_ofGram _ _ fun τ _ _ => hh (τ.comp j) _ _

end Extend

example (σ : ℚ →+* ℂ) : csq (ofBasis (Pi.basisFun ℚ (Fin 2))) σ ![Complex.I, 2] (Pi.basisFun ℚ (Fin 2)) = 5 := by
  simp only [csq, ofBasis, form_ofGram, Fin.sum_univ_two]
  simp
  norm_num

end GlobalTheory.HermTools
end
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HermTools

open NumberField

variable {K E : Type*} [Field K] [Field E] {X X' : Type*} [AddCommGroup X] [Module K X] [AddCommGroup X']
  [Module E X'] {j : K →+* E} (ι : X →ₛₗ[j] X')

def extSpace (V : Submodule K X) : Submodule E X' := Submodule.span E (ι '' V)

def extMap (V : Submodule K X) : V →ₛₗ[j] extSpace ι V :=
  (ι.domRestrict V).codRestrict _ fun x => Submodule.subset_span ⟨x, x.2, rfl⟩

@[simp] theorem coe_extMap (V : Submodule K X) (x : V) : (extMap ι V x : X') = ι x := rfl

theorem isExtension_extMap
    (h : ∀ (n : ℕ) (v : Fin n → X), LinearIndependent K v → LinearIndependent E fun i => ι (v i))
    (V : Submodule K X) : IsExtension (extMap ι V) := by
  refine ⟨fun n v hv => .of_comp (extSpace ι V).subtype (h n _ (hv.map' V.subtype V.ker_subtype)), ?_⟩
  refine Submodule.map_injective_of_injective (extSpace ι V).injective_subtype ?_
  rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
  exact congrArg _ (Set.image_eq_range ι V).symm

variable [Module (𝓞 K) X] [IsScalarTower (𝓞 K) K X] [Module (𝓞 E) X'] [IsScalarTower (𝓞 E) E X']

def extLat (M : Submodule (𝓞 K) X) : Submodule (𝓞 E) X' := Submodule.span (𝓞 E) (ι '' M)

theorem extLat_span (S : Set X) : extLat ι (Submodule.span (𝓞 K) S) = Submodule.span (𝓞 E) (ι '' S) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => exact map_zero ι ▸ zero_mem _
  | add a b _ _ ha hb => exact map_add ι a b ▸ add_mem ha hb
  | smul c a _ ha =>
    rw [← algebraMap_smul K, map_smulₛₗ]
    exact algebraMap_smul E (RingOfIntegers.mapRingHom j c) (ι a) ▸ Submodule.smul_mem _ _ ha

theorem fg_extLat {M : Submodule (𝓞 K) X} (h : M.FG) : (extLat ι M).FG := by
  obtain ⟨S, rfl⟩ := h
  exact extLat_span ι S ▸ Submodule.fg_span (S.finite_toSet.image ι)

variable {ι} in

theorem IsExtension.span_extLat (hι : IsExtension ι) {M : Submodule (𝓞 K) X}
    (h : Submodule.span K (M : Set X) = ⊤) : Submodule.span E (extLat ι M : Set X') = ⊤ := by
  refine top_le_iff.1 (hι.span.ge.trans (Submodule.span_le.2 ?_))
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ Submodule.span K (M : Set X) := h ▸ trivial
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (Submodule.subset_span ⟨x, hx, rfl⟩)
  | zero => exact map_zero ι ▸ zero_mem _
  | add a b _ _ ha hb => exact map_add ι a b ▸ add_mem ha hb
  | smul c a _ ha => exact map_smulₛₗ ι c a ▸ Submodule.smul_mem _ _ ha

structure IsFull (M : Submodule (𝓞 K) X) : Prop where

  fg : M.FG

  span : Submodule.span K (M : Set X) = ⊤

variable {ι} {M : Submodule (𝓞 K) X}

theorem IsFull.finiteDimensional (h : IsFull M) : FiniteDimensional K X := by
  obtain ⟨⟨S, rfl⟩, h⟩ := h
  rw [Submodule.span_span_of_tower] at h
  exact ⟨S, h⟩

theorem IsFull.latRank_eq [NumberField K] (h : IsFull M) : ReciprocityTheory.GeometryOfNumbersTheory.latRank K M = Module.finrank K X := by
  rw [ReciprocityTheory.GeometryOfNumbersTheory.latRank, h.span, finrank_top]

theorem IsFull.extLat (h : IsFull M) (hι : IsExtension ι) : IsFull (extLat ι M) :=
  ⟨fg_extLat ι h.fg, hι.span_extLat h.span⟩

theorem isFull_span {n : Type*} [Finite n] (b : Module.Basis n K X) :
    IsFull (Submodule.span (𝓞 K) (Set.range b)) :=
  ⟨Submodule.fg_span (Set.finite_range b), by rw [Submodule.span_span_of_tower, b.span_eq]⟩

end GlobalTheory.HermTools

namespace GlobalTheory.Vanishing

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX isPushout_sections)
open GlobalTheory.LB GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Points
open H0
open scoped ComplexOrder

variable {Y T : Scheme.{0}}

section Field

variable {k E : Type} [Field k] [Field E] {p : Y ⟶ Sp k} {B : LB Y} {O O' : Y.Opens}

instance H0.moduleInt : Module (𝓞 k) (H0 p B O) := Module.compHom _ (algebraMap (𝓞 k) k)

instance H0.isScalarTowerInt : IsScalarTower (𝓞 k) k (H0 p B O) := IsScalarTower.of_compHom _ _ _

theorem restr_injective [IsIntegral Y] (h : O' ≤ O) (hne : (O' : Set Y).Nonempty) :
    Function.Injective (restr h : H0 p B O → H0 p B O') := by
  refine (injective_iff_map_eq_zero _).2 fun f hf => LB.sec_ext fun i => fun_ext_ger fun y hy => ?_
  have : Nonempty (O' ⊓ B.U i : Y.Opens) := ((nonempty_preirreducible_inter O'.2 (B.U i).2 hne ⟨y, hy.2⟩)).to_subtype
  have e : resG Y (inf_le_inf_right _ h) (f.loc i) = resG Y (inf_le_inf_right _ h) 0 :=
    (congrArg (·.loc i) hf).trans (map_zero _).symm
  exact congrArg _ (map_injective_of_isIntegral Y (homOfLE (inf_le_inf_right _ h)) e)

theorem finite_top (hp : IsProjOver p) (hB : B.IsLB) : Module.Finite k (H0 p B ⊤) := by
  letI := algebraΓOfHom p
  letI : Module k B.Sec := Module.compHom _ (algebraMap k Γ(Y, ⊤))
  haveI : IsScalarTower k Γ(Y, ⊤) B.Sec := IsScalarTower.of_compHom _ _ _
  have e (c : k) : algebraMap k Γ(Y, ⊤) c = algX p ⊤ c := by
    change p.appTop _ = _
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have := finite_coh_zero_twist_of_isProjOver (fun _ => rfl) hp hB
  have := Module.Finite.equiv ((cohZeroTwistEquiv B).restrictScalars k)
  exact Module.Finite.of_surjective
    ({ H0.ofSec p ⊤ with map_smul' := fun c σ => (e c ▸ ofSec_smul c σ :) } : B.Sec →ₗ[k] H0 p B ⊤)
    bijective_ofSec_top.2

variable [Algebra k E] {q : T ⟶ Sp E} {r : T ⟶ Y} (H : IsPullback r q p (spMap (algebraMap k E)))
  {B' : LB T} (hB : B.IsLB) (hB' : B'.IsLB) (a : ChartPull B' B r) {W : T.Opens}

include hB hB' in

theorem linearIndependent_pullChart (h : W ≤ r ⁻¹ᵁ O) (h' : r ⁻¹ᵁ O ≤ W) {ι : Type*} [Fintype ι]
    {f : ι → H0 p B O} (hf : LinearIndependent k f) :
    LinearIndependent E fun i => pullChart a H.w h (f i) := by
  refine Fintype.linearIndependent_iff.2 fun u hu j => (Module.forall_dual_apply_eq_zero_iff k (u j)).1 fun l =>
    Fintype.linearIndependent_iff.1 hf (fun i => l (u i)) (ext_germ fun y hy => ?_) j
  obtain ⟨c, hc⟩ := exists_chart hB y
  obtain ⟨⟨V, hV⟩, hyV, hle⟩ := exists_affine (memInf hy hc)
  obtain ⟨Λ, hΛ⟩ := Adelic.IndepBaseChange.exists_contract (isPushout_sections p q r H V hV) l
  have e : ∑ i, algX q _ (u i) * (r.appLE V (r ⁻¹ᵁ V ⊓ q ⁻¹ᵁ ⊤) inf_le_left).hom (resG Y hle ((f i).loc c)) = 0 :=
    fun_ext_ger fun z hz => by
      obtain ⟨d, hd⟩ := exists_chart hB' z
      have hz' := hle hz.1
      have e := congrArg (germ d z (h' hz'.1) hd) hu
      simp only [map_sum, germ_smul, germ_pullChart, map_zero] at e
      simp only [map_sum, map_mul, ger_algX, ger_appLE, ger_resG, map_zero]
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) ((Finset.mul_sum _ _ _).symm.trans
        ((congrArg ((r.stalkMap z).hom (tr B (r z) c (a.idx d)).val * ·) e).trans (mul_zero _)))
      rw [mul_left_comm, ← map_mul]
      exact congrArg (_ * (r.stalkMap z).hom ·) ((ger_resG hle _ hz.1 _).trans
        (germ_change c _ _ hz'.1 hz'.2 (a.le d hd) (f i)))
  have e₂ := (map_sum Λ _ _).symm.trans ((congrArg Λ e).trans (map_zero Λ))
  have e₃ := congrArg (ger y hyV) ((Finset.sum_congr rfl fun i _ => (hΛ _ _).symm).trans e₂)
  refine ⟨c, hc, ?_⟩
  simp only [map_sum, map_mul, map_zero, ger_resG] at e₃
  simp only [map_sum, germ_smul, map_zero]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) e₃
  exact congrArg (· * _) (ger_algX y hyV _).symm

include hB hB' in

theorem isExtension_pullChart_top (hp : IsProjOver p) (hq : IsProjOver q) :
    IsExtension (pullChart (O := ⊤) (W := ⊤) a H.w le_top) := by
  refine ⟨fun _ _ => linearIndependent_pullChart H hB hB' a _ le_top, ?_⟩
  have := finite_top hp hB
  have := finite_top hq hB'
  have : IsProper p := by
    obtain ⟨N, i, hi, e⟩ := hp
    have := isProper_str k N
    rw [← e]
    infer_instance
  have e : Module.finrank E (H0 q B' ⊤) = Module.finrank k (H0 p B ⊤) := by
    letI := algebraΓOfHom q
    rw [H0.finrank_top, H0.finrank_top, lineBundleGlobalSectionsDim_congr_picardClass hB' (LB.isLB_pull hB r) ((cls_eq_iff _ _).2 (lbIso_of_chartPull
      ⟨fun i _ => a.idx i, fun i _ hz => mem_pull.2 (a.le i hz), fun z i j hi hj => (a.g z i j hi hj).trans ?_⟩
      (LB.isLB_pull hB r)))]
    · exact FieldChangeInter.hdim_pull H hB 0
    · exact ((GlobalTheory.chartPullPull B r).g z (fun _ => a.idx i) (fun _ => a.idx j) (mem_pull.2 (a.le i hi))
        (mem_pull.2 (a.le j hj))).symm
  refine top_le_iff.1 (((linearIndependent_pullChart (W := ⊤) H hB hB' a le_top le_top
    (Module.finBasis k (H0 p B ⊤)).linearIndependent).span_eq_top_of_card_eq_finrank'
      ((Fintype.card_fin _).trans e.symm)).ge.trans (Submodule.span_mono ?_))
  rintro _ ⟨i, rfl⟩
  exact ⟨_, rfl⟩

end Field

section General

variable {k k' : Type} [CommRing k] [CommRing k'] {p : Y ⟶ Sp k} {q : T ⟶ Sp k'} {φ : k →+* k'} {r : T ⟶ Y}
  {P B N : LB Y} {B' : LB T} {O O' : Y.Opens} {W W' : T.Opens}

theorem restr_pullChart (a : ChartPull B' B r) (hq : r ≫ p = q ≫ spMap φ) (h : W ≤ r ⁻¹ᵁ O) (h' : W' ≤ r ⁻¹ᵁ O')
    (e : O' ≤ O) (e' : W' ≤ W) (f : H0 p B O) :
    restr e' (pullChart a hq h f) = pullChart a hq h' (restr e f) :=
  LB.sec_ext fun i => fun_ext_ger fun z hz => by
    change germ i z hz.1 hz.2 _ = germ i z hz.1 hz.2 _
    rw [germ_restr, germ_pullChart, germ_pullChart]
    exact congrArg _ (germ_restr _ _ _ _ _ _).symm

def polarMap (C : ProdChart P B N) (t : P.Sec) (ht : O ≤ nonzeroLocus t) : H0 p N ⊤ →ₗ[k] H0 p B O :=
  (C.mulEquiv (σ := H0.ofSec p O t) fun y hy i hi => by
    rw [germ_ofSec, isUnit_ger_iff]; exact ht hy).symm.toLinearMap ∘ₗ restr le_top

variable (p B) in

def polar (hP : P.IsLB) (hB : B.IsLB) (t : P.Sec) (ht : O ≤ nonzeroLocus t) : Submodule k (H0 p B O) :=
  LinearMap.range (polarMap (tensChart hP hB) t ht)

theorem mem_polar {hP : P.IsLB} {hB : B.IsLB} {t : P.Sec} {ht : O ≤ nonzeroLocus t} {f : H0 p B O} :
    f ∈ polar p B hP hB t ht ↔
      ∃ g : H0 p (tens P B) ⊤, restr le_top g = (tensChart hP hB).mul (H0.ofSec p O t) f :=
  exists_congr fun _ => LinearEquiv.symm_apply_eq _

theorem range_restr_le_polar (hP : P.IsLB) (hB : B.IsLB) (t : P.Sec) (ht : O ≤ nonzeroLocus t) :
    LinearMap.range (restr (le_top : O ≤ ⊤)) ≤ polar p B hP hB t ht := by
  rintro _ ⟨f, rfl⟩
  exact mem_polar.2 ⟨(tensChart hP hB).mul (H0.ofSec p ⊤ t) f, by rw [ProdChart.restr_mul, restr_ofSec]⟩

variable (σ : k →+* ℂ)

def cval : H0 p B O →ₛₗ[σ] (B.ι → CxPts p σ → ℂ) where
  toFun f i := ev p σ (O ⊓ B.U i) (f.loc i)
  map_add' f g := funext₂ fun i y => ev_add _ _ y
  map_smul' c f := funext₂ fun i y => by
    refine (ev_mul _ _ y).trans ?_
    by_cases h : y ∈ ptsIn p σ (O ⊓ B.U i)
    · exact congrArg (· * _) ((ev_res inf_le_left h _).trans (ev_algX (ptsIn_mono inf_le_left h) c))
    · simp only [Pi.smul_apply, ev_of_notMem h, mul_zero, smul_zero]

theorem cval_eq_val (f : H0 p B O) (i : B.ι) (y : CxPts p σ) (hO : y ∈ ptsIn p σ O) (hi : y ∈ ptsIn p σ (B.U i)) :
    cval σ f i y = val y.1 i hO hi f := ev_eq (mem_ptsIn_inf.2 ⟨hO, hi⟩) _

theorem cval_ofSec (s : B.Sec) : cval σ (H0.ofSec p ⊤ s) = secVal p σ s := funext₂ fun i y => by
  by_cases h : y ∈ ptsIn p σ (B.U i)
  · exact ev_res inf_le_right (mem_ptsIn_inf.2 ⟨mem_ptsIn_top, h⟩) _
  · exact (ev_of_notMem (fun e => h (mem_ptsIn_inf.1 e).2) _).trans (ev_of_notMem h _).symm

theorem cval_mem (f : H0 p B ⊤) : cval σ f ∈ fibSec p σ B := by
  obtain ⟨s, rfl⟩ := bijective_ofSec_top.2 f
  exact cval_ofSec σ s ▸ secVal_mem s

theorem cval_mem_holSec {D : ℕ} (R : AnRead p σ D) (f : H0 p B ⊤) : cval σ f ∈ R.holSec B := by
  obtain ⟨s, rfl⟩ := bijective_ofSec_top.2 f
  exact cval_ofSec σ s ▸ R.secVal_mem_holSec s

variable {σ}

def assocVal : ((tens (tens P B) N).ι → CxPts p σ → ℂ) →ₗ[ℂ] ((tens P (tens B N)).ι → CxPts p σ → ℂ) :=
  LinearMap.funLeft ℂ _ fun c => ((c.1, c.2.1), c.2.2)

theorem assocVal_mem_holSec {D : ℕ} {R : AnRead p σ D} {f : (tens (tens P B) N).ι → CxPts p σ → ℂ}
    (hf : f ∈ R.holSec _) : assocVal f ∈ R.holSec _ := by
  have e (c : (tens P (tens B N)).ι) : (tens P (tens B N)).U c = (tens (tens P B) N).U ((c.1, c.2.1), c.2.2) :=
    (inf_assoc _ _ _).symm
  refine ⟨⟨fun c c' y h h' => ?_, fun c y h => hf.1.2 _ y (e c ▸ h)⟩, fun c => e c ▸ hf.2 _⟩
  have g := e c ▸ h
  have g' := e c' ▸ h'
  refine (hf.1.1 _ _ y g g').trans (congrArg (· * _) ?_)
  rw [gv_tens g g', gv_tens h h', gv_tens (mem_ptsIn_inf.1 g).1 (mem_ptsIn_inf.1 g').1,
    gv_tens (mem_ptsIn_inf.1 h).2 (mem_ptsIn_inf.1 h').2, mul_assoc]

end General

theorem sum_tmul_eq_zero {E Ω A ι : Type*} [Field E] [Field Ω] [IsAlgClosed Ω] [CommRing A] [Algebra E Ω]
    [Algebra E A] [Algebra.FormallyUnramified E A] [Algebra.FiniteType E A] [Fintype ι] (c : ι → Ω) (a : ι → A)
    (h : ∀ φ : A →ₐ[E] Ω, ∑ i, c i * φ (a i) = 0) : ∑ i, c i ⊗ₜ[E] a i = 0 := by
  have := Algebra.FormallyUnramified.isReduced_of_field Ω (Ω ⊗[E] A)
  have : IsJacobsonRing (Ω ⊗[E] A) := isJacobsonRing_of_finiteType (A := Ω)
  refine (IsJacobsonRing.out this (Ideal.isRadical_bot (R := Ω ⊗[E] A))).le (Ideal.mem_sInf.2 fun m hm => ?_)
  have := hm.2
  letI := Ideal.Quotient.field m
  have := finite_of_finite_type_of_isJacobsonRing Ω ((Ω ⊗[E] A) ⧸ m)
  let e := AlgEquiv.ofBijective (Algebra.ofId Ω ((Ω ⊗[E] A) ⧸ m)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ψ := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ Ω m)
  refine Ideal.Quotient.eq_zero_iff_mem.1 (e.symm.injective ((map_sum ψ _ _).trans ?_))
  rw [map_zero, ← h ((ψ.restrictScalars E).comp Algebra.TensorProduct.includeRight)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← smul_eq_mul]
  exact (congrArg ψ (by simp [smul_tmul'])).trans (ψ.toLinearMap.map_smul (c i) (1 ⊗ₜ a i))

section Points

variable {E : Type} [Field E] {S : Scheme.{0}} {q : S ⟶ Sp E} {B : LB S}

theorem finite_cxPts (hq : IsFinite q) (τ : E →+* ℂ) : Finite (CxPts q τ) := by
  have : IsAffine S := isAffine_of_isAffineHom q
  letI := (algX q ⊤).toAlgebra
  letI := τ.toAlgebra
  have : Module.Finite E Γ(S, ⊤) := by
    have := q.finite_appTop.comp (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (.of E)).symm.commRingCatIsoToRingEquiv.surjective)
    rwa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] at this
  let e : CxPts q τ → (Γ(S, ⊤) →ₐ[E] ℂ) := fun z =>
    { evHom (mem_ptsIn_top (y := z)) with
      commutes' := fun a => (ev_eq _ _).symm.trans (ev_algX mem_ptsIn_top a) }
  exact Finite.of_injective e fun z z' hz => Subtype.ext
    (ext_of_valR (isAffineOpen_top _) mem_ptsIn_top mem_ptsIn_top fun f =>
      (ev_eq _ f).trans ((congrArg (fun q : _ →ₐ[E] ℂ => q f) hz).trans (ev_eq _ f).symm))

theorem linearIndependent_cval (hq : Etale q) (hB : B.IsLB) (τ : E →+* ℂ) {ι : Type*} [Fintype ι]
    {g : ι → H0 q B ⊤} (hg : LinearIndependent E g) :
    LinearIndependent ℂ fun i y => cval τ (g i) (pick hB y) y := by
  letI := τ.toAlgebra
  refine Fintype.linearIndependent_iff.2 fun u hu j => (Module.forall_dual_apply_eq_zero_iff E (u j)).1 fun l =>
    Fintype.linearIndependent_iff.1 hg (fun i => l (u i)) (ext_germ fun y hy => ?_) j
  obtain ⟨c, hc⟩ := exists_chart hB y
  obtain ⟨⟨V, hV⟩, hyV, hle⟩ := exists_affine (memInf hy hc)
  letI := (algX q V).toAlgebra
  have : Algebra.Etale E Γ(S, V) := RingHom.Etale.respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of E)).symm.commRingCatIsoToRingEquiv
    (HasRingHomProperty.appLE @Etale q hq ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top)
  have e := sum_tmul_eq_zero (E := E) u (fun i => resG S hle ((g i).loc c)) fun φ => by
    let z := ofHom hV φ.toRingHom φ.commutes
    have hz : z ∈ ptsIn q τ V := ofHom_mem _ _ _
    have e := congrArg (gv q τ B c (pick hB z) z * ·) (congrFun hu z)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero, Finset.mul_sum] at e
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) e
    rw [mul_left_comm, ← (cval_mem τ (g i)).1 c _ z (ptsIn_mono (hle.trans inf_le_right) hz) (mem_pick hB z)]
    exact congrArg _ ((ev_ofHom hV φ.toRingHom φ.commutes _).symm.trans (ev_res hle hz _))
  have e₂ := congrArg (fun x => ger y hyV (TensorProduct.lid E _ (l.rTensor _ x))) e
  refine ⟨c, hc, ?_⟩
  simp only [map_sum, LinearMap.rTensor_tmul, lid_tmul, Algebra.smul_def, map_mul, map_zero, ger_resG] at e₂
  simp only [map_sum, germ_smul, map_zero]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) e₂
  exact congrArg (· * _) (ger_algX y hyV _).symm

variable (hf : IsFinite q) (he : Etale q) (φ : ∀ τ, Weight q τ B)

open Classical in

def pointHerm : HermFam E (H0 q B ⊤) :=
  letI : ∀ τ, Fintype (CxPts q τ) := fun τ => @Fintype.ofFinite _ (finite_cxPts hf τ)
  ofCoords (P := CxPts q)
    (fun τ => (LinearMap.pi fun y => LinearMap.proj y ∘ₗ LinearMap.proj (pick (φ τ).isLB y)).comp (cval τ))
    (fun τ => Matrix.diagonal fun y => (Real.exp (-(φ τ).φ (pick (φ τ).isLB y) y) : ℝ))
    (fun _ => Matrix.PosDef.diagonal fun _ => Complex.zero_lt_real.2 (Real.exp_pos _))
    fun τ _ _ => linearIndependent_cval he (φ τ).isLB τ

theorem form_pointHerm (τ : E →+* ℂ) [Fintype (CxPts q τ)] (g g' : H0 q B ⊤) :
    (pointHerm hf he φ).form τ g g' = ∑ y, starRingEnd ℂ (cval τ g (pick (φ τ).isLB y) y) *
      cval τ g' (pick (φ τ).isLB y) y * (Real.exp (-(φ τ).φ (pick (φ τ).isLB y) y) : ℝ) := by
  classical
  simp only [pointHerm, ofCoords, dotProduct, Matrix.mulVec_diagonal]
  exact Finset.sum_congr (by congr; exact Subsingleton.elim _ _) fun y _ => by
    rw [mul_comm (Complex.ofReal _), ← mul_assoc]; rfl

theorem csq_pointHerm (τ : E →+* ℂ) {ι : Type*} [Fintype ι] (c : ι → ℂ) (g : ι → H0 q B ⊤) :
    csq (pointHerm hf he φ) τ c g = ∑ᶠ y, (φ τ).nsq (∑ i, c i • cval τ (g i)) y := by
  letI := @Fintype.ofFinite _ (finite_cxPts hf τ)
  rw [finsum_eq_sum_of_fintype, csq, ← Complex.ofReal_re (∑ y, _)]
  simp only [form_pointHerm, Finset.mul_sum, Weight.nsq, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_pow, ← Complex.conj_mul', Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
    Finset.sum_mul]
  refine congrArg _ ?_
  simp only [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv ⟨fun t => (t.2.2, t.2.1, t.1), fun t => (t.2.2, t.2.1, t.1), fun _ => rfl, fun _ => rfl⟩
    _ _ fun t => by simp only [Equiv.coe_fn_mk]; ring


end Points

end GlobalTheory.Vanishing
end
end
