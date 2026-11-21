import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.HermitianLattices.FinalNeighbourConstruct
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountStmt
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegerDenominator

section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.MainNotions.Gaps.CC.Surj

open Formalism.UG Formalism.UG.CS Formalism.UG.P

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  {n : Type} [Fintype n] [DecidableEq n]

theorem coe_algebraMap_int (d : 𝓞 F) :
    ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E) = algebraMap F E (d : F) := rfl

theorem hcompl_norm (σ : E →ₐ[F] E) (hσ : (σ : E →+* E) = starRingEnd E)
    (hfix : ∀ e, σ e = e → ∃ a : F, algebraMap F E a = e) (p : Ideal (𝓞 E)) [hp : p.IsPrime]
    (s : 𝓞 E) (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) p) :
    ∃ (t : 𝓞 E) (d : 𝓞 F), algebraMap (𝓞 F) (𝓞 E) d ∉ p ∧ algebraMap (𝓞 F) (𝓞 E) d = t * s := by
  have hstar : ∀ x : E, σ x = star x := fun x => RingHom.congr_fun hσ x
  induction hs using Submonoid.closure_induction with
  | mem s hs =>
    obtain ⟨hs1, hs2⟩ := hs
    have hint : IsIntegral ℤ (σ (s : E)) := map_isIntegral_int σ s.2
    let t : 𝓞 E := ⟨σ (s : E), hint⟩
    have htp : t ∉ p := hs2 t (hstar _)
    have hinv : σ (σ (s : E) * (s : E)) = σ (s : E) * (s : E) := by
      rw [map_mul, hstar (σ (s : E)), hstar (s : E), star_star, mul_comm]
    obtain ⟨a, ha⟩ := hfix _ hinv
    have haint : IsIntegral ℤ a := by
      rw [← isIntegral_algebraMap_iff (algebraMap F E).injective, ha]
      exact hint.mul s.2
    refine ⟨t, ⟨a, haint⟩, ?_, ?_⟩
    · have e : algebraMap (𝓞 F) (𝓞 E) ⟨a, haint⟩ = t * s := by
        apply RingOfIntegers.ext
        exact ha
      rw [e]
      exact fun h => (hp.mem_or_mem h).elim htp hs1
    · apply RingOfIntegers.ext
      exact ha
  | one => exact ⟨1, 1, by rw [map_one]; exact fun h => hp.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨t, d, h1, h2⟩ := hx
    obtain ⟨t', d', h1', h2'⟩ := hy
    refine ⟨t * t', d * d', ?_, ?_⟩
    · rw [map_mul]
      exact fun h => (hp.mem_or_mem h).elim h1 h1'
    · rw [map_mul, h2, h2']; ring

theorem mem_loc_iff (σ : E →ₐ[F] E) (hσ : (σ : E →+* E) = starRingEnd E)
    (hfix : ∀ e, σ e = e → ∃ a : F, algebraMap F E a = e) (p : Ideal (𝓞 E)) [hp : p.IsPrime]
    (v : Ideal (𝓞 F)) (hv : v = p.comap (algebraMap (𝓞 F) (𝓞 E)))
    (Λ : Submodule (𝓞 E) (n → E)) (x : n → E) :
    x ∈ Formalism.HermitianLatticesTheory.loc (K := E) p Λ ↔ ∃ d : 𝓞 F, d ∉ v ∧ (algebraMap F E (d : F)) • x ∈ Λ := by
  have hstar : ∀ x : E, σ x = star x := fun x => RingHom.congr_fun hσ x
  constructor
  · rintro ⟨s, hs, hx⟩
    obtain ⟨t, d, h1, h2⟩ := hcompl_norm σ hσ hfix p s hs
    refine ⟨d, by rw [hv]; exact h1, ?_⟩
    have : (algebraMap F E (d : F)) • x = t • (s • x) := by
      rw [← coe_algebraMap_int, h2, smul_smul]
      rfl
    rw [this]
    exact Λ.smul_mem t hx
  · rintro ⟨d, hd, hx⟩
    refine ⟨algebraMap (𝓞 F) (𝓞 E) d, Submonoid.subset_closure ⟨by rw [hv] at hd; exact hd, ?_⟩, hx⟩
    intro t ht
    have : t = algebraMap (𝓞 F) (𝓞 E) d := by
      apply RingOfIntegers.ext
      rw [coe_algebraMap_int]
      have h2 : (t : E) = star (algebraMap F E (d : F)) := ht
      rw [h2, ← hstar, AlgHom.commutes]
    rw [this]
    rw [hv] at hd; exact hd

end Loc

section Glue

variable {R : Type} [CommRing R] {I : Type} [Fintype I] {n : Type} [Fintype n] [DecidableEq n]

def glueM (e : I → R) (A : I → Matrix n n R) : Matrix n n R := ∑ i, e i • A i

theorem glueM_mul {e : I → R} (he : OrthogonalIdempotents e) (A B : I → Matrix n n R) :
    glueM e A * glueM e B = glueM e (fun i => A i * B i) := by
  classical
  unfold glueM
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [smul_mul_smul_comm, (he.idem i).eq]
  · intro j _ hj
    rw [smul_mul_smul_comm, he.ortho (Ne.symm hj), zero_smul]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem glueM_const {e : I → R} (he : CompleteOrthogonalIdempotents e) (A : Matrix n n R) :
    glueM e (fun _ => A) = A := by
  unfold glueM
  rw [← Finset.sum_smul, he.complete, one_smul]

theorem smul_glueM {e : I → R} (he : OrthogonalIdempotents e) (A : I → Matrix n n R) (i : I) :
    e i • glueM e A = e i • A i := by
  classical
  unfold glueM
  rw [Finset.smul_sum, Finset.sum_eq_single i]
  · rw [smul_smul, (he.idem i).eq]
  · intro j _ hj
    rw [smul_smul, he.ortho (Ne.symm hj), zero_smul]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem cT_glueM (τ : R →+* R) {e : I → R} (hτ : ∀ i, τ (e i) = e i) (A : I → Matrix n n R) :
    cT τ (glueM e A) = glueM e (fun i => cT τ (A i)) := by
  ext a b
  simp only [cT, glueM, Matrix.transpose_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, map_sum, map_mul, hτ]

def glueGL {e : I → R} (he : CompleteOrthogonalIdempotents e) (A : I → GL n R) : GL n R where
  val := glueM e (fun i => (A i : Matrix n n R))
  inv := glueM e (fun i => ((A i)⁻¹ : GL n R))
  val_inv := by
    rw [glueM_mul he.toOrthogonalIdempotents]
    simp only [Units.mul_inv]
    exact glueM_const he 1
  inv_val := by
    rw [glueM_mul he.toOrthogonalIdempotents]
    simp only [Units.inv_mul]
    exact glueM_const he 1

theorem glueGL_mem_UJ {e : I → R} (he : CompleteOrthogonalIdempotents e) (A : I → GL n R)
    (τ : R →+* R) (hτ : ∀ i, τ (e i) = e i) (J : Matrix n n R) (hA : ∀ i, A i ∈ UJ τ J) :
    glueGL he A ∈ UJ τ J := by
  show cT τ (glueM e (fun i => (A i : Matrix n n R))) * J * glueM e (fun i => (A i : Matrix n n R)) = J
  rw [cT_glueM τ hτ]
  conv_lhs => rw [← glueM_const he J]
  rw [glueM_mul he.toOrthogonalIdempotents, glueM_mul he.toOrthogonalIdempotents]
  have : (fun i => cT τ (A i : Matrix n n R) * J * (A i : Matrix n n R)) = fun _ => J := by
    funext i; exact hA i
  rw [this]
  exact glueM_const he J

end Glue

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

def inclAd : 𝔸 →+* 𝒜 := (Algebra.TensorProduct.includeRight : 𝔸 →ₐ[F] 𝒜).toRingHom


theorem sigR_inclAd (σ : E →ₐ[F] E) (a : 𝔸) : sigR σ 𝔸 (inclAd (E := E) a) = inclAd a := by
  show Algebra.TensorProduct.map σ (AlgHom.id F 𝔸) ((1 : E) ⊗ₜ[F] a) = (1 : E) ⊗ₜ[F] a
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

def Near (a : 𝔸) (Λ : Submodule (𝓞 E) (n → E)) (y : n → E) : Prop :=
  ∃ d : 𝓞 F, ∃ c ∈ intAd F, a = algebraMap F 𝔸 (d : F) * c ∧ (algebraMap F E (d : F)) • y ∈ Λ

theorem near_mem {a : 𝔸} {Λ : Submodule (𝓞 E) (n → E)} {y : n → E} (h : Near a Λ y) :
    inclAd (E := E) a • (fun i => ιA (y i)) ∈ latS (F := F) 𝔸 𝒮 Λ := by
  obtain ⟨d, c, hc, rfl, hy⟩ := h
  have hcS : inclAd (E := E) c ∈ 𝒮 := Subring.subset_closure (Or.inr ⟨⟨c, hc⟩, rfl⟩)
  have e : inclAd (E := E) (algebraMap F 𝔸 (d : F) * c) • (fun i => ιA (y i)) =
      (⟨inclAd (E := E) c, hcS⟩ : 𝒮) • (fun i => ιA (((algebraMap F E (d : F)) • y) i)) := by
    funext i
    show ((1 : E) ⊗ₜ[F] (algebraMap F 𝔸 (d : F) * c)) * ((y i) ⊗ₜ[F] (1 : 𝔸)) =
      ((1 : E) ⊗ₜ[F] c) * ((algebraMap F E (d : F) * y i) ⊗ₜ[F] (1 : 𝔸))
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul,
      mul_one, mul_one, ← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.smul_tmul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hy, rfl⟩)

theorem sum_smul_eq {I : Type} [Fintype I] {e : I → 𝒜} (he : CompleteOrthogonalIdempotents e)
    (u : n → 𝒜) : u = ∑ i, e i • u := by
  rw [← Finset.sum_smul, he.complete, one_smul]

theorem bc_mulVec_incl (γ : GL n E) (x : n → E) :
    ((bc ιA γ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ιA (x i)) =
      fun i => ιA (((γ : Matrix n n E) *ᵥ x) i) := csEquiv_bc_mulVec γ x

theorem glue_globLat (σ : E →ₐ[F] E) (J : Matrix n n E) {I : Type} [Fintype I] (a : I → 𝔸)
    (ha : CompleteOrthogonalIdempotents a) (γ : I → GL n E) (hγ : ∀ i, γ i ∈ UJ (σ : E →+* E) J)
    (L M : Submodule (𝓞 E) (n → E)) (hMfin : Module.Finite (𝓞 E) M)
    (hMspan : Submodule.span E (M : Set (n → E)) = ⊤)
    (H1 : ∀ i, ∀ x ∈ M, Near (a i) L ((((γ i)⁻¹ : GL n E) : Matrix n n E) *ᵥ x))
    (H2 : ∀ i, ∀ l ∈ L, Near (a i) M ((γ i : Matrix n n E) *ᵥ l)) :
    ∃ g ∈ UPts σ J 𝔸, globLat g L = M := by
  have he : CompleteOrthogonalIdempotents (fun i => inclAd (E := E) (a i)) := ha.map inclAd
  refine ⟨glueGL he (fun i => bc ιA (γ i)), ?_, ?_⟩
  · refine glueGL_mem_UJ he _ _ (fun i => sigR_inclAd σ (a i)) _ fun i => ?_
    exact Formalism.UG.Final.RatPtsLe F E n σ J 𝔸 ⟨γ i, hγ i, rfl⟩
  · ext x
    constructor
    · intro hx
      have hx' : glueM (fun i => inclAd (E := E) (a i))
          (fun i => (((bc ιA (γ i))⁻¹ : GL n 𝒜) : Matrix n n 𝒜)) *ᵥ (fun i => ιA (x i)) ∈
          latS (F := F) 𝔸 𝒮 L := hx
      set u := glueM (fun i => inclAd (E := E) (a i))
          (fun i => (((bc ιA (γ i))⁻¹ : GL n 𝒜) : Matrix n n 𝒜)) *ᵥ (fun i => ιA (x i)) with hu
      have hgu : (fun i => ιA (x i)) = glueM (fun i => inclAd (E := E) (a i))
          (fun i => ((bc ιA (γ i) : GL n 𝒜) : Matrix n n 𝒜)) *ᵥ u := by
        rw [hu, Matrix.mulVec_mulVec]
        have := (glueGL he (fun i => bc ιA (γ i))).val_inv
        change glueM _ _ * glueM _ _ = 1 at this
        rw [this, Matrix.one_mulVec]
      have key : ∀ i, ∀ w ∈ latS (F := F) 𝔸 𝒮 L,
          inclAd (E := E) (a i) • (((bc ιA (γ i) : GL n 𝒜) : Matrix n n 𝒜) *ᵥ w) ∈
            latS (F := F) 𝔸 𝒮 M := by
        intro i w hw
        induction hw using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨l, hl, rfl⟩ := hw
          rw [bc_mulVec_incl]
          exact near_mem (H2 i l hl)
        | zero => rw [Matrix.mulVec_zero, smul_zero]; exact zero_mem _
        | add w w' _ _ h h' => rw [Matrix.mulVec_add, smul_add]; exact add_mem h h'
        | smul s w _ h =>
          have : inclAd (E := E) (a i) • (((bc ιA (γ i) : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (s • w)) =
              s • (inclAd (E := E) (a i) • (((bc ιA (γ i) : GL n 𝒜) : Matrix n n 𝒜) *ᵥ w)) := by
            rw [Subring.smul_def, Matrix.mulVec_smul, Subring.smul_def, smul_comm]
          rw [this]
          exact Submodule.smul_mem _ _ h
      have hmem : (fun i => ιA (x i)) ∈ latS (F := F) 𝔸 𝒮 M := by
        rw [sum_smul_eq he (fun i => ιA (x i))]
        refine Submodule.sum_mem _ fun i _ => ?_
        rw [hgu, ← Matrix.smul_mulVec, smul_glueM he.toOrthogonalIdempotents, Matrix.smul_mulVec]
        exact key i u hx'
      have h1 := Formalism.UG.P.global_lattice_one_holds F E n M hMfin hMspan
      rw [← h1]
      show (((1 : GL n 𝒜)⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ιA (x i)) ∈ latS (F := F) 𝔸 𝒮 M
      rw [inv_one, Units.val_one, Matrix.one_mulVec]
      exact hmem
    · intro hx
      show glueM (fun i => inclAd (E := E) (a i))
          (fun i => (((bc ιA (γ i))⁻¹ : GL n 𝒜) : Matrix n n 𝒜)) *ᵥ (fun i => ιA (x i)) ∈
          latS (F := F) 𝔸 𝒮 L
      rw [sum_smul_eq he (glueM _ _ *ᵥ _)]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [← Matrix.smul_mulVec, smul_glueM he.toOrthogonalIdempotents, Matrix.smul_mulVec, ← map_inv,
        bc_mulVec_incl]
      exact near_mem (H1 i x hx)

end Main

section Ind

variable {F : Type} [Field F] [NumberField F]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

open Classical in

def indA (T : Set (HeightOneSpectrum (𝓞 F))) : 𝔸 :=
  ⟨fun w => if w ∈ T then 1 else 0, Filter.Eventually.of_forall fun w => by
    dsimp only
    split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

theorem indA_mem {T : Set (HeightOneSpectrum (𝓞 F))} {w : HeightOneSpectrum (𝓞 F)} (h : w ∈ T) :
    indA T w = 1 := by
  classical
  exact if_pos h

theorem indA_notMem {T : Set (HeightOneSpectrum (𝓞 F))} {w : HeightOneSpectrum (𝓞 F)} (h : w ∉ T) :
    indA T w = 0 := by
  classical
  exact if_neg h

theorem indA_complete {I : Type} [Fintype I] (T : I → Set (HeightOneSpectrum (𝓞 F)))
    (hT : ∀ w, ∃! i, w ∈ T i) : CompleteOrthogonalIdempotents (fun i => indA (T i)) := by
  classical
  rw [CompleteOrthogonalIdempotents.iff_ortho_complete]
  constructor
  · intro i j hij
    refine DFunLike.ext _ _ fun w => ?_
    show indA (T i) w * indA (T j) w = 0
    by_cases h : w ∈ T i
    · have : w ∉ T j := fun h' => hij ((hT w).unique h h')
      rw [indA_notMem this, mul_zero]
    · rw [indA_notMem h, zero_mul]
  · refine DFunLike.ext _ _ fun w => ?_
    have e : (∑ i, indA (T i)) w = ∑ i, indA (T i) w := map_sum (evalV F w) _ _
    show (∑ i, indA (T i)) w = 1
    obtain ⟨i0, h0, hu⟩ := hT w
    rw [e, Finset.sum_eq_single i0, indA_mem h0]
    · intro j _ hj
      exact indA_notMem fun h => hj (hu j h)
    · intro h; exact absurd (Finset.mem_univ i0) h

theorem indA_div (T : Set (HeightOneSpectrum (𝓞 F))) (d : 𝓞 F) (hd : ∀ w ∈ T, d ∉ w.asIdeal) :
    ∃ c ∈ intAd F, indA T = algebraMap F 𝔸 (d : F) * c := by
  classical
  have hint : ∀ w : HeightOneSpectrum (𝓞 F),
      (if w ∈ T then (algebraMap F (w.adicCompletion F) (d : F))⁻¹ else 0) ∈
        w.adicCompletionIntegers F := by
    intro w
    split_ifs with h
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, levelaf_valued_algebraMap,
        show ((d : F)) = algebraMap (𝓞 F) F d from rfl,
        (HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 (hd w h), inv_one]
    · exact zero_mem _
  refine ⟨⟨fun w => if w ∈ T then (algebraMap F (w.adicCompletion F) (d : F))⁻¹ else 0,
    Filter.Eventually.of_forall hint⟩, hint, ?_⟩
  refine DFunLike.ext _ _ fun w => ?_
  show indA T w = algebraMap F (w.adicCompletion F) (d : F) *
    (if w ∈ T then (algebraMap F (w.adicCompletion F) (d : F))⁻¹ else 0)
  by_cases h : w ∈ T
  · rw [indA_mem h, if_pos h, mul_inv_cancel₀]
    have hd0 : d ≠ 0 := fun h0 => hd w h (h0 ▸ zero_mem _)
    exact levelaf_algebraMap_ne_zero w d hd0
  · rw [indA_notMem h, if_neg h, mul_zero]

end Ind

section Denom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

theorem algebraMap_coe_mul (a b : 𝓞 F) :
    algebraMap F E ((a * b : 𝓞 F) : F) = algebraMap F E (a : F) * algebraMap F E (b : F) := by
  rw [← map_mul]; rfl

theorem smul_int_mem (L : Submodule (𝓞 E) (n → E)) (d : 𝓞 F) {x : n → E} (hx : x ∈ L) :
    (algebraMap F E (d : F)) • x ∈ L := L.smul_mem (algebraMap (𝓞 F) (𝓞 E) d) hx

theorem exists_denom_pt (L : Submodule (𝓞 E) (n → E))
    (hL : Submodule.span E (L : Set (n → E)) = ⊤) (x : n → E) :
    ∃ D : 𝓞 F, D ≠ 0 ∧ (algebraMap F E (D : F)) • x ∈ L :=
  _root_.UpperTheory.Reformulated.B.IntegerDenominator.exists_denom_pt L hL x

theorem exists_denom (L M : Submodule (𝓞 E) (n → E))
    (hL : Submodule.span E (L : Set (n → E)) = ⊤) (hM : M.FG) :
    ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ x ∈ M, (algebraMap F E (D : F)) • x ∈ L := by
  classical
  obtain ⟨S, rfl⟩ := hM
  choose D hD0 hD using exists_denom_pt (F := F) L hL
  refine ⟨∏ s ∈ S, D s, Finset.prod_ne_zero_iff.2 fun s _ => hD0 s, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    have hx' : x ∈ S := hx
    rw [← Finset.mul_prod_erase S D hx', mul_comm, algebraMap_coe_mul, ← smul_smul]
    exact smul_int_mem L _ (hD x)
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ h h' => rw [smul_add]; exact add_mem h h'
  | smul a x _ h =>
    rw [smul_comm]
    exact L.smul_mem a h

end Denom

section Surj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

theorem finite_places_of_mem (D : 𝓞 F) (hD : D ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | D ∈ v.asIdeal}.Finite := by
  have := Ideal.finite_factors (I := Ideal.span {D}) (by simpa using hD)
  simpa only [Ideal.dvd_span_singleton] using this

theorem exists_prime_over (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : Ideal (𝓞 E), p.IsMaximal ∧ v.asIdeal = p.comap (algebraMap (𝓞 F) (𝓞 E)) := by
  have hv : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) v.asIdeal (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
    exact bot_le)
  exact ⟨Q, hQ, hQv.symm⟩

theorem genus_local (σ : E →ₐ[F] E) (hσ : (σ : E →+* E) = starRingEnd E)
    (hfix : ∀ e, σ e = e → ∃ a : F, algebraMap F E a = e)
    (h : (n → E) →ₗ⋆[E] (n → E) →ₗ[E] E) (L M : Submodule (𝓞 E) (n → E))
    (hgen : Formalism.HermitianLatticesTheory.SameGenus h L M) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ γ : GL n E, γ ∈ UJ (σ : E →+* E) (gram h) ∧
      (∀ x ∈ M, ∃ d : 𝓞 F, d ∉ v.asIdeal ∧
        (algebraMap F E (d : F)) • (((γ⁻¹ : GL n E) : Matrix n n E) *ᵥ x) ∈ L) ∧
      (∀ l ∈ L, ∃ d : 𝓞 F, d ∉ v.asIdeal ∧
        (algebraMap F E (d : F)) • ((γ : Matrix n n E) *ᵥ l) ∈ M) := by
  obtain ⟨p, hp, hpv⟩ := exists_prime_over (E := E) v
  have hpp : p.IsPrime := hp.isPrime
  obtain ⟨u, hu, hLM⟩ := hgen p hp
  obtain ⟨γ, rfl⟩ := Formalism.UG.Final.HermBridgeSurj E n h u hu
  have hle : ∀ (N : Submodule (𝓞 E) (n → E)), ∀ x ∈ N, x ∈ Formalism.HermitianLatticesTheory.loc (K := E) p N := by
    intro N x hx
    rw [mem_loc_iff σ hσ hfix p v.asIdeal hpv]
    refine ⟨1, fun h1 => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), ?_⟩
    simpa using hx
  refine ⟨γ, ?_, ?_, ?_⟩
  · rw [hσ]
    exact (Formalism.UG.Final.HermBridge E n h γ).2 hu
  · intro x hx
    have hx' := hle M x hx
    rw [← hLM] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    have hyx' : (γ : Matrix n n E) *ᵥ y = x := by
      rw [← Formalism.UG.Final.GlEquivApply E n γ y]; exact hyx
    rw [← hyx', Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact (mem_loc_iff σ hσ hfix p v.asIdeal hpv L y).1 hy
  · intro l hl
    have : (γ : Matrix n n E) *ᵥ l ∈ Formalism.HermitianLatticesTheory.loc (K := E) p M := by
      rw [← hLM, ← Formalism.UG.Final.GlEquivApply E n γ l]
      exact ⟨l, hle L l hl, rfl⟩
    exact (mem_loc_iff σ hσ hfix p v.asIdeal hpv M _).1 this

theorem genus_surj (σ : E →ₐ[F] E) (hσ : (σ : E →+* E) = starRingEnd E)
    (hfix : ∀ e, σ e = e → ∃ a : F, algebraMap F E a = e)
    (h : (n → E) →ₗ⋆[E] (n → E) →ₗ[E] E) (L M : Submodule (𝓞 E) (n → E))
    (hLfin : Module.Finite (𝓞 E) L) (hLspan : Submodule.span E (L : Set (n → E)) = ⊤)
    (hM : M ∈ Formalism.HermitianLatticesTheory.genus h L) :
    ∃ g ∈ UPts σ (gram h) 𝔸, globLat g L = M := by
  classical
  obtain ⟨hMlat, hgen⟩ := hM
  have hMfg : M.FG := hMlat.fg
  have hMspan : Submodule.span E (M : Set (n → E)) = ⊤ := hMlat.span_eq_top
  obtain ⟨D1, hD1, h1⟩ := exists_denom (F := F) L M hLspan hMfg
  obtain ⟨D2, hD2, h2⟩ := exists_denom (F := F) M L hMspan (Module.Finite.iff_fg.1 hLfin)
  have hD : D1 * D2 ≠ 0 := mul_ne_zero hD1 hD2
  set S : Finset (HeightOneSpectrum (𝓞 F)) := (finite_places_of_mem (D1 * D2) hD).toFinset with hS
  have hSmem : ∀ w, w ∉ S → D1 * D2 ∉ w.asIdeal := by
    intro w hw hmem
    exact hw ((Set.Finite.mem_toFinset _).2 hmem)
  choose γ hγU hγ1 hγ2 using genus_local σ hσ hfix h L M hgen
  let T : Option S → Set (HeightOneSpectrum (𝓞 F)) := fun i => i.elim {w | w ∉ S} (fun v => {v.1})
  let γ' : Option S → GL n E := fun i => i.elim 1 (fun v => γ v.1)
  have hT : ∀ w, ∃! i, w ∈ T i := by
    intro w
    by_cases hw : w ∈ S
    · refine ⟨some ⟨w, hw⟩, rfl, ?_⟩
      rintro (_ | ⟨v, hv⟩) hi
      · exact absurd hw hi
      · have : w = v := hi
        subst this; rfl
    · refine ⟨none, hw, ?_⟩
      rintro (_ | ⟨v, hv⟩) hi
      · rfl
      · have : w = v := hi
        subst this; exact absurd hv hw
  refine glue_globLat σ (gram h) (fun i => indA (T i)) (indA_complete T hT) γ' ?_ L M
    (Module.Finite.iff_fg.2 hMfg) hMspan ?_ ?_
  · rintro (_ | v)
    · exact one_mem _
    · exact hγU v.1
  · rintro (_ | v) x hx
    · obtain ⟨c, hc, hc'⟩ := indA_div (T none) (D1 * D2) hSmem
      refine ⟨D1 * D2, c, hc, hc', ?_⟩
      show (algebraMap F E ((D1 * D2 : 𝓞 F) : F)) • ((((1 : GL n E)⁻¹ : GL n E) : Matrix n n E) *ᵥ x) ∈ L
      rw [inv_one, Units.val_one, Matrix.one_mulVec, mul_comm, algebraMap_coe_mul, ← smul_smul]
      exact smul_int_mem L D2 (h1 x hx)
    · obtain ⟨d, hd, hdx⟩ := hγ1 v.1 x hx
      obtain ⟨c, hc, hc'⟩ := indA_div (T (some v)) d (by
        intro w hw
        have : w = v.1 := hw
        rw [this]; exact hd)
      exact ⟨d, c, hc, hc', hdx⟩
  · rintro (_ | v) l hl
    · obtain ⟨c, hc, hc'⟩ := indA_div (T none) (D1 * D2) hSmem
      refine ⟨D1 * D2, c, hc, hc', ?_⟩
      show (algebraMap F E ((D1 * D2 : 𝓞 F) : F)) • (((1 : GL n E) : Matrix n n E) *ᵥ l) ∈ M
      rw [Units.val_one, Matrix.one_mulVec, algebraMap_coe_mul, ← smul_smul]
      exact smul_int_mem M D1 (h2 l hl)
    · obtain ⟨d, hd, hdx⟩ := hγ2 v.1 l hl
      obtain ⟨c, hc, hc'⟩ := indA_div (T (some v)) d (by
        intro w hw
        have : w = v.1 := hw
        rw [this]; exact hd)
      exact ⟨d, c, hc, hc', hdx⟩

end Surj

section Std

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  {k : ℕ}

theorem gram_stdForm : gram (Formalism.MainNotions.StandardLattice.stdForm E k) = 1 := by
  ext i j
  show ∑ a, star ((Pi.single i 1 : Fin k → E) a) * (Pi.single j 1 : Fin k → E) a = _
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, star_one, one_mul, Matrix.one_apply, Pi.single_apply]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, star_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem stdLat_fg : (Formalism.MainNotions.StandardLattice.stdLat E k).FG := Submodule.fg_span (Set.finite_range _)

theorem stdLat_finite : Module.Finite (𝓞 E) (Formalism.MainNotions.StandardLattice.stdLat E k) := Module.Finite.iff_fg.2 stdLat_fg

theorem stdLat_span : Submodule.span E ((Formalism.MainNotions.StandardLattice.stdLat E k : Submodule (𝓞 E) (Fin k → E)) :
    Set (Fin k → E)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun E (Fin k)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact Submodule.subset_span ⟨i, by simp⟩

theorem sig_eq_star (σ : E →ₐ[F] E) (hσ : ∀ e, σ e = star e) : (σ : E →+* E) = starRingEnd E :=
  RingHom.ext hσ

theorem genusSurj (σ : E →ₐ[F] E) (hσ : ∀ e, σ e = star e)
    (hfix : ∀ e, σ e = e → ∃ a : F, algebraMap F E a = e) :
    GenusSurj σ (1 : Matrix (Fin k) (Fin k) E) := by
  intro M hM
  have := genus_surj σ (sig_eq_star σ hσ) hfix (Formalism.MainNotions.StandardLattice.stdForm E k) (Formalism.MainNotions.StandardLattice.stdLat E k) M
    stdLat_finite stdLat_span hM
  rwa [gram_stdForm] at this

end Std

end Formalism.MainNotions.Gaps.CC.Surj
end
end

section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.MainNotions.Gaps.CC.Surj

open Formalism.UG

def WACore : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E),
    (∀ e, σ (σ e) = e) → (∃ θ, σ θ ≠ θ) → IsHerm (σ : E →+* E) J → IsUnit J.det →
    ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ g ∈ UPts σ J (v.adicCompletion F), ∀ D : 𝓞 F, D ≠ 0 →
    ∃ γ ∈ UJ (σ : E →+* E) J, ∀ i j,
      ∃ s ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring,
        (g : Matrix n n (E ⊗[F] v.adicCompletion F)) i j -
            inclE (F := F) (v.adicCompletion F) ((γ : Matrix n n E) i j) =
          inclE (F := F) (v.adicCompletion F) (algebraMap F E (D : F)) * s

def WeakApprox1 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E),
    (∀ e, σ (σ e) = e) → (∃ θ, σ θ ≠ θ) → IsHerm (σ : E →+* E) J → IsUnit J.det →
    ∀ (Λ : Submodule (𝓞 E) (n → E)), Module.Finite (𝓞 E) Λ →
    Submodule.span E (Λ : Set (n → E)) = ⊤ → ∀ (v : HeightOneSpectrum (𝓞 F)),
    ∀ g ∈ UPts σ J (v.adicCompletion F), ∃ γ ∈ UJ (σ : E →+* E) J,
      (bc (inclE (F := F) (v.adicCompletion F)) γ)⁻¹ * g ∈
        stabGL (latS (F := F) (v.adicCompletion F)
          (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ)

section Abs

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def walInt (S : Subring A) (M : Matrix n n A) : Prop := ∀ i j, M i j ∈ S

omit [DecidableEq n] in
theorem walInt_mul (S : Subring A) {M N : Matrix n n A} (hM : walInt S M) (hN : walInt S N) :
    walInt S (M * N) := fun i j => by
  rw [Matrix.mul_apply]; exact Subring.sum_mem _ fun k _ => mul_mem (hM i k) (hN k j)

omit [Fintype n] [DecidableEq n] in
theorem walInt_smul (S : Subring A) {c : A} (hc : c ∈ S) {M : Matrix n n A} (hM : walInt S M) :
    walInt S (c • M) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem hc (hM i j)

omit [Fintype n] [DecidableEq n] in
theorem walInt_sub (S : Subring A) {M N : Matrix n n A} (hM : walInt S M) (hN : walInt S N) :
    walInt S (M - N) := fun i j => by
  rw [Matrix.sub_apply]; exact sub_mem (hM i j) (hN i j)

omit [Fintype n] [DecidableEq n] in
theorem walInt_neg (S : Subring A) {M : Matrix n n A} (hM : walInt S M) :
    walInt S (-M) := fun i j => by
  rw [Matrix.neg_apply]; exact neg_mem (hM i j)

omit [Fintype n] [DecidableEq n] in
theorem walInt_cT (S : Subring A) (τ : A →+* A) (hτ : ∀ s ∈ S, τ s ∈ S) {M : Matrix n n A}
    (hM : walInt S M) : walInt S (cT τ M) := fun i j => hτ _ (hM j i)

omit [Fintype n] [DecidableEq n] in
theorem wal_cT_sub (τ : A →+* A) (M N : Matrix n n A) : cT τ (M - N) = cT τ M - cT τ N := by
  ext i j; simp [cT]

omit [Fintype n] [DecidableEq n] in
theorem wal_cT_smul (τ : A →+* A) (c : A) (M : Matrix n n A) : cT τ (c • M) = τ c • cT τ M := by
  ext i j; simp [cT]

theorem wal_inv_eq (τ : A →+* A) (J Ji : Matrix n n A) (hJi : Ji * J = 1) (u : GL n A)
    (hu : u ∈ UJ τ J) :
    ((u⁻¹ : GL n A) : Matrix n n A) = Ji * cT τ (u : Matrix n n A) * J := by
  have h : cT τ (u : Matrix n n A) * J * (u : Matrix n n A) = J := hu
  have h2 : Ji * cT τ (u : Matrix n n A) * J * (u : Matrix n n A) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT τ _), h, hJi]
  calc ((u⁻¹ : GL n A) : Matrix n n A) = 1 * ((u⁻¹ : GL n A) : Matrix n n A) := (Matrix.one_mul _).symm
    _ = Ji * cT τ (u : Matrix n n A) * J * (u : Matrix n n A) * ((u⁻¹ : GL n A) : Matrix n n A) := by
        rw [h2]
    _ = Ji * cT τ (u : Matrix n n A) * J := by
        rw [Matrix.mul_assoc _ (u : Matrix n n A), Units.mul_inv, Matrix.mul_one]

theorem wal_abs (S : Subring A) (τ : A →+* A) (hτ : ∀ s ∈ S, τ s ∈ S) (J Ji : Matrix n n A)
    (hJi : Ji * J = 1) (L : Submodule S (n → A)) (δ c : A) (hδ : δ ∈ S) (hc : c ∈ S)
    (hτδ : τ δ = δ) (hτc : τ c = c)
    (hL : ∀ N : Matrix n n A, walInt S N → ∀ x ∈ L, (δ • N) *ᵥ x ∈ L)
    (g γ : GL n A) (hg : g ∈ UJ τ J) (hγ : γ ∈ UJ τ J)
    (hgi : walInt S (c • ((g⁻¹ : GL n A) : Matrix n n A))) (hJ : walInt S (c • J))
    (hJi' : walInt S (c • Ji)) (T : Matrix n n A) (hT : walInt S T)
    (hD : (g : Matrix n n A) - (γ : Matrix n n A) = (c * c * δ) • T) :
    γ⁻¹ * g ∈ stabGL L := by
  set G : Matrix n n A := (g : Matrix n n A) with hG
  set Γ : Matrix n n A := (γ : Matrix n n A) with hΓ
  set Gi : Matrix n n A := ((g⁻¹ : GL n A) : Matrix n n A) with hGi
  set Γi : Matrix n n A := ((γ⁻¹ : GL n A) : Matrix n n A) with hΓi
  have e1 : Gi * (G - Γ) = δ • (c • ((c • Gi) * T)) := by
    rw [hD]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    congr 1; ring
  have e2 : Γi = Gi - Ji * cT τ (G - Γ) * J := by
    rw [hΓi, hGi, wal_inv_eq τ J Ji hJi γ hγ, wal_inv_eq τ J Ji hJi g hg, wal_cT_sub, Matrix.mul_sub,
      Matrix.sub_mul, sub_sub_cancel]
  have e3 : Ji * cT τ (G - Γ) * J * (G - Γ) =
      δ • ((c * c * δ) • ((c • Ji) * cT τ T * (c • J) * T)) := by
    rw [hD, wal_cT_smul, map_mul, map_mul, hτc, hτδ]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    congr 1; ring
  have i1 : walInt S (c • ((c • Gi) * T)) := walInt_smul S hc (walInt_mul S hgi hT)
  have i3 : walInt S ((c * c * δ) • ((c • Ji) * cT τ T * (c • J) * T)) :=
    walInt_smul S (mul_mem (mul_mem hc hc) hδ)
      (walInt_mul S (walInt_mul S (walInt_mul S hJi' (walInt_cT S τ hτ hT)) hJ) hT)
  have hΓΓ : Γi * Γ = 1 := Units.inv_mul γ
  have hGG : Gi * G = 1 := Units.inv_mul g
  have hk : Γi * G = 1 + δ • (c • ((c • Gi) * T) -
      (c * c * δ) • ((c • Ji) * cT τ T * (c • J) * T)) := by
    have : Γi * G = 1 + Γi * (G - Γ) := by rw [Matrix.mul_sub, hΓΓ]; abel
    rw [this, e2, Matrix.sub_mul, e1, e3, smul_sub]
  have hki : Gi * Γ = 1 + δ • (-(c • ((c • Gi) * T))) := by
    have : Gi * Γ = 1 - Gi * (G - Γ) := by rw [Matrix.mul_sub, hGG]; abel
    rw [this, e1, smul_neg, sub_eq_add_neg]
  have hkk : Gi * Γ * (Γi * G) = 1 := by
    have h1 : Γ * Γi = 1 := Units.mul_inv γ
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Γ, h1, Matrix.one_mul, hGG]
  intro x
  rw [Units.val_mul]
  constructor
  · intro hx
    rw [hk, Matrix.add_mulVec, Matrix.one_mulVec]
    exact add_mem hx (hL _ (walInt_sub S i1 i3) x hx)
  · intro hx
    have : x = (Gi * Γ) *ᵥ ((Γi * G) *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, hkk, Matrix.one_mulVec]
    rw [this, hki, Matrix.add_mulVec, Matrix.one_mulVec]
    exact add_mem hx (hL _ (walInt_neg S i1) _ hx)

end Abs

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : Type} [Fintype n] [DecidableEq n]

local notation "Av" => E ⊗[F] v.adicCompletion F
local notation "Sv" => Formalism.UG.P.lvS F E v
local notation "ιv" => inclE (F := F) (E := E) (v.adicCompletion F)

theorem wal_incl_int (e : E) (he : IsIntegral ℤ e) : ιv e ∈ Sv :=
  Subring.subset_closure (Or.inl ⟨⟨e, ⟨⟨e, he⟩, rfl⟩⟩, rfl⟩)

theorem wal_sig_mem (σ : E →ₐ[F] E) {s : Av} (hs : s ∈ Sv) :
    sigR σ (v.adicCompletion F) s ∈ Sv := by
  refine Subring.closure_induction (p := fun s _ => sigR σ (v.adicCompletion F) s ∈ Sv)
    ?_ ?_ ?_ ?_ ?_ ?_ hs
  · rintro x (⟨⟨e, ⟨b, rfl⟩⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · have h1 : sigR σ (v.adicCompletion F) (algebraMap (𝓞 E) E b ⊗ₜ[F] (1 : v.adicCompletion F)) =
          ιv ((σ : E →+* E) (algebraMap (𝓞 E) E b)) := by
        simp [sigR, inclE, Algebra.TensorProduct.includeLeftRingHom_apply]
      show sigR σ _ (algebraMap (𝓞 E) E b ⊗ₜ[F] (1 : v.adicCompletion F)) ∈ Sv
      rw [h1]
      exact wal_incl_int v _ ((RingOfIntegers.isIntegral_coe b).map ((σ : E →+* E).toIntAlgHom))
    · have h1 : sigR σ (v.adicCompletion F) ((1 : E) ⊗ₜ[F] y) = (1 : E) ⊗ₜ[F] y := by
        simp [sigR]
      show sigR σ _ ((1 : E) ⊗ₜ[F] y) ∈ Sv
      rw [h1]
      exact Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  · rw [map_zero]; exact zero_mem _
  · rw [map_one]; exact one_mem _
  · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
  · intro x _ hx; rw [map_neg]; exact neg_mem hx
  · intro x y _ _ hx hy; rw [map_mul]; exact mul_mem hx hy

theorem wal_upper (Λ : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ x ∈ latS (F := F) (v.adicCompletion F) Sv Λ, ∀ i, (m : Av) * x i ∈ Sv := by
  classical
  obtain ⟨s, hs⟩ : Λ.FG := Module.Finite.iff_fg.mp hfin
  obtain ⟨m, hm0, hm⟩ := Formalism.UG.P.adelstabL_den (fun p : s × n => (p.1 : n → E) p.2)
  have hΛ : ∀ x ∈ Λ, ∀ k, IsIntegral ℤ ((m : E) * x k) := by
    intro x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => intro k; exact hm (⟨x, hx⟩, k)
    | zero => intro k; simp [isIntegral_zero]
    | add x y _ _ hx hy => intro k; simpa [mul_add] using (hx k).add (hy k)
    | smul r x _ hx =>
      intro k
      have : (m : E) * (r • x) k = algebraMap (𝓞 E) E r * ((m : E) * x k) := by
        simp [Algebra.smul_def]; ring
      rw [this]
      exact (RingOfIntegers.isIntegral_coe r).mul (hx k)
  refine ⟨m, hm0, fun x hx => ?_⟩
  have hC : (m : Av) = ιv (m : E) := (map_intCast _ m).symm
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    intro i
    rw [hC, ← map_mul]
    exact wal_incl_int v _ (hΛ y hy i)
  | zero => intro i; simp
  | add x w _ _ hx hw => intro i; rw [Pi.add_apply, mul_add]; exact add_mem (hx i) (hw i)
  | smul s x _ hx =>
    intro i
    rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, mul_left_comm]
    exact mul_mem s.2 (hx i)

theorem wal_lower (Λ : Submodule (𝓞 E) (n → E))
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ x : n → Av, (∀ i, x i ∈ Sv) →
      (fun i => (m : Av) * x i) ∈ latS (F := F) (v.adicCompletion F) Sv Λ := by
  classical
  have hk : ∀ k : n, ∃ N : ℕ, ∃ f : Fin N → E, ∃ w : Fin N → Λ,
      ∑ j, f j • (w j : n → E) = Pi.single k 1 := by
    intro k
    have : (Pi.single k 1 : n → E) ∈ Submodule.span E (Λ : Set (n → E)) := by
      rw [hspan]; exact Submodule.mem_top
    obtain ⟨N, f, w, h⟩ := Submodule.mem_span_set'.1 this
    exact ⟨N, f, fun j => ⟨w j, (w j).2⟩, h⟩
  choose N f w hw using hk
  obtain ⟨m, hm0, hm⟩ := Formalism.UG.P.adelstabL_den (fun p : Σ k : n, Fin (N k) => f p.1 p.2)
  have hsingle : ∀ k, (Pi.single k (m : E) : n → E) ∈ Λ := by
    intro k
    have : (Pi.single k (m : E) : n → E) =
        ∑ j, (⟨(m : E) * f k j, hm ⟨k, j⟩⟩ : 𝓞 E) • (w k j : n → E) := by
      have h1 : (Pi.single k (m : E) : n → E) = (m : E) • (Pi.single k 1 : n → E) := by
        rw [← Pi.single_smul', smul_eq_mul, mul_one]
      rw [h1, ← hw k, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← algebraMap_smul E, smul_smul]
      rfl
    rw [this]
    exact sum_mem fun j _ => Λ.smul_mem _ (w k j).2
  refine ⟨m, hm0, fun x hx => ?_⟩
  have hC : (m : Av) = ιv (m : E) := (map_intCast _ m).symm
  have : (fun i => (m : Av) * x i) =
      ∑ k, (⟨x k, hx k⟩ : Sv) • (fun i => ιv ((Pi.single k (m : E) : n → E) i)) := by
    ext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · show _ = (_ : Sv) • ιv ((Pi.single i (m : E) : n → E) i)
      rw [Pi.single_eq_same, Subring.smul_def, smul_eq_mul, ← hC, mul_comm]
    · intro k _ hki
      show (_ : Sv) • ιv ((Pi.single k (m : E) : n → E) i) = 0
      rw [Pi.single_apply, if_neg (Ne.symm hki), map_zero, smul_zero]
    · exact fun h => absurd (Finset.mem_univ i) h
  rw [this]
  exact sum_mem fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hsingle k, rfl⟩)

theorem wal_delta (Λ : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ N : Matrix n n Av, walInt Sv N →
      ∀ x ∈ latS (F := F) (v.adicCompletion F) Sv Λ,
        ((m : Av) • N) *ᵥ x ∈ latS (F := F) (v.adicCompletion F) Sv Λ := by
  obtain ⟨m₁, h₁, hu⟩ := wal_upper v Λ hfin
  obtain ⟨m₂, h₂, hl⟩ := wal_lower v Λ hspan
  refine ⟨m₂ * m₁, mul_ne_zero h₂ h₁, fun N hN x hx => ?_⟩
  have : (((m₂ * m₁ : ℤ) : Av) • N) *ᵥ x =
      fun i => (m₂ : Av) * ∑ j, N i j * ((m₁ : Av) * x j) := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
      Int.cast_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [this]
  exact hl _ fun i => Subring.sum_mem _ fun j _ => mul_mem (hN i j) (hu x hx j)

end Loc

theorem wal_main (h : WACore) : WeakApprox1 := by
  intro F E _ _ _ _ _ n _ _ σ J hσ hθ hherm hdet Λ hfin hspan v g hg
  classical
  obtain ⟨m, hm0, hL⟩ := wal_delta (F := F) v Λ hfin hspan
  set ι := inclE (F := F) (E := E) (v.adicCompletion F) with hι
  set Ji : Matrix n n (E ⊗[F] v.adicCompletion F) := (J⁻¹).map ι with hJidef
  obtain ⟨N, hN0, hN⟩ := Formalism.UG.P.levelv_denom_family (F := F) (E := E) v
    (Sum.elim (fun p : n × n =>
        ((g⁻¹ : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) p.1 p.2)
      (Sum.elim (fun p : n × n => (J.map ι) p.1 p.2) (fun p : n × n => Ji p.1 p.2)))
  have hD0 : (((N : ℤ) * (N : ℤ) * m : ℤ) : 𝓞 F) ≠ 0 :=
    Int.cast_ne_zero.2 (mul_ne_zero (mul_ne_zero (by exact_mod_cast hN0) (by exact_mod_cast hN0)) hm0)
  obtain ⟨γ, hγ, hs⟩ := h F E n σ J hσ hθ hherm hdet v g hg _ hD0
  choose T hT hTe using hs
  refine ⟨γ, hγ, ?_⟩
  have hγ' : bc ι γ ∈ UJ (sigR σ (v.adicCompletion F)) (J.map ι) :=
    Formalism.UG.Final.RatPtsLe F E n σ J (v.adicCompletion F) (Subgroup.mem_map_of_mem _ hγ)
  have hJi : Ji * J.map ι = 1 := by
    rw [hJidef, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet,
      Matrix.map_one ι (map_zero ι) (map_one ι)]
  have hcS : ((N : ℕ) : E ⊗[F] v.adicCompletion F) ∈ tensInt (F := F) (v.adicCompletion F) (intOE E)
      (v.adicCompletionIntegers F).toSubring := natCast_mem _ N
  have hmS : ((m : ℤ) : E ⊗[F] v.adicCompletion F) ∈ tensInt (F := F) (v.adicCompletion F) (intOE E)
      (v.adicCompletionIntegers F).toSubring := intCast_mem _ m
  refine wal_abs _ (sigR σ (v.adicCompletion F)) (fun s hs => wal_sig_mem v σ hs) (J.map ι) Ji hJi _
    (m : E ⊗[F] v.adicCompletion F) (N : E ⊗[F] v.adicCompletion F) hmS hcS (map_intCast _ m)
    (map_natCast _ N) hL g (bc ι γ) hg hγ' ?_ ?_ ?_ (Matrix.of T) (fun i j => hT i j) ?_
  · intro i j
    have := hN (Sum.inl (i, j))
    rw [nsmul_eq_mul] at this
    exact this
  · intro i j
    have := hN (Sum.inr (Sum.inl (i, j)))
    rw [nsmul_eq_mul] at this
    exact this
  · intro i j
    have := hN (Sum.inr (Sum.inr (i, j)))
    rw [nsmul_eq_mul] at this
    exact this
  · ext i j
    have h1 := hTe i j
    have h2 : ι (algebraMap F E ((((N : ℤ) * (N : ℤ) * m : ℤ) : 𝓞 F) : F)) =
        (N : E ⊗[F] v.adicCompletion F) * (N : E ⊗[F] v.adicCompletion F) *
          (m : E ⊗[F] v.adicCompletion F) := by
      simp
    rw [h2] at h1
    rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, ← h1]
    rfl

end Formalism.MainNotions.Gaps.CC.Surj
end
end

section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace Formalism.MainNotions.Gaps.CC.Surj

open Formalism.UG Formalism.UG.CS Formalism.UG.P

section Conv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
local notation "Sv[" v "]" => tensInt (F := F) (adicCompletion F v) (intOE E)
  (ValuationSubring.toSubring (adicCompletionIntegers F v))
local notation "ιv[" v "]" => inclE (F := F) (E := E) (adicCompletion F v)

theorem conv_eps_tmul (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    afsplitEps E v * ιA e = e ⊗ₜ[F] afsplitI v (1 : v.adicCompletion F) := by
  rw [afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul]
  show ((1 : E) ⊗ₜ[F] afsplitI v (1 : v.adicCompletion F)) * (e ⊗ₜ[F] (1 : 𝔸)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem conv_tmul_smul (a : F) (e : E) (c : 𝔸) :
    e ⊗ₜ[F] (a • c) = ((1 : E) ⊗ₜ[F] c) * ιA (algebraMap F E a * e) := by
  show _ = ((1 : E) ⊗ₜ[F] c) * ((algebraMap F E a * e) ⊗ₜ[F] (1 : 𝔸))
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul', Algebra.smul_def]

theorem conv_one_tmul_mem {c : 𝔸} (hc : c ∈ intAd F) : (1 : E) ⊗ₜ[F] c ∈ 𝒮 :=
  Subring.subset_closure (Or.inr ⟨⟨c, hc⟩, rfl⟩)

theorem conv_tmul_mem (Λ : Submodule (𝓞 E) (n → E)) (y : n → E) (a : F) {c : 𝔸}
    (hc : c ∈ intAd F) (hy : (algebraMap F E a) • y ∈ Λ) :
    (fun i => y i ⊗ₜ[F] (a • c)) ∈ latS (F := F) 𝔸 𝒮 Λ := by
  have : (fun i => y i ⊗ₜ[F] (a • c)) =
      (⟨_, conv_one_tmul_mem (E := E) hc⟩ : 𝒮) • (fun i => ιA (((algebraMap F E a) • y) i)) := by
    funext i
    rw [conv_tmul_smul]
    rfl
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hy, rfl⟩)

theorem conv_eps_mem (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (n → E)) (y : n → E)
    (d : 𝓞 F) (hd : d ∉ v.asIdeal) (hy : (algebraMap F E (d : F)) • y ∈ Λ) :
    (fun i => afsplitEps E v * ιA (y i)) ∈ latS (F := F) 𝔸 𝒮 Λ := by
  have hval : Valued.v (algebraMap F (v.adicCompletion F) (d : F)) = 1 := by
    rw [levelaf_valued_algebraMap]
    exact (valuation_eq_one_iff_notMem (K := F) (v := v)).2 hd
  have hdv0 : algebraMap F (v.adicCompletion F) (d : F) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hval
    exact zero_ne_one hval
  have hc : (algebraMap F (v.adicCompletion F) (d : F))⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [mem_adicCompletionIntegers, map_inv₀, hval, inv_one]
  have h1 : afsplitI v (1 : v.adicCompletion F) =
      (d : F) • afsplitI v (algebraMap F (v.adicCompletion F) (d : F))⁻¹ := by
    rw [← map_smul, Algebra.smul_def, mul_inv_cancel₀ hdv0]
  have := conv_tmul_mem Λ y (d : F) (afsplitI_mem_intAd v _ hc) hy
  rw [← h1] at this
  simpa only [conv_eps_tmul] using this

theorem conv_exists_den (Λ : Submodule (𝓞 E) (n → E))
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) (y : n → E) :
    ∃ D : 𝓞 F, D ≠ 0 ∧ (algebraMap F E (D : F)) • y ∈ Λ := by
  classical
  obtain ⟨m, hm0, hm⟩ := csGlob_single Λ hspan
  obtain ⟨m', hm'0, hm'⟩ := adelstabL_den y
  refine ⟨((m' * m : ℤ) : 𝓞 F), Int.cast_ne_zero.2 (mul_ne_zero hm'0 hm0), ?_⟩
  have : (algebraMap F E (((m' * m : ℤ) : 𝓞 F) : F)) • y =
      ∑ k, (⟨(m' : E) * y k, hm' k⟩ : 𝓞 E) • (Pi.single k (m : E) : n → E) := by
    ext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def]
      show _ = (m' : E) * y j * (m : E)
      simp only [Int.cast_mul, map_mul, map_intCast]
      ring
    · intro k _ hkj
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hkj), smul_zero]
    · exact fun h => absurd (Finset.mem_univ j) h
  rw [this]
  exact sum_mem fun k _ => Λ.smul_mem _ (hm k)

theorem conv_incl_mem_iff (Λ : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) (x : n → E) :
    (fun i => ιA (x i)) ∈ latS (F := F) 𝔸 𝒮 Λ ↔ x ∈ Λ := by
  conv_rhs => rw [← global_lattice_one_holds F E n Λ hfin hspan]
  show _ ↔ ((1⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ιA (x i)) ∈ latS (F := F) 𝔸 𝒮 Λ
  rw [inv_one, Units.val_one, one_mulVec]

theorem conv_eps_mem_conv (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (n → E))
    (hfin : Module.Finite (𝓞 E) Λ) (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) (y : n → E)
    (h : (fun i => afsplitEps E v * ιA (y i)) ∈ latS (F := F) 𝔸 𝒮 Λ) :
    ∃ d : 𝓞 F, d ∉ v.asIdeal ∧ (algebraMap F E (d : F)) • y ∈ Λ := by
  obtain ⟨D0, hD0, hD0y⟩ := conv_exists_den (F := F) Λ hspan y
  obtain ⟨π, hπv, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hD : π * D0 ≠ 0 := mul_ne_zero hπ0 hD0
  have hDv : π * D0 ∈ v.asIdeal := Ideal.mul_mem_right _ _ hπv
  have hDy : (algebraMap F E ((π * D0 : 𝓞 F) : F)) • y ∈ Λ := by
    have : (algebraMap F E ((π * D0 : 𝓞 F) : F)) • y =
        (algebraMap (𝓞 F) (𝓞 E) π) • ((algebraMap F E (D0 : F)) • y) := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul]
      rw [mul_assoc]
      rfl
    rw [this]
    exact Λ.smul_mem _ hD0y
  have ha : (1 - afsplitI v (1 : v.adicCompletion F) : 𝔸) ∈ intAd F :=
    sub_mem (one_mem _) (afsplitI_mem_intAd v 1 (one_mem _))
  obtain ⟨r, z, hz, hr⟩ := csGlob_intAdApprox F (π * D0) hD _ ha
  have hrv : r ∈ v.asIdeal := by
    have hv := congrArg (fun a : 𝔸 => a v) hr
    simp only [afsplit_sub_apply, afsplit_one_apply, afsplitI_self, sub_self, afsplit_add_apply,
      afsplit_mul_apply] at hv
    have e1 : (algebraMap (𝓞 F) 𝔸 r) v = algebraMap F (v.adicCompletion F) (r : F) := rfl
    have e2 : (algebraMap (𝓞 F) 𝔸 (π * D0)) v =
        algebraMap F (v.adicCompletion F) ((π * D0 : 𝓞 F) : F) := rfl
    rw [e1, e2] at hv
    have e3 : algebraMap F (v.adicCompletion F) (r : F) =
        -(algebraMap F (v.adicCompletion F) ((π * D0 : 𝓞 F) : F) * z v) := by
      linear_combination -hv
    rw [← valuation_lt_one_iff_mem (K := F), ← levelaf_valued_algebraMap, e3, Valuation.map_neg,
      map_mul, levelaf_valued_algebraMap]
    have h1 : v.valuation F ((π * D0 : 𝓞 F) : F) < 1 := (valuation_lt_one_iff_mem (K := F) v _).2 hDv
    have h2 : Valued.v (z v) ≤ 1 := hz v
    calc _ ≤ v.valuation F ((π * D0 : 𝓞 F) : F) * 1 := by gcongr
      _ < 1 := by rwa [mul_one]
  refine ⟨1 - r, fun hmem => ?_, ?_⟩
  · have : (1 : 𝓞 F) ∈ v.asIdeal := by
      have := v.asIdeal.add_mem hmem hrv
      rwa [sub_add_cancel] at this
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  · rw [← conv_incl_mem_iff (F := F) Λ hfin hspan]
    have hz' := conv_tmul_mem Λ y ((π * D0 : 𝓞 F) : F) hz hDy
    have hsum := add_mem h hz'
    convert hsum using 1
    funext i
    rw [Pi.add_apply, conv_eps_tmul, ← TensorProduct.tmul_add]
    have e4 : afsplitI v (1 : v.adicCompletion F) + ((π * D0 : 𝓞 F) : F) • z =
        algebraMap (𝓞 F) 𝔸 (1 - r) := by
      rw [map_sub, map_one (algebraMap (𝓞 F) 𝔸), Algebra.smul_def, ← IsScalarTower.algebraMap_apply (𝓞 F) F 𝔸]
      linear_combination -hr
    rw [e4, csGlob_tmul_int]
    rfl

theorem conv_prV_latS (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (n → E)) (u : n → 𝒜)
    (hu : u ∈ latS (F := F) 𝔸 𝒮 Λ) :
    (fun i => prV (E := E) v (u i)) ∈ latS (F := F) (v.adicCompletion F) Sv[v] Λ := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, hx, rfl⟩ := hu
    exact Submodule.subset_span ⟨x, hx, by funext i; exact (afsplit_prV_inclE v (x i)).symm⟩
  | zero =>
    have := zero_mem (latS (F := F) (v.adicCompletion F) Sv[v] Λ)
    convert this using 1
    funext i
    simp
  | add u w _ _ hu hw =>
    have := add_mem hu hw
    convert this using 1
    funext i
    simp
  | smul a u _ hu =>
    have := Submodule.smul_mem _ (⟨_, afsplit_prV_int v (a : 𝒜) a.2⟩ : Sv[v]) hu
    convert this using 1
    funext i
    show prV (E := E) v ((a : 𝒜) * u i) = _
    rw [map_mul]
    rfl

theorem conv_IE_latS (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (n → E))
    (u : n → E ⊗[F] v.adicCompletion F)
    (hu : u ∈ latS (F := F) (v.adicCompletion F) Sv[v] Λ) :
    (fun i => afsplitIE v (u i)) ∈ latS (F := F) 𝔸 𝒮 Λ := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, hx, rfl⟩ := hu
    have := Submodule.smul_mem (latS (F := F) 𝔸 𝒮 Λ) (⟨_, afsplit_eps_int (E := E) v⟩ : 𝒮)
      (Submodule.subset_span ⟨x, hx, rfl⟩)
    convert this using 1
    funext i
    show afsplitIE v (ιv[v] (x i)) = afsplitEps E v * ιA (x i)
    rw [← afsplit_decomp, afsplit_prV_inclE]
  | zero =>
    have := zero_mem (latS (F := F) 𝔸 𝒮 Λ)
    convert this using 1
    funext i
    simp
  | add u w _ _ hu hw =>
    have := add_mem hu hw
    convert this using 1
    funext i
    simp
  | smul a u _ hu =>
    have := Submodule.smul_mem _ (⟨_, afsplit_IE_int v (a : E ⊗[F] v.adicCompletion F) a.2⟩ : 𝒮) hu
    convert this using 1
    funext i
    show afsplitIE v ((a : E ⊗[F] v.adicCompletion F) * u i) = _
    rw [map_mul]
    rfl

theorem conv_IE_latS_iff (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (n → E))
    (u : n → E ⊗[F] v.adicCompletion F) :
    (fun i => afsplitIE v (u i)) ∈ latS (F := F) 𝔸 𝒮 Λ ↔
      u ∈ latS (F := F) (v.adicCompletion F) Sv[v] Λ := by
  refine ⟨fun h => ?_, conv_IE_latS v Λ u⟩
  have := conv_prV_latS v Λ _ h
  simpa only [afsplit_prV_IE] using this

theorem conv_bc_mulVec {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (γ : GL n A)
    (x : n → A) :
    ((bc φ γ : GL n B) : Matrix n n B) *ᵥ (fun i => φ (x i)) =
      fun i => φ (((γ : Matrix n n A) *ᵥ x) i) := by
  funext i
  rw [RingHom.map_mulVec]
  rfl

theorem conv_locIff [StarRing E] (σ : E →ₐ[F] E) (hσ : (σ : E →+* E) = starRingEnd E)
    (hfix : ∀ e, σ e = e → ∃ a : F, algebraMap F E a = e)
    (Λ : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) (g : GL n 𝒜)
    (p : Ideal (𝓞 E)) [p.IsPrime] (v : HeightOneSpectrum (𝓞 F))
    (hv : v.asIdeal = p.comap (algebraMap (𝓞 F) (𝓞 E))) (x : n → E) :
    x ∈ Formalism.HermitianLatticesTheory.loc (K := E) p (globLat g Λ) ↔
      (((bc (prV (E := E) v) g)⁻¹ : GL n (E ⊗[F] v.adicCompletion F)) :
        Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ (fun i => ιv[v] (x i)) ∈
        latS (F := F) (v.adicCompletion F) Sv[v] Λ := by
  have hlat := global_lattice_isLattice_holds F E n Λ hfin hspan g
  have hfinM : Module.Finite (𝓞 E) (globLat g Λ) := Module.Finite.iff_fg.2 hlat.fg
  have hspanM := hlat.span_eq_top
  rw [mem_loc_iff σ hσ hfix p v.asIdeal hv]
  have step1 : (∃ d : 𝓞 F, d ∉ v.asIdeal ∧ (algebraMap F E (d : F)) • x ∈ globLat g Λ) ↔
      (fun i => afsplitEps E v * ιA (x i)) ∈ latS (F := F) 𝔸 𝒮 (globLat g Λ) :=
    ⟨fun ⟨d, hd, hx⟩ => conv_eps_mem v _ x d hd hx, conv_eps_mem_conv v _ hfinM hspanM x⟩
  rw [step1, ← conv_IE_latS_iff]
  refine Iff.trans (span_recovery_of_integral_adelic_approx csGlob_intAdApprox F E n Λ hfin hspan g
    (fun i => afsplitEps E v * ιA (x i))) ?_
  have h1 : (((bc (prV (E := E) v) g)⁻¹ : GL n (E ⊗[F] v.adicCompletion F)) :
        Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ (fun i => ιv[v] (x i)) =
      fun i => prV (E := E) v ((((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ fun i => ιA (x i)) i) := by
    rw [← map_inv, ← conv_bc_mulVec]
    rfl
  have h2 : ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => afsplitEps E v * ιA (x i)) =
      fun i => afsplitIE v (((((bc (prV (E := E) v) g)⁻¹ : GL n (E ⊗[F] v.adicCompletion F)) :
        Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ (fun i => ιv[v] (x i))) i) := by
    rw [h1]
    funext i
    rw [afsplit_decomp]
    have : (fun i => afsplitEps E v * ιA (x i)) = afsplitEps E v • (fun i => ιA (x i)) := rfl
    rw [this, mulVec_smul]
    rfl
  rw [h2]

end Conv

section Genus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

theorem conv_mem_gmap {R : Type} [CommRing R] [Algebra R E] (γ : GL n E)
    (L : Submodule R (n → E)) (x : n → E) :
    x ∈ Formalism.HermitianLatticesTheory.gmap (glEquiv γ) L ↔ ((γ⁻¹ : GL n E) : Matrix n n E) *ᵥ x ∈ L := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    show ((γ⁻¹ : GL n E) : Matrix n n E) *ᵥ (glEquiv γ y) ∈ L
    rw [glEquiv_apply', mulVec_mulVec, Units.inv_mul, one_mulVec]
    exact hy
  · intro hy
    refine ⟨_, hy, ?_⟩
    show glEquiv γ _ = x
    rw [glEquiv_apply', mulVec_mulVec, Units.mul_inv, one_mulVec]

theorem conv_genus (hWA : WeakApprox1) [StarRing E] (σ : E →ₐ[F] E)
    (hσ : (σ : E →+* E) = starRingEnd E)
    (hfix : ∀ e, σ e = e → ∃ a : F, algebraMap F E a = e) (hθ : ∃ θ, σ θ ≠ θ)
    (h : (n → E) →ₗ⋆[E] (n → E) →ₗ[E] E) (J : Matrix n n E) (hJ : J = gram h)
    (hherm : IsHerm (σ : E →+* E) J) (hdet : IsUnit J.det)
    (Λ : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤)
    (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    globLat g Λ ∈ Formalism.HermitianLatticesTheory.genus h Λ := by
  refine ⟨global_lattice_isLattice_holds F E n Λ hfin hspan g, fun p hp => ?_⟩
  have := hp.isPrime
  have hpne : p ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField E)
  obtain ⟨a, hap, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpne
  have hne : p.comap (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem ha0 hap (Algebra.IsIntegral.isIntegral a)
  let v : HeightOneSpectrum (𝓞 F) := ⟨p.comap (algebraMap (𝓞 F) (𝓞 E)), Ideal.comap_isPrime _ _, hne⟩
  have hstar : ∀ e, σ e = star e := fun e => congrArg (fun f : E →+* E => f e) hσ
  have hinv : ∀ e, σ (σ e) = e := fun e => by rw [hstar, hstar, star_star]
  obtain ⟨γ, hγ, hk⟩ := hWA F E n σ J hinv hθ hherm hdet Λ hfin hspan v _
    (afsplit_bc_mem σ J v g hg)
  refine ⟨glEquiv γ, ?_, ?_⟩
  · rw [← hermitian_lattice_correspondence_holds E n h γ, ← hJ, ← hσ]
    exact hγ
  · ext x
    rw [conv_locIff σ hσ hfix Λ hfin hspan g p v rfl x, conv_mem_gmap]
    have h1 := conv_locIff σ hσ hfix Λ hfin hspan 1 p v rfl (((γ⁻¹ : GL n E) : Matrix n n E) *ᵥ x)
    rw [global_lattice_one_holds F E n Λ hfin hspan, map_one, inv_one, Units.val_one, one_mulVec] at h1
    rw [h1, (inv_mem hk) _, _root_.mul_inv_rev, inv_inv, Units.val_mul, ← mulVec_mulVec,
      conv_bc_mulVec, mulVec_mulVec, Units.mul_inv, one_mulVec]

end Genus

section StdIn

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  {k : ℕ}

theorem genusIn_of_core (hc : WACore) (σ : E →ₐ[F] E) (hσ : ∀ e, σ e = star e)
    (hfix : ∀ e, σ e = e → ∃ a : F, algebraMap F E a = e) (hθ : ∃ θ, σ θ ≠ θ) :
    GenusIn σ (1 : Matrix (Fin k) (Fin k) E) := fun g hg =>
  conv_genus (wal_main hc) σ (sig_eq_star σ hσ) hfix hθ (Formalism.MainNotions.StandardLattice.stdForm E k) 1 gram_stdForm.symm
    (cT_one _) (by simp) (Formalism.MainNotions.StandardLattice.stdLat E k) stdLat_finite stdLat_span g hg

end StdIn

end Formalism.MainNotions.Gaps.CC.Surj
end
end
