module

public import Formalism.LocalToGlobal.GlobalTheory.HLatOps
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.ExistsNsmulMem
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.TruncatedLatticeHolds
public import Formalism.LocalRingCardinality.DataDIVDefs

@[expose] public section

open Module NumberField ComplexOrder

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.HLatOps

open Formalism.BasicNotions Formalism.HN Formalism.HermitianLatticesTheory

section Basic

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]

theorem cnorm_sq (u : ι → ℂ) : cnorm u ^ 2 = ∑ i, ‖u i‖ ^ 2 := by
  unfold cnorm
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)

theorem cnorm_nonneg (u : ι → ℂ) : 0 ≤ cnorm u := by
  unfold cnorm
  exact Real.sqrt_nonneg _

theorem cnorm_eq_zero {u : ι → ℂ} (h : cnorm u = 0) : u = 0 := by
  unfold cnorm at h
  rw [Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg _),
    Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)] at h
  funext i
  have hi := h i (Finset.mem_univ i)
  simpa using hi

theorem normAt_eq_zero (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (hX : IsUnit (X v).det) {x : V} (h : normAt b X v x = 0) : x = 0 := by
  have h1 : (X v)⁻¹.mulVec (vecAt b v x) = 0 := cnorm_eq_zero h
  have h2 : vecAt b v x = 0 := by
    have h3 : (X v).mulVec ((X v)⁻¹.mulVec (vecAt b v x)) = 0 := by
      rw [h1, Matrix.mulVec_zero]
    rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hX, Matrix.one_mulVec] at h3
  apply b.repr.injective
  ext i
  have h4 := congrFun h2 i
  simp only [vecAt, Pi.zero_apply, map_eq_zero] at h4
  simpa using h4

theorem majAt_self (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x : V) : majAt b X v x x = ((normAt b X v x ^ 2 : ℝ) : ℂ) := by
  show (∑ i, star (fcoord b X v x i) * fcoord b X v x i) =
    (((cnorm (fcoord b X v x)) ^ 2 : ℝ) : ℂ)
  rw [cnorm_sq]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem normAt_eq_sqrt (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x : V) : normAt b X v x = Real.sqrt (majAt b X v x x).re := by
  rw [majAt_self, Complex.ofReal_re]
  exact (Real.sqrt_sq (cnorm_nonneg _)).symm

theorem isSesq_maj (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) :
    IsSesq (fun v => majAt b X v) := by
  intro v
  have hadd : ∀ x y : V, fcoord b X v (x + y) = fcoord b X v x + fcoord b X v y := by
    intro x y
    have hv : vecAt b v (x + y) = vecAt b v x + vecAt b v y := by
      funext i
      simp [vecAt]
    unfold fcoord
    rw [hv, Matrix.mulVec_add]
  have hsmul : ∀ (a : K) (x : V), fcoord b X v (a • x) = v.embedding a • fcoord b X v x := by
    intro a x
    have hv : vecAt b v (a • x) = v.embedding a • vecAt b v x := by
      funext i
      simp [vecAt]
    unfold fcoord
    rw [hv, Matrix.mulVec_smul]
  refine ⟨fun x x' y => ?_, fun x y y' => ?_, fun a x y => ?_, fun a x y => ?_⟩
  · simp only [majAt, hadd, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]
  · simp only [majAt, hadd, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  · simp only [majAt, hsmul, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    first
    | (rw [Complex.star_def]; ring)
    | (simp only [RCLike.star_def]; ring)
    | ring
  · simp only [majAt, hsmul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

theorem sesq_eq_sum {H : InfinitePlace K → V → V → ℂ} (hH : IsSesq H) (b : Basis ι K V)
    (v : InfinitePlace K) (x y : V) :
    H v x y = ∑ i, ∑ j, starRingEnd ℂ (vecAt b v x i) * gramOf b (H v) i j * vecAt b v y j := by
  obtain ⟨h1, h2, h3, h4⟩ := hH v
  have hz1 : ∀ y, H v 0 y = 0 := by
    intro y
    have e := h1 0 0 y
    rw [add_zero] at e
    linear_combination (-1 : ℂ) * e
  have hz2 : ∀ x, H v x 0 = 0 := by
    intro x
    have e := h2 x 0 0
    rw [add_zero] at e
    linear_combination (-1 : ℂ) * e
  have hsumL : ∀ (s : Finset ι) (c : ι → K) (y : V),
      H v (∑ i ∈ s, c i • b i) y = ∑ i ∈ s, starRingEnd ℂ (v.embedding (c i)) * H v (b i) y := by
    intro s c y
    refine Finset.induction_on s ?_ ?_
    · simp [hz1]
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, h1, h3, ih]
  have hsumR : ∀ (s : Finset ι) (c : ι → K) (x : V),
      H v x (∑ i ∈ s, c i • b i) = ∑ i ∈ s, v.embedding (c i) * H v x (b i) := by
    intro s c x
    refine Finset.induction_on s ?_ ?_
    · simp [hz2]
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, h2, h4, ih]
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [hsumL, hsumR, vecAt, gramOf, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gramOf_maj (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) :
    gramOf b (majAt b X v) = ((X v)⁻¹).conjTranspose * (X v)⁻¹ := by
  have hv : ∀ i, vecAt b v (b i) = Pi.single i 1 := by
    intro i
    funext j
    simp only [vecAt]
    rw [b.repr_self]
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Finsupp.single_apply, Pi.single_apply, hj, Ne.symm hj]
  have hf : ∀ i k, fcoord b X v (b i) k = (X v)⁻¹ k i := by
    intro i k
    simp [fcoord, hv, Matrix.mulVec, dotProduct, Pi.single_apply]
  ext i j
  simp [gramOf, majAt, hf, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem sesq_ext {F G : V → V → ℂ} {σ : K →+* ℂ} (hσ : ∃ a : K, (σ a).im ≠ 0)
    (hF : (∀ x x' y, F (x + x') y = F x y + F x' y) ∧ (∀ x y y', F x (y + y') = F x y + F x y') ∧
      (∀ (a : K) x y, F (a • x) y = starRingEnd ℂ (σ a) * F x y) ∧
      (∀ (a : K) x y, F x (a • y) = σ a * F x y))
    (hG : (∀ x x' y, G (x + x') y = G x y + G x' y) ∧ (∀ x y y', G x (y + y') = G x y + G x y') ∧
      (∀ (a : K) x y, G (a • x) y = starRingEnd ℂ (σ a) * G x y) ∧
      (∀ (a : K) x y, G x (a • y) = σ a * G x y))
    (h : ∀ x, F x x = G x x) (x y : V) : F x y = G x y := by
  obtain ⟨a, ha⟩ := hσ
  obtain ⟨hF1, hF2, hF3, hF4⟩ := hF
  obtain ⟨hG1, hG2, hG3, hG4⟩ := hG
  have key : ∀ u w : V, F u w + F w u = G u w + G w u := by
    intro u w
    have h1 := h (u + w)
    rw [hF1, hF2, hF2, hG1, hG2, hG2] at h1
    linear_combination h1 - h u - h w
  have k1 := key x y
  have k2 := key x (a • y)
  rw [hF4, hF3, hG4, hG3] at k2
  have hne : σ a - starRingEnd ℂ (σ a) ≠ 0 := by
    intro h0
    apply ha
    have h5 := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at h5
    linarith
  have hprod : (σ a - starRingEnd ℂ (σ a)) * (F x y - G x y) = 0 := by
    linear_combination k2 - (starRingEnd ℂ (σ a)) * k1
  rcases mul_eq_zero.1 hprod with h0 | h0
  · exact absurd h0 hne
  · exact sub_eq_zero.1 h0

theorem exists_im_ne_zero [_root_.NumberField.IsTotallyComplex K] (v : InfinitePlace K) :
    ∃ a : K, (v.embedding a).im ≠ 0 := by
  have hc : v.IsComplex := IsTotallyComplex.isComplex v
  rw [InfinitePlace.isComplex_iff] at hc
  by_contra hcon
  push_neg at hcon
  apply hc
  rw [ComplexEmbedding.isReal_iff]
  ext a
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact Complex.conj_eq_iff_im.2 (hcon a)

end Basic

section IsoSec

variable {K : Type} [Field K] [NumberField K] [StarRing K]

variable {A B : HLat K}

theorem frame_free : FrameFree := by
  intro K V ι κ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' hn L hL
  obtain ⟨h1, -, h3, h4, h5, -, -⟩ := rerealize K V ι V κ b X b' X' LinearMap.id hX hX'
    Function.injective_id (fun v x => (hn v x).symm) L hL
  have hid : L.map ((LinearMap.id : V →ₗ[K] V).restrictScalars (𝓞 K)) = L := by
    ext x
    simp
  rw [hid] at h1 h3 h4 h5
  refine ⟨h1.symm, ?_, ?_, ?_⟩
  · unfold muDef; rw [h3]
  · unfold muMaxDef; rw [h4]
  · unfold muMinDef; rw [h5]

end IsoSec

section Forms

open scoped MatrixOrder in
theorem exists_frame {ι : Type} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι ℂ} (hG : G.PosDef) :
    ∃ B : Matrix ι ι ℂ, IsUnit B.det ∧ B.conjTranspose * B = G := by
  have hex : ∃ B : Matrix ι ι ℂ, G = B.conjTranspose * B := by
    first
    | exact Matrix.posSemidef_iff_eq_conjTranspose_mul_self.1 hG.posSemidef
    | (obtain ⟨B, hB⟩ := Matrix.posSemidef_iff_eq_conjTranspose_mul_self.1 hG.posSemidef
       exact ⟨B, hB⟩)
    | (have h0 : (0 : Matrix ι ι ℂ) ≤ G := Matrix.nonneg_iff_posSemidef.2 hG.posSemidef
       refine ⟨CFC.sqrt G, ?_⟩
       have hs : (CFC.sqrt G).conjTranspose = CFC.sqrt G := (CFC.sqrt_nonneg G).isSelfAdjoint
       rw [hs]
       exact (CFC.sqrt_mul_sqrt_self G h0).symm)
  obtain ⟨B, hB⟩ := hex
  refine ⟨B, ?_, hB.symm⟩
  have hdet : G.det ≠ 0 := by
    first
    | exact hG.det_pos.ne'
    | exact hG.det_ne_zero
    | exact (Matrix.isUnit_iff_isUnit_det G).1 hG.isUnit |>.ne_zero
  rw [isUnit_iff_ne_zero]
  intro h0
  apply hdet
  rw [hB, Matrix.det_mul, h0, mul_zero]

theorem frameOf_spec {ι : Type} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι ℂ} (hG : G.PosDef) :
    IsUnit (frameOf G).det ∧ ((frameOf G)⁻¹).conjTranspose * (frameOf G)⁻¹ = G := by
  have h := exists_frame hG
  have hspec := Classical.choose_spec h
  unfold frameOf
  rw [dite_eq_left h]
  refine ⟨Matrix.isUnit_nonsing_inv_det _ hspec.1, ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv _ hspec.1]
  exact hspec.2

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem of_form_spec : OfFormSpec := by
  unfold OfFormSpec
  intro K V ι _ _ _ _ _ _ _ _ _ b L H hH hP
  have hF : ∀ v, IsUnit (frameOf (gramOf b (H v))).det ∧
      ((frameOf (gramOf b (H v)))⁻¹).conjTranspose * (frameOf (gramOf b (H v)))⁻¹ =
        gramOf b (H v) := fun v => frameOf_spec (hP v)
  have hmaj : ∀ v x y, majAt b (fun v => frameOf (gramOf b (H v))) v x y = H v x y := by
    intro v x y
    have e1 : majAt b (fun v => frameOf (gramOf b (H v))) v x y =
        ∑ i, ∑ j, starRingEnd ℂ (vecAt b v x i) *
          gramOf b (majAt b (fun v => frameOf (gramOf b (H v))) v) i j * vecAt b v y j :=
      sesq_eq_sum (isSesq_maj b _) b v x y
    have e2 : H v x y = ∑ i, ∑ j, starRingEnd ℂ (vecAt b v x i) * gramOf b (H v) i j *
        vecAt b v y j := sesq_eq_sum hH b v x y
    rw [e1, e2, gramOf_maj, (hF v).2]
  refine ⟨fun v => (hF v).1, hmaj, fun v x => ?_⟩
  rw [normAt_eq_sqrt]
  exact congrArg (fun t => Real.sqrt t.re) (hmaj v x x)

theorem posAt_comp {V ι W κ : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ] (b : Basis ι K V) (c : Basis κ K W)
    {H : InfinitePlace K → V → V → ℂ} (hH : IsSesq H) (hP : PosAt b H) (f : W →ₗ[K] V)
    (hf : Function.Injective f) : PosAt c (fun v x y => H v (f x) (f y)) := by
  intro v
  have hG := hP v
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f (LinearMap.ker_eq_bot.2 hf)
  obtain ⟨M, hM⟩ : ∃ M, M = (LinearMap.toMatrix c b f).map v.embedding := ⟨_, rfl⟩
  have hinv : ((LinearMap.toMatrix b c g).map v.embedding) * M = 1 := by
    rw [hM, ← Matrix.map_mul, ← LinearMap.toMatrix_comp, hg, LinearMap.toMatrix_id,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hinj : Function.Injective M.mulVec := by
    intro a a' h
    have h1 := congrArg ((LinearMap.toMatrix b c g).map v.embedding).mulVec h
    simpa [Matrix.mulVec_mulVec, hinv] using h1
  have hvec : ∀ j, vecAt b v (f (c j)) = fun k => M k j := by
    intro j
    funext k
    rw [hM]
    simp only [vecAt, Matrix.map_apply]
    rw [LinearMap.toMatrix_apply]
  have hgram : gramOf c (fun x y => H v (f x) (f y)) = M.conjTranspose * gramOf b (H v) * M := by
    ext i j
    simp only [gramOf, Matrix.of_apply]
    rw [sesq_eq_sum hH b v (f (c i)) (f (c j)), hvec, hvec]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rfl
  show (gramOf c (fun x y => H v (f x) (f y))).PosDef
  rw [hgram]
  first
  | exact hG.conjTranspose_mul_mul_same hinj
  | exact Matrix.PosDef.conjTranspose_mul_mul_same hG hinj

theorem isSesq_comp {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {H : InfinitePlace K → V → V → ℂ} (hH : IsSesq H) (f : W →ₗ[K] V) :
    IsSesq (fun v x y => H v (f x) (f y)) := by
  intro v
  obtain ⟨h1, h2, h3, h4⟩ := hH v
  refine ⟨fun x x' y => ?_, fun x y y' => ?_, fun a x y => ?_, fun a x y => ?_⟩
  · simp only [map_add (f := _)]
    exact h1 _ _ _
  · simp only [map_add (f := _)]
    exact h2 _ _ _
  · simp only [map_smul]
    exact h3 _ _ _
  · simp only [map_smul]
    exact h4 _ _ _

theorem posAt_maj {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) :
    PosAt b (fun v => majAt b X v) := by
  intro v
  show (gramOf b (majAt b X v)).PosDef
  rw [gramOf_maj]
  have hinj : Function.Injective ((X v)⁻¹).mulVec := by
    intro a c hac
    have h1 := congrArg (X v).mulVec hac
    simpa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hX v)] using h1
  first
  | exact Matrix.PosDef.conjTranspose_mul_self _ hinj
  | exact (Matrix.posDef_conjTranspose_mul_self_iff _).2 hinj
  | (have h1 := Matrix.PosDef.one.conjTranspose_mul_mul_same hinj
     simpa using h1)

end Forms

section Pull

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem pull_spec1 (B : HLat K) {W κ : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] [Fintype κ] [DecidableEq κ] (c : Basis κ K W) (f : W →ₗ[K] B.V)
    (hB : FrameOK B) (hf : Function.Injective f) :
    FrameOK (pull B c f) ∧
    (∀ v (x y : W), majAt (pull B c f).b (pull B c f).X v x y = majAt B.b B.X v (f x) (f y)) ∧
    (∀ v (x : W), normAt (pull B c f).b (pull B c f).X v x = normAt B.b B.X v (f x)) := by
  have hS : IsSesq (fun v x y => majAt B.b B.X v (f x) (f y)) :=
    isSesq_comp (isSesq_maj B.b B.X) f
  have hPos : PosAt c (fun v x y => majAt B.b B.X v (f x) (f y)) :=
    posAt_comp B.b c (isSesq_maj B.b B.X) (posAt_maj B.b B.X hB) f hf
  obtain ⟨h1, h2, h3⟩ := of_form_spec K W κ c (B.L.comap (f.restrictScalars (𝓞 K))) _ hS hPos
  refine ⟨h1, h2, fun v x => ?_⟩
  rw [h3, normAt_eq_sqrt]

theorem map_comap_eq' {V W : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] (f : W →ₗ[K] V) (L : Submodule (𝓞 K) V) :
    (L.comap (f.restrictScalars (𝓞 K))).map (f.restrictScalars (𝓞 K)) =
      L ⊓ (LinearMap.range f).restrictScalars (𝓞 K) := by
  rw [Submodule.map_comap_eq, inf_comm]
  first
  | rfl
  | (congr 1
     ext y
     simp [LinearMap.mem_range])

theorem rkK_map {V W : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] (f : W →ₗ[K] V) (hf : Function.Injective f)
    (N : Submodule (𝓞 K) W) : rkK (N.map (f.restrictScalars (𝓞 K))) = rkK N := by
  unfold rkK
  have hs : Submodule.span K ((N.map (f.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V) =
      (Submodule.span K (N : Set W)).map f := by
    rw [Submodule.map_coe, ← Submodule.span_image]
    rfl
  rw [hs]
  exact (Submodule.equivMapOfInjective f hf _).finrank_eq.symm

theorem pull_spec : PullSpec := by
  intro K _ _ _ B W κ _ _ _ _ _ _ c f hB hf
  obtain ⟨h1, h2, h3⟩ := pull_spec1 B c f hB hf
  have hf' : Function.Injective (f.restrictScalars (𝓞 K)) := hf
  have hfg : B.L.FG → (pull B c f).L.FG := by
    intro hL
    apply Submodule.fg_of_fg_map_injective (f.restrictScalars (𝓞 K)) hf'
    show ((B.L.comap (f.restrictScalars (𝓞 K))).map (f.restrictScalars (𝓞 K))).FG
    rw [map_comap_eq']
    exact Formalism.LFunctionChainParameters.slopeLatticeData.fg_of_le hL inf_le_left
  refine ⟨h1, h2, h3, fun hL => ?_, fun hG => ⟨h1, hfg hG.2.1, ?_⟩⟩
  · obtain ⟨-, -, r3, r4, r5, -, -⟩ := rerealize K W κ B.V B.ι (pull B c f).b (pull B c f).X B.b B.X f
      h1 hB hf (fun v x => (h3 v x).symm) (pull B c f).L (hfg hL)
    have hm : (pull B c f).L.map (f.restrictScalars (𝓞 K)) =
        B.L ⊓ (LinearMap.range f).restrictScalars (𝓞 K) := map_comap_eq' f B.L
    rw [hm] at r3 r4 r5
    refine ⟨hfg hL, ?_, ?_, ?_, ?_⟩
    · show rkK (pull B c f).L = rkK (B.L ⊓ (LinearMap.range f).restrictScalars (𝓞 K))
      rw [← hm, rkK_map f hf]
    · show muDef (pull B c f).b (pull B c f).X (pull B c f).L =
        muDef B.b B.X (B.L ⊓ (LinearMap.range f).restrictScalars (𝓞 K))
      unfold muDef; rw [r3]
    · show muMaxDef (pull B c f).b (pull B c f).X (pull B c f).L =
        muMaxDef B.b B.X (B.L ⊓ (LinearMap.range f).restrictScalars (𝓞 K))
      unfold muMaxDef; rw [r4]
    · show muMinDef (pull B c f).b (pull B c f).X (pull B c f).L =
        muMinDef B.b B.X (B.L ⊓ (LinearMap.range f).restrictScalars (𝓞 K))
      unfold muMinDef; rw [r5]
  · rw [eq_top_iff]
    intro x _
    have hx : f x ∈ Submodule.span K (B.L : Set B.V) := by rw [hG.2.2]; trivial
    obtain ⟨d, hd, hdx⟩ := Formalism.LFunctionChainParameters.LLcv.span_le_locS B.L hx
    have hd0 : algebraMap (𝓞 K) K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    have h4 : d • x ∈ (pull B c f).L := by
      show (f.restrictScalars (𝓞 K)) (d • x) ∈ B.L
      rw [map_smul]
      exact hdx
    have h5 : x = (algebraMap (𝓞 K) K d)⁻¹ • (d • x) := by
      rw [← algebraMap_smul K d x, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rw [h5]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h4)

end Pull

section Unitary

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

end Unitary

section DualSec

variable {K : Type} [Field K] [NumberField K] [StarRing K] {A B : HLat K}

theorem dual_numbers : DualNumbers := by
  intro K _ _ _ _ A hG hr
  have hL : A.L ≠ ⊥ := Formalism.LFunctionChainParameters.slopeLatticeData.ne_bot_of_rkK_pos hr
  have hd := dualPl K A.V A.ι A.b A.X hG.1 A.L hG.2.1 hG.2.2
  have hXd : ∀ v, IsUnit (dualFrame A.X v).det := DualPolygon.dualFrame_unit A.X hG.1
  have : Module.Finite K A.V := Module.Finite.of_basis A.b
  have hdne : dualLat A.L ≠ ⊥ := by
    intro h
    have htop := hd.2.1
    rw [h, Submodule.bot_coe, Submodule.span_zero_singleton] at htop
    have h0 : Module.finrank K (Module.Dual K A.V) = 0 := by
      rw [← finrank_top K (Module.Dual K A.V), ← htop, finrank_bot]
    rw [Subspace.dual_finrank_eq] at h0
    have : rkK A.L ≤ Module.finrank K A.V := Submodule.finrank_le _
    simp only [HLat.rank] at hr
    omega
  have hs1 := sizeMu K A.V A.ι A.b A.X hG.1 A.L hG.2.1 hL
  have hs2 := sizeMu K (Module.Dual K A.V) A.ι A.b.dualBasis (dualFrame A.X) hXd
    (dualLat A.L) hd.1 hdne
  simp only at hs1 hs2
  have hc : logDisc K / (2 * (Module.finrank ℚ K : ℝ)) =
      logDisc K / (Module.finrank ℚ K : ℝ) / 2 := by rw [div_div, mul_comm]
  refine ⟨?_, ?_, ?_⟩
  · show muDef A.b.dualBasis (dualFrame A.X) (dualLat A.L) = -muDef A.b A.X A.L
    rw [hs2.2.1, hs1.2.1, hd.2.2.2.1, Real.log_inv]
    ring
  · have e := hd.2.2.2.2.1
    rw [hs2.2.2.2.1, hs1.2.2.2.2.1, ← Real.exp_neg] at e
    have e2 := Real.exp_injective e
    rw [hc] at e2
    show muMaxDef A.b.dualBasis (dualFrame A.X) (dualLat A.L) = -muMinDef A.b A.X A.L
    unfold muMaxDef muMinDef
    linarith
  · have e := hd.2.2.2.2.2.1
    rw [hs2.2.2.2.2.1, hs1.2.2.2.1, ← Real.exp_neg] at e
    have e2 := Real.exp_injective e
    rw [hc] at e2
    show muMinDef A.b.dualBasis (dualFrame A.X) (dualLat A.L) = -muMaxDef A.b A.X A.L
    unfold muMaxDef muMinDef
    linarith

end DualSec

section HtMap

variable {K : Type} [Field K] [NumberField K] [StarRing K]

end HtMap

section Emb

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem frameOK_of_emb (A B : HLat K) (ψ : A.V →ₗ[K] B.V) (hB : FrameOK B)
    (hψ : Function.Injective ψ) (hn : ∀ v x, normAt A.b A.X v x = normAt B.b B.X v (ψ x)) :
    FrameOK A := by
  intro v
  by_contra hv
  have h0 : ∀ y : A.V, y = 0 := by
    intro y
    have hy : normAt B.b B.X v (ψ y) = 0 := by
      rw [← hn]
      show cnorm ((A.X v)⁻¹.mulVec (vecAt A.b v y)) = 0
      rw [Matrix.nonsing_inv_apply_not_isUnit _ hv, Matrix.zero_mulVec]
      simp [cnorm]
    exact hψ (by rw [normAt_eq_zero B.b B.X v (hB v) hy, map_zero])
  haveI hι : IsEmpty A.ι := ⟨fun i => A.b.ne_zero i (h0 _)⟩
  apply hv
  rw [Matrix.det_isEmpty]
  exact isUnit_one

theorem emb_numbers : EmbNumbers := by
  intro K _ _ _ A B ψ hB hψ hn
  have hA := frameOK_of_emb A B ψ hB hψ hn
  refine ⟨hA, fun N => ⟨(rkK_map ψ hψ N).symm, fun hN => ?_⟩⟩
  obtain ⟨h1, -, h3, h4, h5, -, -⟩ := rerealize K A.V A.ι B.V B.ι A.b A.X B.b B.X ψ hA hB hψ
    (fun v x => (hn v x).symm) N hN
  refine ⟨?_, ?_, ?_, ?_⟩
  · show muDef A.b A.X N = muDef B.b B.X (N.map (ψ.restrictScalars (𝓞 K)))
    unfold muDef; rw [h3]
  · show muMaxDef A.b A.X N = muMaxDef B.b B.X (N.map (ψ.restrictScalars (𝓞 K)))
    unfold muMaxDef; rw [h4]
  · show muMinDef A.b A.X N = muMinDef B.b B.X (N.map (ψ.restrictScalars (𝓞 K)))
    unfold muMinDef; rw [h5]
  · show (2 / (finrank ℚ K : ℝ)) * Real.log (ht A.b A.X N) =
      (2 / (finrank ℚ K : ℝ)) * Real.log (ht B.b B.X (N.map (ψ.restrictScalars (𝓞 K))))
    rw [h1]

theorem comap_fg {V W : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] (f : W →ₗ[K] V) (hf : Function.Injective f)
    {L : Submodule (𝓞 K) V} (hL : L.FG) : (L.comap (f.restrictScalars (𝓞 K))).FG := by
  apply Submodule.fg_of_fg_map_injective (f.restrictScalars (𝓞 K)) hf
  rw [map_comap_eq']
  have hN : IsNoetherian (𝓞 K) L := isNoetherian_of_fg_of_noetherian L hL
  exact isNoetherian_submodule.mp hN _ inf_le_left

end Emb

section Ext

open TensorProduct

variable {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K']
  [StarRing K'] [Algebra K K']

end Ext

section Record

open Formalism.BasicNotions.DV

end Record

section Checks

variable {K : Type} [Field K] [NumberField K] [StarRing K]

end Checks

end Formalism.L2.GlobalTheoryTheory.HLatOps
