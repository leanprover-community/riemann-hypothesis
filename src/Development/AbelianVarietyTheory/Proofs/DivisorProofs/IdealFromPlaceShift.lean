import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisLatTQuotPure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairTAdjTLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateKernelAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedBasis
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsTangentChartOfIsUnivChart
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PlaceShiftSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearPatPoint
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDvrExtensionForMonicFamily
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PointShiftStOfPlaceShiftSt

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.CompHt GlobalTheory.CM GlobalTheory.PointMap
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PointSig

section Rank

open GlobalTheory.HodgeTateCompare GlobalTheory.EigenLieCompare GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeRankLie

variable {O C : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field C] [Algebra O C] [IsFractionRing O C]
  {G : Over (Sp O)} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {Λ : Type} [CommRing Λ] (α : Out.RingAct G Λ)

theorem rTau_eq_of_lieMult (τ : Λ →+* O) {N : ℕ}
    (h : LieMult (ofRingAct α) (spMap (algebraMap O C)) ((algebraMap O C).comp τ) N) : AvDefs.rTau G α τ = N := by
  obtain ⟨n, x, hx⟩ := Chart.univChartLoc G
  have hB : LieLatCompare.CoordBC hx C :=
    (LieLatCompare.tangentBaseChange_iff_one.2 (LieLatCompare.tanBCOne_of_tanBCSt Chart.tanBC)) O G n x hx C
  rw [LieLatCompare.lieMult_iff hx hB] at h
  obtain ⟨h₁, h₂⟩ := finite_free_eigSub α τ
  rw [rTau_eq, eigRank_eq, Module.finrank_linearMap_self, ← h]
  choose f₀ hf₀ using fun c : Fin n → O =>
    (lieEquiv G).surjective ⟨Chart.tvec (x := x) c, Chart.isTan_tvec hx c⟩
  have hf : ∀ c, (lieEquiv G (f₀ c)).1 = Chart.tvec (x := x) c := fun c => congrArg Subtype.val (hf₀ c)
  let f : (Fin n → O) →ₗ[O] GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.Lie G :=
    { toFun := f₀
      map_add' := fun c c' => lie_ext (by
        rw [lieEquiv_add, hf, hf, hf]
        exact Chart.tvec_add hx c c')
      map_smul' := fun a c => lie_ext (by
        rw [RingHom.id_apply, lieEquiv_smul, hf, hf]
        exact Chart.tvec_smul hx a c) }
  replace hf : ∀ c, (lieEquiv G (f c)).1 = Chart.tvec (x := x) c := hf
  let e : (Fin n → O) ≃ₗ[O] GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.Lie G := LinearEquiv.ofBijective f
    ⟨fun c c' hc => Chart.tvec_inj hx (by rw [← hf, ← hf, hc]), fun y =>
      ⟨Chart.tcoord hx (lieEquiv G y).1 (lieEquiv G y).2, lie_ext (by
        rw [hf]; exact (Chart.tcoord_spec hx _ _).symm)⟩⟩
  have hmem : ∀ c, e c ∈ eigSub α τ ↔ ∀ a, lieAct hx (ofRingAct α) a c = τ a • c := fun c =>
    forall_congr' fun a => by
      haveI := α.hom a
      change (lieEquiv G (f c)).1 ≫ _ = (lieEquiv G (τ a • f c)).1 ↔ _
      rw [← map_smul, hf, hf, Chart.tvec_smul hx]
      exact Chart.tvec_eig_iff hx (α.act a) c (τ a)
  let B : eigSub α τ →ₗ[O] (Fin n → C) :=
    (Algebra.linearMap O C).compLeft (Fin n) ∘ₗ e.symm.toLinearMap ∘ₗ (eigSub α τ).subtype
  have hinj := IsFractionRing.injective O C
  have hBi : Function.Injective B := fun y y' hy =>
    Subtype.ext (e.symm.injective (funext fun k => hinj (congrFun hy k)))
  have key : ∀ (c : Fin n → O) (a : Λ), (extendLin C (lieAct hx (ofRingAct α) a) -
      (algebraMap O C).comp τ a • (LinearMap.id : (Fin n → C) →ₗ[C] _)) (algebraMap O C ∘ c) = 0 ↔
      lieAct hx (ofRingAct α) a c = τ a • c := fun c a => by
    rw [LinearMap.sub_apply, LieLatCompare.extendLin_comp, sub_eq_zero]
    refine ⟨fun hc => funext fun k => hinj ?_, fun hc => funext fun k => ?_⟩
    · simpa [Algebra.smul_def] using congrFun hc k
    · simp [hc, Algebra.smul_def]
  rw [← HodgeTateEigenRank.finrank_span_range (C := C) B hBi]
  refine congrArg (fun S : Submodule C (Fin n → C) => Module.finrank C S)
    (le_antisymm (Submodule.span_le.2 ?_) fun w hw => ?_)
  · rintro _ ⟨y, rfl⟩
    refine (Submodule.mem_iInf _).2 fun a => (key (e.symm y.1) a).2 ?_
    exact (hmem _).1 (by rw [e.apply_symm_apply]; exact y.2) a
  · obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) w
    choose c hc using hs
    have hs' : algebraMap O C s ≠ 0 := fun h0 => nonZeroDivisors.coe_ne_zero s (hinj (by rw [h0, map_zero]))
    have hc' : algebraMap O C ∘ c = algebraMap O C s • w := funext fun k => by
      simpa [Algebra.smul_def] using hc k
    have hm : e c ∈ eigSub α τ := (hmem c).2 fun a => (key c a).1 (by
      rw [hc']
      exact (Submodule.mem_iInf _).1 (Submodule.smul_mem _ _ hw) a)
    have : w = (algebraMap O C s)⁻¹ • B ⟨e c, hm⟩ := by
      have h1 : B ⟨e c, hm⟩ = algebraMap O C ∘ c := by
        change algebraMap O C ∘ e.symm (e c) = _
        rw [e.symm_apply_apply]
      rw [h1, hc', smul_smul, inv_mul_cancel₀ hs', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

end Rank

section Frames

open GlobalTheory.HodgeTateCompare GlobalTheory.EigenLieCompare GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type}
  [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O]
  [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

theorem bLie_injective (hcok : CokernelBound P) : Function.Injective P.bLie := by
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  obtain ⟨-, -, hb⟩ := Point.omega_free_finite_bijective p C v O Λ P
  have hp : algebraMap O C ((p : O) ^ 2) ≠ 0 := by
    rw [map_pow, map_natCast]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  intro x y hxy
  have h0 : ∀ t, (P.al₀ t).1 x = (P.al₀ t).1 y := fun t => P.integers.hom_inj (by
    rw [← P.pairV_bLie, ← P.pairV_bLie, hxy])
  have h1 : ∀ z, (P.al z).1 x = (P.al z).1 y := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => simp only [map_add, Submodule.coe_add, Pi.add_apply, hz, hz']
    | tmul c t => simp only [Point.al_tmul, Submodule.coe_smul, Pi.smul_apply, h0]
  refine hb.1 (LinearMap.ext fun f => ?_)
  obtain ⟨z, hz⟩ := hcok f
  have h2 := h1 z
  rw [hz] at h2
  exact mul_left_cancel₀ (fun h => hp (by rw [h, map_zero])) h2

theorem exists_basis_wRec (hinj : Function.Injective P.bLie) (τ : Λ →+* O) {n : ℕ}
    (hn : AvDefs.rTau P.Gt P.oGt τ = n) :
    ∃ x : Fin n → LieG P.Gt, (∀ j, AvDefs.IsEig P.Gt P.oGt τ (x j)) ∧
      LinearIndependent C (fun j => P.bLie (x j)) ∧
      Submodule.span O (Set.range fun j => P.bLie (x j)) = P.wRec τ := by
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := ValuationRing.of_integers v P.integers
  haveI : IsFractionRing O C := P.integers.isFractionRing
  haveI := (GlobalTheory.UnitRigidity.smooth_geometricallyConnected_of_isGt _ _ ⟨P.D⟩).1
  obtain ⟨h₁, h₂⟩ := finite_free_eigSub P.oGt τ
  rw [rTau_eq, eigRank_eq, Module.finrank_linearMap_self] at hn
  let B : eigSub P.oGt τ →ₗ[O] P.V :=
    { toFun := fun x => P.bLie (lieEquiv P.Gt x.1)
      map_add' := fun x y => by
        rw [← P.bLie_add]
        exact congrArg P.bLie (Subtype.ext (lieEquiv_add x.1 y.1))
      map_smul' := fun c x => by
        rw [RingHom.id_apply, ← P.bLie_scale]
        exact congrArg P.bLie (Subtype.ext (lieEquiv_smul c x.1)) }
  have hBi : Function.Injective B := fun x y h =>
    Subtype.ext ((lieEquiv P.Gt).injective (hinj h))
  have hr : LinearMap.range B = P.wRec τ := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(eigEquiv P.oGt τ).symm (subEquiv P.oGt τ x), rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨(subEquiv P.oGt τ).symm (eigEquiv P.oGt τ x), congrArg P.bLie ?_⟩
      exact (subEquiv_val P.oGt τ _).symm.trans
        (congrArg Subtype.val ((subEquiv P.oGt τ).apply_symm_apply _))
  let b := Module.finBasisOfFinrankEq O (eigSub P.oGt τ) hn
  refine ⟨fun j => lieEquiv P.Gt (b j).1, fun j => ((eigEquiv P.oGt τ).symm (subEquiv P.oGt τ (b j))).2,
    (LinearIndependent.iff_fractionRing O C).1 (b.linearIndependent.map' B (LinearMap.ker_eq_bot.2 hBi)), ?_⟩
  rw [← hr]
  change Submodule.span O (Set.range (B ∘ b)) = _
  rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_top]

theorem exists_frame (hinj : Function.Injective P.bLie) (τ : Λ →+* O) {n : ℕ} (hn : AvDefs.rTau P.Gt P.oGt τ = n)
    {La : Submodule O P.V} (hfg : La.FG) (hle : P.wRec τ ≤ La) :
    ∃ (x : Fin n → LieG P.Gt) (g : Matrix (Fin n) (Fin n) C), (∀ j, AvDefs.IsEig P.Gt P.oGt τ (x j)) ∧
      LinearIndependent C (fun j => P.bLie (x j)) ∧
      Submodule.span O (Set.range fun j => P.bLie (x j)) = P.wRec τ ∧ g.det ≠ 0 ∧
      IsLatBasis C La fun i => ∑ j, g i j • P.bLie (x j) := by
  obtain ⟨x, h1, h2, h3⟩ := exists_basis_wRec P hinj τ hn
  obtain ⟨g, g1, g2, g3⟩ := FlagBasis.exists_adapted_basis O C P.V v P.integers n La hfg _ h2 fun j =>
    ⟨1, one_ne_zero, by rw [one_smul]; exact hle ⟨⟨x j, h1 j⟩, rfl⟩⟩
  refine ⟨x, g, h1, h2, h3, ?_, g3⟩
  rw [Matrix.det_of_lowerTriangular _ fun i j hij => g1 i j hij]
  exact Finset.prod_ne_zero_iff.2 fun i _ => g2 i

theorem span_eq_eigW (hcok : CokernelBound P) (hW : P.W = Submodule.span C (Set.range P.bLie)) (τ : Λ →+* O) {n : ℕ}
    (hn : AvDefs.rTau P.Gt P.oGt τ = n) {x : Fin n → LieG P.Gt} (h1 : ∀ j, AvDefs.IsEig P.Gt P.oGt τ (x j))
    (h2 : LinearIndependent C fun j => P.bLie (x j)) :
    Submodule.span C (Set.range fun j => P.bLie (x j)) = P.eigW τ := by
  refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨j, rfl⟩
    exact ⟨hW.ge (Submodule.subset_span ⟨_, rfl⟩), bLie_mem_eigV (h1 j)⟩
  · rw [finrank_span_eq_card h2, Fintype.card_fin, HodgeTateEigenRank.finrank_eigW p C v O Λ P hcok hW, hn]

end Frames

section Triples

open GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] [IsAlgClosed C] {v : Valuation C ℝ≥0} {O : Type}
  [CommRing O] [Algebra O C] (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C)

omit [NumberField K] [IsAlgClosed C] in

theorem conj_rt_ne (H : Host E) : IsCMField.complexConj E (H.rt : E) ≠ (H.rt : E) := by
  intro h
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h1 := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
  rw [h] at h1
  have h2 : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, RingOfIntegers.coe_eq_algebraMap, ← map_pow, H.rt_sq]; simp
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h1.symm
  rw [hr] at h2
  have h3 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast h2
  have h4 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg r]

open Classical in

theorem rTau_patPoint (T : PAT H (Sp (𝓞 K))) {ρ : 𝓞 K} {p q : ℕ} (hT : HasType H T.t.act ρ p q) (τ : 𝓞 E →+* O) :
    letI := H.starRing
    AvDefs.rTau (patPoint hv ε i T).Gt (patPoint hv ε i T).oGt τ =
      if algebraMap O C (τ H.rt) = i (ρ : K) then p else q := by
  letI := H.starRing
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : IsFractionRing O C := hv.isFractionRing
  haveI := (GlobalTheory.UnitRigidity.smooth_geometricallyConnected_of_isGt _ _ ⟨(patPoint hv ε i T).D⟩).1
  have hβ : ∀ a, ((algebraMap O C).comp (embO hv i)) a = i (a : K) := fun a => algebraMap_embO hv i a
  have h := hT C ((algebraMap O C).comp (embO hv i)) (fun a b hab => by
    rw [hβ, hβ] at hab
    exact RingOfIntegers.coe_injective (i.injective hab)) ((algebraMap O C).comp τ)
  rw [hβ, ← spMap_spMap] at h
  refine rTau_eq_of_lieMult (C := C) _ τ ((LiePull.lieMult_pull (𝓞 E) _ _ T.t.G (patPoint hv ε i T).Gt (spMap (embO hv i))
    (pullback.fst T.t.G.hom _) T.t.act _ (isGrpPullback_pullback T.t.G _) (fun a => ?_) C _ _ _).2 ?_)
  · change ((patPoint hv ε i T).oGt.act a).left ≫ _ = _
    rw [goodPoint_oGt]
    exact pullback.lift_fst _ _ _
  · split_ifs with h0
    exacts [h.1 h0, h.2 h0]

end Triples

section Main

open GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type}
  [CommRing O] [Algebra O C] [Fact ¬IsUnit (ℓ : O)] [IsAdicComplete (Ideal.span {(ℓ : O)}) O] [Algebra ℤ_[ℓ] O]
  [Algebra ℤ_[ℓ] C] [IsScalarTower ℤ_[ℓ] O C]

open Classical in

def HasSigFrames [StarRing (𝓞 E)] (P : Point ℓ v O (𝓞 E)) (rt : 𝓞 E) (τ : E →+* C) (p q : ℕ) : Prop :=
  (∀ φ : E →+* C, Module.finrank C (P.eigW (embO P.integers φ)) = if φ (rt : E) = τ (rt : E) then p else q) ∧
    ∃ (x : Fin p → LieG P.Gt) (x' : Fin q → LieG P.Gt) (g : Matrix (Fin p) (Fin p) C) (g' : Matrix (Fin q) (Fin q) C),
      Submodule.span O (Set.range fun j => P.bLie (x j)) = P.wRec (embO P.integers τ) ∧
      Submodule.span O (Set.range fun j => P.bLie (x' j)) = P.wRec ((embO P.integers τ).comp (starRingEnd (𝓞 E))) ∧
      IsLatBasis C (P.latTQuot (σ := fun φ : E →+* C => embO P.integers φ) (isSplitting_embO P.integers) τ)
        (fun k => ∑ j, g k j • P.bLie (x j)) ∧
      IsLatBasis C (P.latTSub ((embO P.integers τ).comp (starRingEnd (𝓞 E)))) (fun k => ∑ j, g' k j • P.bLie (x' j)) ∧
      g.det ≠ 0 ∧ g'.det ≠ 0 ∧
      (∀ j, AvDefs.IsEig P.Gt P.oGt (embO P.integers τ) (x j)) ∧
      (∀ j, AvDefs.IsEig P.Gt P.oGt ((embO P.integers τ).comp (starRingEnd (𝓞 E))) (x' j)) ∧
      LinearIndependent C (fun j => P.bLie (x j)) ∧ LinearIndependent C (fun j => P.bLie (x' j)) ∧
      Submodule.span C (Set.range fun j => P.bLie (x j)) = P.eigW (embO P.integers τ) ∧
      Submodule.span C (Set.range fun j => P.bLie (x' j)) = P.eigW ((embO P.integers τ).comp (starRingEnd (𝓞 E)))

open Classical in

theorem hasSigFrames_of_rTau [StarRing (𝓞 E)] (P : Point ℓ v O (𝓞 E)) (hcok : CokernelBound P)
    (hW : P.W = Submodule.span C (Set.range P.bLie)) (rt : 𝓞 E) (τ : E →+* C) (hrt : τ ((star rt : 𝓞 E) : E) ≠ τ (rt : E))
    {p q : ℕ} (h : ∀ χ : 𝓞 E →+* O, AvDefs.rTau P.Gt P.oGt χ = if algebraMap O C (χ rt) = τ (rt : E) then p else q) :
    HasSigFrames P rt τ p q := by
  have hinj := bLie_injective P hcok
  have hp : AvDefs.rTau P.Gt P.oGt (embO P.integers τ) = p := by rw [h, algebraMap_embO, if_pos rfl]
  have hq : AvDefs.rTau P.Gt P.oGt ((embO P.integers τ).comp (starRingEnd (𝓞 E))) = q := by
    rw [h, RingHom.comp_apply, algebraMap_embO, starRingEnd_apply, if_neg hrt]
  obtain ⟨x, g, a1, a2, a3, a4, a5⟩ := exists_frame P hinj _ hp
    (P.fg_latTQuot (σ := fun φ : E →+* C => embO P.integers φ) (isSplitting_embO P.integers) τ)
    ((P.wRec_le_latTSub _).trans (P.latTSub_le_latTQuot (σ := fun φ : E →+* C => embO P.integers φ) _ τ))
  obtain ⟨x', g', b1, b2, b3, b4, b5⟩ := exists_frame P hinj _ hq (fg_inf P.integers P.fg_latT _) (P.wRec_le_latTSub _)
  refine ⟨fun φ => ?_, x, x', g, g', a3, b3, a5, b5, a4, b4, a1, b1, a2, b2, span_eq_eigW P hcok hW _ hp a1 a2,
    span_eq_eigW P hcok hW _ hq b1 b2⟩
  rw [HodgeTateEigenRank.finrank_eigW ℓ C v O _ P hcok hW, h, algebraMap_embO]

variable (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C)

end Main

end GlobalTheory.PointSig
end
end

section
set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.CompHt GlobalTheory.IndexIdeal
open scoped TensorProduct NNReal

namespace GlobalTheory.HTIndex

section Algebra

variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {v : Valuation C ℝ≥0}

omit [Module O U] [IsScalarTower O C U] in
theorem indep_comb {n : ℕ} {w : Fin n → U} (hw : LinearIndependent C w) {a : Matrix (Fin n) (Fin n) C}
    (ha : a.det ≠ 0) : LinearIndependent C fun i => ∑ j, a i j • w j :=
  (Matrix.linearIndependent_rows_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det a).2 ha.isUnit)).map'
    (Fintype.linearCombination C w)
    (LinearMap.ker_eq_bot.2 fun s t h => funext (Fintype.linearIndependent_iffₛ.1 hw s t h))

omit [Module O U] [IsScalarTower O C U] in
theorem eq_inv_comb {n : ℕ} (w : Fin n → U) {a : Matrix (Fin n) (Fin n) C} (ha : a.det ≠ 0) (i : Fin n) :
    w i = ∑ j, a⁻¹ i j • ∑ k, a j k • w k := by
  have h := comb_comb (x := fun i => ∑ j, a⁻¹ i j • ∑ k, a j k • w k) (y := fun j => ∑ k, a j k • w k) (z := w)
    (fun _ => rfl) (fun _ => rfl) i
  rw [Matrix.nonsing_inv_mul _ ha.isUnit] at h
  simpa [Matrix.one_apply] using h.symm

omit [Module O U] [IsScalarTower O C U] in
theorem span_comb {n : ℕ} (w : Fin n → U) {a : Matrix (Fin n) (Fin n) C} (ha : a.det ≠ 0) :
    Submodule.span C (Set.range fun i => ∑ j, a i j • w j) = Submodule.span C (Set.range w) :=
  le_antisymm
    (Submodule.span_le.2 (Set.range_subset_iff.2 fun _ => Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)))
    (Submodule.span_le.2 (Set.range_subset_iff.2 fun i => (eq_inv_comb w ha i).symm ▸ Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)))

theorem exists_hasIndex {n : ℕ} {w x : Fin n → U} (hw : LinearIndependent C w) {a : Matrix (Fin n) (Fin n) C}
    (ha : a.det ≠ 0) (hx : ∀ i, x i = ∑ j, a i j • w j) (hm : ∀ i, x i ∈ Submodule.span O (Set.range w)) :
    ∃ d : O, algebraMap O C d = a.det ∧
      HasIndex C n (Submodule.span O (Set.range w)) (Submodule.span O (Set.range x)) (Ideal.span {d}) := by
  obtain ⟨g, hg⟩ := exists_matrix (C := C) (Submodule.span_le.2 (Set.range_subset_iff.2 hm))
  have e : algebraMap O C g.det = a.det := by rw [RingHom.map_det, comb_inj hw hx hg]; rfl
  refine ⟨g.det, e, w, g, hw, rfl, ?_, fun h => ha (by rw [← e, h, map_zero]), rfl⟩
  congr 2
  funext i
  simp only [hg i, Matrix.map_apply, algebraMap_smul]

theorem exists_block_basis (hv : v.Integers O) {p q : ℕ} {L : Submodule O U} {u : Fin p → U} {u' : Fin q → U}
    {I : Ideal O} (hI : HasIndex C (p + q) L (Submodule.span O (Set.range u) ⊔ Submodule.span O (Set.range u')) I) :
    ∃ (g₁ : Matrix (Fin p) (Fin p) C) (g' : Matrix (Fin q) (Fin p) C) (g₂ : Matrix (Fin q) (Fin q) C) (d : O),
      LinearIndependent C u ∧ algebraMap O C d * (g₁.det * g₂.det) = 1 ∧ Ideal.span {d} = I ∧
      Submodule.span O (Set.range fun i => ∑ j, g₁ i j • u j) =
        L ⊓ (Submodule.span C (Set.range u)).restrictScalars O ∧
      Submodule.span O (Set.range fun i => ∑ j, g₁ i j • u j) ⊔
        Submodule.span O (Set.range fun i => ∑ j, g' i j • u j + ∑ j, g₂ i j • u' j) = L := by
  let e : Fin p ⊕ Fin q ≃ Fin (p + q) := finSumFinEquiv
  let b : Fin (p + q) → U := Sum.elim u u' ∘ e.symm
  have hb : Submodule.span O (Set.range b) = Submodule.span O (Set.range u) ⊔ Submodule.span O (Set.range u') := by
    rw [e.symm.surjective.range_comp, Set.Sum.elim_range, Submodule.span_union]
  have hle := hI.le
  obtain ⟨w, g₀, hw, hL, hL', hg₀, -⟩ := id hI
  have hd₀ : (g₀.map (algebraMap O C)).det ≠ 0 := fun h =>
    hg₀ (hv.hom_inj (by rw [RingHom.map_det, map_zero]; exact h))
  have hbw : Submodule.span C (Set.range b) = Submodule.span C (Set.range w) := by
    rw [← Submodule.span_span_of_tower O C, hb, ← hL', Submodule.span_span_of_tower, ← span_comb w hd₀]
    simp only [Matrix.map_apply, algebraMap_smul]
  have hbi : LinearIndependent C b := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hbw, finrank_span_eq_card hw]
  obtain ⟨g, g1, g2, g3⟩ := FlagBasis.exists_adapted_basis O C U v hv (p + q) L
    (hL ▸ Submodule.fg_span (Set.finite_range w)) b hbi fun j =>
      ⟨1, one_ne_zero, by rw [one_smul]; exact hle (hb ▸ Submodule.subset_span ⟨j, rfl⟩)⟩
  have hg : g.det ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular _ fun i j hij => g1 i j hij]
    exact Finset.prod_ne_zero_iff.2 fun i _ => g2 i
  have ht : Submodule.span O (Set.range fun i => ∑ j, g i j • b j) = L := by
    rw [g3.2, span_comb b hg, hbw, inf_eq_left, ← hL]
    exact Submodule.span_le_restrictScalars O C _
  obtain ⟨d, hd, hd'⟩ := hI.det hv.hom_inj ht hb (eq_inv_comb b hg)
  let G := g.submatrix e e
  have h12 : G.toBlocks₁₂ = 0 := Matrix.ext fun i j => g1 _ _ (by
    simp only [e, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega)
  have hdet : g.det = G.toBlocks₁₁.det * G.toBlocks₂₂.det := by
    rw [← Matrix.det_submatrix_equiv_self e, ← Matrix.det_fromBlocks_zero₁₂ _ G.toBlocks₂₁, ← h12,
      Matrix.fromBlocks_toBlocks]
  have hs : ∀ s, ∑ j, g (e s) j • b j = ∑ j, G s (.inl j) • u j + ∑ j, G s (.inr j) • u' j := fun s => by
    rw [← e.sum_comp, Fintype.sum_sum_type]
    simp [b, G]
  have hl : ∀ i, ∑ j, g (e (.inl i)) j • b j = ∑ j, G.toBlocks₁₁ i j • u j := fun i => by
    have : ∀ j, G (.inl i) (.inr j) = 0 := fun j => congrFun (congrFun h12 i) j
    simp only [hs, this, zero_smul, Finset.sum_const_zero, add_zero]
    rfl
  have hsup : Submodule.span O (Set.range fun i => ∑ j, G.toBlocks₁₁ i j • u j) ⊔
      Submodule.span O (Set.range fun i => ∑ j, G.toBlocks₂₁ i j • u j + ∑ j, G.toBlocks₂₂ i j • u' j) = L := by
    rw [← ht, ← e.surjective.range_comp, ← Submodule.span_union, ← Set.Sum.elim_range]
    congr 2
    funext s
    rcases s with i | i
    exacts [(hl i).symm, (hs (.inr i)).symm]
  have h1 : G.toBlocks₁₁.det ≠ 0 := left_ne_zero_of_mul (hdet ▸ hg)
  refine ⟨G.toBlocks₁₁, G.toBlocks₂₁, G.toBlocks₂₂, d, ?_, ?_, hd', le_antisymm (le_inf (le_sup_left.trans hsup.le) ?_) ?_,
    hsup⟩
  · simpa [b, Function.comp_def] using hbi.comp (e ∘ .inl) (e.injective.comp Sum.inl_injective)
  · rw [hd, ← hdet, Matrix.det_nonsing_inv_mul_det _ hg.isUnit]
  · rw [← span_comb u h1]
    exact Submodule.span_le_restrictScalars O C _
  · rintro x ⟨hx, hx'⟩
    rw [← span_comb u h1] at hx'
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 hx'
    have := (g3.sum_mem_iff (Sum.elim c 0 ∘ e.symm)).1 (by
      rw [← e.sum_comp, Fintype.sum_sum_type]
      simpa [hl] using hx)
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨o, ho⟩ := this (e (.inl i))
    have ho' : c i = algebraMap O C o := by simpa using ho.symm
    rw [ho', algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem index_mul_gram [FiniteDimensional C U] (hv : v.Integers O) {p q : ℕ} (B : U →ₗ[C] U →ₗ[C] C)
    {L S : Submodule O U} {W W' : Submodule C U} {u : Fin p → U} {u' z : Fin q → U} {I : Ideal O}
    (hI : HasIndex C (p + q) L (Submodule.span O (Set.range u) ⊔ Submodule.span O (Set.range u')) I)
    (hW : Module.finrank C W = p) (hW' : Module.finrank C W' = q) (hu : ∀ a, u a ∈ W) (hz : ∀ b, z b ∈ W')
    (hzS : ∀ b, z b ∈ S) (hS : ∀ y ∈ W', y ∈ S ↔ ∀ x ∈ L, ∃ c : O, algebraMap O C c = B x y)
    (horth : ∀ a b, B (u a) (z b) = 0) {G : Matrix (Fin q) (Fin q) O} (hG : G.det ≠ 0)
    (hGram : ∀ a b, B (u' a) (z b) = algebraMap O C (G a b)) :
    ∃ I₁ I₂ : Ideal O, HasIndex C p (L ⊓ W.restrictScalars O) (Submodule.span O (Set.range u)) I₁ ∧
      HasIndex C q (S ⊓ W'.restrictScalars O) (Submodule.span O (Set.range z)) I₂ ∧
      I₁ * Ideal.span {G.det} = I * I₂ := by
  obtain ⟨g₁, g', g₂, d, hui, hd, rfl, h₁, h₂⟩ := exists_block_basis hv hI
  have hne : g₁.det * g₂.det ≠ 0 := right_ne_zero_of_mul (hd ▸ one_ne_zero)
  have hg₁ := left_ne_zero_of_mul hne
  have hspan : ∀ {n : ℕ} {x : Fin n → U} {F : Submodule C U}, LinearIndependent C x → (∀ a, x a ∈ F) →
      Module.finrank C F = n → Submodule.span C (Set.range x) = F := fun hx hF hn =>
    Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 (Set.range_subset_iff.2 hF))
      (by rw [finrank_span_eq_card hx, Fintype.card_fin, hn])
  rw [hspan hui hu hW] at h₁
  obtain ⟨d₁, hd₁, hI₁⟩ := exists_hasIndex (O := O) (indep_comb hui hg₁) (Matrix.isUnit_nonsing_inv_det _ hg₁.isUnit).ne_zero
    (eq_inv_comb u hg₁) fun i => h₁.ge ⟨hI.le (Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)), hu i⟩
  rw [h₁] at hI₁
  have hGC : (G.map (algebraMap O C)).det = algebraMap O C G.det := (RingHom.map_det _ _).symm
  let Q := (g₂ * G.map (algebraMap O C)).transpose
  have hQd : Q.det = g₂.det * algebraMap O C G.det := by rw [Matrix.det_transpose, Matrix.det_mul, hGC]
  have hQ : Q.det ≠ 0 := hQd ▸ mul_ne_zero (right_ne_zero_of_mul hne) fun h => hG (hv.hom_inj (by rw [h, map_zero]))
  let t : Fin q → U := fun i => ∑ j, g' i j • u j + ∑ j, g₂ i j • u' j
  let x : Fin q → U := fun k => ∑ b, Q⁻¹ k b • z b
  have htz : ∀ j b, B (t j) (z b) = Q b j := fun j b => by
    simp only [t, map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, horth, hGram,
      smul_zero, Finset.sum_const_zero, zero_add]
    rfl
  have htx : ∀ j (c : Fin q → C), B (t j) (∑ k, c k • x k) = c j := fun j c => by
    have : ∀ k, B (t j) (x k) = (1 : Matrix _ _ C) k j := fun k => by
      rw [← Matrix.nonsing_inv_mul _ hQ.isUnit]
      simp [x, htz, Matrix.mul_apply]
    simp [this, Matrix.one_apply]
  have hxi : LinearIndependent C x := Fintype.linearIndependent_iff.2 fun c hc j => by rw [← htx j c, hc, map_zero]
  have hxW : ∀ k, x k ∈ W' := fun k => Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hz b)
  have hzx : ∀ b, z b = ∑ k, Q b k • x k := fun b => by
    have := eq_inv_comb z (Matrix.isUnit_nonsing_inv_det _ hQ.isUnit).ne_zero b
    rwa [Matrix.nonsing_inv_nonsing_inv _ hQ.isUnit] at this
  have hx : Submodule.span O (Set.range x) = S ⊓ W'.restrictScalars O := by
    refine le_antisymm (Submodule.span_le.2 (Set.range_subset_iff.2 fun k => ⟨(hS _ (hxW k)).2 fun l hl => ?_, hxW k⟩)) ?_
    · have : L ≤ (LinearMap.range (Algebra.linearMap O C)).comap ((B.flip (x k)).restrictScalars O) := by
        rw [← h₂]
        refine sup_le (Submodule.span_le.2 (Set.range_subset_iff.2 fun i => ⟨0, ?_⟩))
          (Submodule.span_le.2 (Set.range_subset_iff.2 fun i => ⟨(Pi.single k 1 : Fin q → O) i, ?_⟩))
        · simp [x, horth]
        · have := htx i (Pi.single k 1)
          simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
          exact Eq.trans (by simp [Pi.single_apply, apply_ite]) this.symm
      exact this hl
    · rintro y ⟨hy, hy'⟩
      have hy'' : y ∈ Submodule.span C (Set.range x) := (hspan hxi hxW hW').ge hy'
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 hy''
      refine Submodule.sum_mem _ fun i _ => ?_
      obtain ⟨o, ho⟩ := (hS _ hy').1 hy (t i) (h₂.le (Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)))
      rw [htx] at ho
      rw [← ho, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨d₂, hd₂, hI₂⟩ := exists_hasIndex (O := O) hxi hQ hzx fun b => hx.ge ⟨hzS b, hz b⟩
  rw [hx] at hI₂
  refine ⟨_, _, hI₁, hI₂, ?_⟩
  rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton]
  congr 2
  refine hv.hom_inj ?_
  rw [map_mul, map_mul, hd₁, hd₂, hQd, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, eq_inv_of_mul_eq_one_left hd]
  field_simp [right_ne_zero_of_mul hne]

theorem iSup_map_span {U U' : Type} [AddCommGroup U] [Module O U] [AddCommGroup U'] [Module O U'] {n : ℕ}
    (f : Fin n → (U →ₗ[O] U')) (y : U) :
    ⨆ a, (Submodule.span O {y}).map (f a) = Submodule.span O (Set.range fun a => f a y) := by
  simp only [Submodule.map_span, Set.image_singleton, Submodule.span_range_eq_iSup]

theorem val_det_frame (hv : v.Integers O) {U' : Type} [AddCommGroup U'] [Module C U'] [Module O U']
    [IsScalarTower O C U'] {n : ℕ} {La : Submodule O U} {F : Submodule C U} {La' : Submodule O U'} {F' : Submodule C U'}
    {f : Fin n → (U' →ₗ[C] U)} {d : O} (h : HasIndex C n (La ⊓ F.restrictScalars O)
      (⨆ a, (La' ⊓ F'.restrictScalars O).map ((f a).restrictScalars O)) (Ideal.span {d}))
    {x : Fin n → U} {g : Matrix (Fin n) (Fin n) C} (hg : g.det ≠ 0) (hx : Submodule.span C (Set.range x) = F)
    (hb : IsLatBasis C La fun i => ∑ j, g i j • x j) {y : Fin 1 → U'} {c : Matrix (Fin 1) (Fin 1) C} (hc : c.det ≠ 0)
    (hy : Submodule.span C (Set.range y) = F') (hb' : IsLatBasis C La' fun i => ∑ j, c i j • y j)
    {m : Matrix (Fin n) (Fin n) C} (hm : ∀ a, f a (y 0) = ∑ k, m a k • x k) :
    v c.det ^ n * v m.det = v g.det * v (algebraMap O C d) := by
  have e := hb.2
  have e' := hb'.2
  rw [span_comb x hg, hx] at e
  rw [span_comb y hc, hy, Set.range_unique] at e'
  rw [← e', iSup_map_span] at h
  have := h.val_det hv e rfl (a := c.det • (m * g⁻¹)) fun a => by
    have h1 := comb_comb hm (eq_inv_comb x hg) a
    simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, ← h1]
    simp
  rw [← this, Matrix.det_smul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Fintype.card_fin, ← map_pow,
    ← map_mul, ← map_mul]
  congr 1
  field_simp

end Algebra

section Points

variable {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type}
  [CommRing O] [Algebra O C] [Fact ¬IsUnit (ℓ : O)] [IsAdicComplete (Ideal.span {(ℓ : O)}) O] [Algebra ℤ_[ℓ] O]
  [Algebra ℤ_[ℓ] C] [IsScalarTower ℤ_[ℓ] O C] {Λ : Type} [CommRing Λ] [StarRing Λ]
  {J : Type} [DecidableEq J] {σ : J → Λ →+* O} (hs : IsSplitting (embC C σ)) (k : J)

theorem wHT_eq_of_rank_one (P : Point ℓ v O Λ) {y : P.V} (hy : Submodule.span O {y} = P.latTQuot hs k)
    (hW : Module.finrank C (P.eigW (σ k)) = 1) : y ∈ P.eigW (σ k) ∧ P.wHT hs k = Submodule.span O {y} := by
  have hle : P.eigW (σ k) ≤ Submodule.span C {y} := fun x hx => by
    obtain ⟨a, ha, h⟩ := P.exists_smul_mem_latT x
    have ha' : algebraMap O C a ≠ 0 := fun h0 => ha (P.integers.hom_inj (by rw [h0, map_zero]))
    have h1 : a • x ∈ Submodule.span O {y} := hy.ge (P.latTSub_le_latTQuot hs k
      ⟨h, by rw [← algebraMap_smul C]; exact (P.eigV (σ k)).smul_mem _ hx.2⟩)
    have h2 := Submodule.span_le_restrictScalars O C _ h1
    rw [← algebraMap_smul C] at h2
    exact (Submodule.smul_mem_iff _ ha').1 h2
  have he : P.eigW (σ k) = Submodule.span C {y} := Submodule.eq_of_le_of_finrank_le hle
    (hW ▸ (finrank_span_le_card _).trans (by simp))
  refine ⟨he.ge (Submodule.mem_span_singleton_self y), ?_⟩
  rw [Point.wHT, ← hy, he, inf_eq_left]
  exact Submodule.span_le_restrictScalars O C _

theorem exists_dual_of_rank_one (P : Point ℓ v O Λ) {y : P.V} (hy : Submodule.span O {y} = P.latTQuot hs k)
    (hW : Module.finrank C (P.eigW ((σ k).comp (starRingEnd Λ))) = 1) :
    ∃ z ∈ P.eigW ((σ k).comp (starRingEnd Λ)), P.pairV y z = 1 ∧
      P.latTSub ((σ k).comp (starRingEnd Λ)) ⊓ (P.eigW ((σ k).comp (starRingEnd Λ))).restrictScalars O =
        Submodule.span O {z} := by
  obtain ⟨⟨z₀, hz₀⟩, h0, hgen⟩ := finrank_eq_one_iff'.1 hW
  have hne : P.pairV y z₀ ≠ 0 := fun h => h0 (Subtype.ext (P.eq_of_pairV fun t => by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hy.ge ⟨_, P.one_tmul_mem_latT t, rfl⟩)
    have e := Model.pairV_proj P hs k (1 ⊗ₜ t) hz₀.2
    change _ = proj hs P.actV k (1 ⊗ₜ t) at hc
    rw [← hc, ← algebraMap_smul C, map_smul, LinearMap.smul_apply, h, smul_zero] at e
    change P.pairV z₀ _ = P.pairV 0 _
    rw [P.pairV_swap, ← e, neg_zero, map_zero, LinearMap.zero_apply]))
  have hz := (P.eigW _).smul_mem (P.pairV y z₀)⁻¹ hz₀
  have h1 : P.pairV y ((P.pairV y z₀)⁻¹ • z₀) = 1 := by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hne]
  have hgen' : ∀ x ∈ P.eigW ((σ k).comp (starRingEnd Λ)), ∃ c : C, c • (P.pairV y z₀)⁻¹ • z₀ = x := fun x hx => by
    obtain ⟨c, hc⟩ := hgen ⟨x, hx⟩
    exact ⟨c * P.pairV y z₀, by
      rw [smul_smul, mul_assoc, mul_inv_cancel₀ hne, mul_one]; exact congrArg Subtype.val hc⟩
  generalize (P.pairV y z₀)⁻¹ • z₀ = z at hz h1 hgen'
  refine ⟨z, hz, h1, le_antisymm ?_ ((Submodule.span_singleton_le_iff_mem _ _).2 ⟨?_, hz⟩)⟩
  · rintro x ⟨hx, hx'⟩
    obtain ⟨c, rfl⟩ := hgen' x hx'
    obtain ⟨o, ho⟩ := (Model.mem_latTSub_iff P hs k hx'.2).1 hx y (hy.le (Submodule.mem_span_singleton_self y))
    rw [map_smul, h1, smul_eq_mul, mul_one] at ho
    rw [← ho, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z)
  · refine (Model.mem_latTSub_iff P hs k hz.2).2 fun x hx => ?_
    obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 (hy.ge hx)
    exact ⟨o, by rw [← algebraMap_smul C, map_smul, LinearMap.smul_apply, h1, smul_eq_mul, mul_one]⟩

theorem index_points {A A' B : Point ℓ v O Λ} {p q : ℕ} (φ : Fin p → (A.V →ₗ[C] B.V)) (φ' : Fin q → (A'.V →ₗ[C] B.V))
    {I : Ideal O} (hI : HasIndex C (p + q) (B.latTQuot hs k)
      ((⨆ a, (A.latTQuot hs k).map ((φ a).restrictScalars O)) ⊔
        ⨆ b, (A'.latTQuot hs k).map ((φ' b).restrictScalars O)) I)
    {y : A.V} (hy : Submodule.span O {y} = A.latTQuot hs k) {y' : A'.V} (hy' : Submodule.span O {y'} = A'.latTQuot hs k)
    (hA : Module.finrank C (A.eigW (σ k)) = 1) (hA' : Module.finrank C (A'.eigW ((σ k).comp (starRingEnd Λ))) = 1)
    (hB : Module.finrank C (B.eigW (σ k)) = p) (hB' : Module.finrank C (B.eigW ((σ k).comp (starRingEnd Λ))) = q)
    (hφ : ∀ a, ∀ x ∈ A.eigW (σ k), φ a x ∈ B.eigW (σ k))
    (hφ' : ∀ b, ∀ x ∈ A'.eigW ((σ k).comp (starRingEnd Λ)), φ' b x ∈ B.eigW ((σ k).comp (starRingEnd Λ)))
    (hT : ∀ b, ∀ x ∈ A'.latTSub ((σ k).comp (starRingEnd Λ)), φ' b x ∈ B.latTSub ((σ k).comp (starRingEnd Λ)))
    {g : Matrix (Fin q) (Fin q) Λ} (hg : σ k g.det ≠ 0)
    (hGram : ∀ a b x z, B.pairV (φ' a x) (φ' b z) = A'.pairV (A'.actV (g a b) x) z)
    (horth : ∀ a b x z, B.pairV (φ a x) (φ' b z) = 0) :
    ∃ I₁ I₂ : Ideal O, HasIndex C p (B.wHT hs k) (⨆ a, (A.wHT hs k).map ((φ a).restrictScalars O)) I₁ ∧
      HasIndex C q
        (B.latTSub ((σ k).comp (starRingEnd Λ)) ⊓ (B.eigW ((σ k).comp (starRingEnd Λ))).restrictScalars O)
        (⨆ b, (A'.latTSub ((σ k).comp (starRingEnd Λ)) ⊓
          (A'.eigW ((σ k).comp (starRingEnd Λ))).restrictScalars O).map ((φ' b).restrictScalars O)) I₂ ∧
      I₁ * Ideal.span {σ k g.det} = I * I₂ := by
  obtain ⟨h1, h2⟩ := wHT_eq_of_rank_one hs k A hy hA
  obtain ⟨z, h3, h4, h5⟩ := exists_dual_of_rank_one hs k A' hy' hA'
  have h6 : y' ∈ A'.eigV (σ k) := eigQuotLat_le A'.actV hs k A'.latT (hy'.le (Submodule.mem_span_singleton_self y'))
  rw [← hy, ← hy', iSup_map_span, iSup_map_span] at hI
  rw [h2, h5, iSup_map_span, iSup_map_span, RingHom.map_det]
  refine index_mul_gram B.integers B.pairV hI hB hB' (fun a => hφ a y h1) (fun b => hφ' b z h3)
    (fun b => hT b z (h5.ge (Submodule.mem_span_singleton_self z)).1)
    (fun x hx => Model.mem_latTSub_iff B hs k hx.2) (fun a b => horth a b y z) (by rwa [← RingHom.map_det])
    fun a b => (hGram a b y' z).trans ?_
  rw [mem_eigenSub.1 h6, map_smul, LinearMap.smul_apply, h4, smul_eq_mul, mul_one]
  rfl

end Points

section Object

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CM GlobalTheory.FlatCM GlobalTheory.PointMap GlobalTheory.GramAt GlobalTheory.PointSig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ}

section At

variable {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type}
  [CommRing O] [Algebra O C] [Fact ¬IsUnit (ℓ : O)] [IsAdicComplete (Ideal.span {(ℓ : O)}) O] [Algebra ℤ_[ℓ] O]
  [Algebra ℤ_[ℓ] C] [IsScalarTower ℤ_[ℓ] O C]

omit [IsCMField E] in

theorem eigW_of_hasSigFrames [StarRing (𝓞 E)] {P : Point ℓ v O (𝓞 E)} {rt : 𝓞 E} {τ : E →+* C} {p q : ℕ}
    (h : HasSigFrames P rt τ p q) :
    (Module.finrank C (P.eigW (embO P.integers τ)) = p ∧
      P.eigW (embO P.integers τ) = Submodule.span C (P.wRec (embO P.integers τ))) ∧
    Module.finrank C (P.eigW ((embO P.integers τ).comp (starRingEnd (𝓞 E)))) = q ∧
      P.eigW ((embO P.integers τ).comp (starRingEnd (𝓞 E))) =
        Submodule.span C (P.wRec ((embO P.integers τ).comp (starRingEnd (𝓞 E)))) := by
  obtain ⟨-, x, x', g, g', h1, h2, -, -, -, -, -, -, h3, h4, h5, h6⟩ := h
  rw [← h1, ← h2, ← h5, ← h6, finrank_span_eq_card h3, finrank_span_eq_card h4, Submodule.span_span_of_tower,
    Submodule.span_span_of_tower]
  simp

omit [IsCMField E] [NumberField E] in
theorem map_mem_eigW [StarRing (𝓞 E)] {P P' : Point ℓ v O (𝓞 E)} {χ : 𝓞 E →+* O} (f : P.V →ₗ[C] P'.V)
    (h : P.eigW χ = Submodule.span C (P.wRec χ)) (h' : P'.eigW χ = Submodule.span C (P'.wRec χ))
    (hf : ∀ x ∈ P.wRec χ, f x ∈ P'.wRec χ) : ∀ x ∈ P.eigW χ, f x ∈ P'.eigW χ := by
  rw [h, h']
  exact fun x hx => (Submodule.span_le (p := (Submodule.span C (P'.wRec χ : Set P'.V)).comap f)).2
    (fun y hy => Submodule.subset_span (hf y hy)) hx

variable (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C) (X : CMObj H K ρ σ₁ p q)

open Classical in

def IsIndexRel (τ : E →+* C) (I : Ideal O) (δ : O) : Prop :=
  letI := H.starRing
  ∃ I₁ I₂ : Ideal O,
    HasIndex C p ((pointB hv ε i X).wHT (σ := fun φ : E →+* C => embO hv φ) (isSplitting_embO hv) τ)
      (⨆ a, ((pointA hv ε i X true).wHT (σ := fun φ : E →+* C => embO hv φ) (isSplitting_embO hv) τ).map
        ((phiVP hv ε i X a).restrictScalars O)) I₁ ∧
    HasIndex C q ((pointB hv ε i X).latTSub ((embO hv τ).comp (starRingEnd (𝓞 E))) ⊓
        ((pointB hv ε i X).eigW ((embO hv τ).comp (starRingEnd (𝓞 E)))).restrictScalars O)
      (⨆ b, ((pointA hv ε i X false).latTSub ((embO hv τ).comp (starRingEnd (𝓞 E))) ⊓
        ((pointA hv ε i X false).eigW ((embO hv τ).comp (starRingEnd (𝓞 E)))).restrictScalars O).map
          ((phiVQ hv ε i X b).restrictScalars O)) I₂ ∧
    I₁ * Ideal.span {δ} = I * I₂

variable {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)}

open Classical in

theorem isIndexRel_of_hasSigFrames (h : IsGram X gP gQ) (τ : E →+* C) : letI := H.starRing
    HasSigFrames (pointB hv ε i X) H.rt τ p q → HasSigFrames (pointA hv ε i X true) H.rt τ 1 0 →
    HasSigFrames (pointA hv ε i X false) H.rt τ 0 1 → ∀ I : Ideal O,
    HasIndex C (p + q) ((pointB hv ε i X).latTQuot (σ := fun φ : E →+* C => embO hv φ) (isSplitting_embO hv) τ)
      (quotImage hv ε i X (σ := fun φ : E →+* C => embO hv φ) (isSplitting_embO hv) τ) I →
    IsIndexRel hv ε i X τ I (embO hv τ gQ.det) := by
  letI := H.starRing
  intro hB hP hQ I hI
  obtain ⟨⟨b1, b2⟩, b3, b4⟩ := eigW_of_hasSigFrames hB
  obtain ⟨⟨p1, p2⟩, -⟩ := eigW_of_hasSigFrames hP
  obtain ⟨-, q1, q2⟩ := eigW_of_hasSigFrames hQ
  obtain ⟨y, -, hy⟩ := exists_basis_latTQuot_pure hv ε i X (σ := fun φ : E →+* C => embO hv φ)
    (isSplitting_embO hv) τ true
  obtain ⟨y', -, hy'⟩ := exists_basis_latTQuot_pure hv ε i X (σ := fun φ : E →+* C => embO hv φ)
    (isSplitting_embO hv) τ false
  rw [Set.range_unique] at hy hy'
  refine index_points (σ := fun φ : E →+* C => embO hv φ) (isSplitting_embO hv) τ (A := pointA hv ε i X true)
    (A' := pointA hv ε i X false) (B := pointB hv ε i X) (phiVP hv ε i X) (phiVQ hv ε i X) hI hy hy' p1 q1 b1 b3
    (fun a => map_mem_eigW _ p2 b2 (patV_mem_wRec (T := X.A true) hv ε i (X.lin (.inl a)) _))
    (fun a => map_mem_eigW _ q2 b4 (patV_mem_wRec (T := X.A false) hv ε i (X.lin (.inr a)) _))
    (fun a => patV_mem_latTSub (T := X.A false) hv ε i (X.lin (.inr a)) _) (fun h0 => (gram_det X h).2.1 ?_)
    (gram_V hv ε i X h).2.1 (gram_V hv ε i X h).2.2
  have h1 := algebraMap_embO hv τ gQ.det
  rw [show embO hv τ gQ.det = 0 from h0, map_zero, eq_comm, map_eq_zero] at h1
  exact RingOfIntegers.coe_injective h1

variable {hv ε i X} in
open Classical in

theorem IsIndexRel.val_det {τ : E →+* C} {n δ : O} (h : IsIndexRel hv ε i X τ (Ideal.span {n}) δ) : letI := H.starRing
    ∀ (x : Fin p → LieG (pointB hv ε i X).Gt) (x' : Fin q → LieG (pointB hv ε i X).Gt)
      (y : Fin 1 → LieG (pointA hv ε i X true).Gt) (y' : Fin 1 → LieG (pointA hv ε i X false).Gt)
      (g m : Matrix (Fin p) (Fin p) C) (g' m' : Matrix (Fin q) (Fin q) C) (c c' : Matrix (Fin 1) (Fin 1) C),
      g.det ≠ 0 → g'.det ≠ 0 → c.det ≠ 0 → c'.det ≠ 0 →
      Submodule.span C (Set.range fun j => (pointB hv ε i X).bLie (x j)) = (pointB hv ε i X).eigW (embO hv τ) →
      Submodule.span C (Set.range fun j => (pointB hv ε i X).bLie (x' j)) =
        (pointB hv ε i X).eigW ((embO hv τ).comp (starRingEnd (𝓞 E))) →
      Submodule.span C (Set.range fun j => (pointA hv ε i X true).bLie (y j)) =
        (pointA hv ε i X true).eigW (embO hv τ) →
      Submodule.span C (Set.range fun j => (pointA hv ε i X false).bLie (y' j)) =
        (pointA hv ε i X false).eigW ((embO hv τ).comp (starRingEnd (𝓞 E))) →
      IsLatBasis C ((pointB hv ε i X).latTQuot (σ := fun φ : E →+* C => embO hv φ) (isSplitting_embO hv) τ)
        (fun k => ∑ j, g k j • (pointB hv ε i X).bLie (x j)) →
      IsLatBasis C ((pointB hv ε i X).latTSub ((embO hv τ).comp (starRingEnd (𝓞 E))))
        (fun k => ∑ j, g' k j • (pointB hv ε i X).bLie (x' j)) →
      IsLatBasis C ((pointA hv ε i X true).latTQuot (σ := fun φ : E →+* C => embO hv φ) (isSplitting_embO hv) τ)
        (fun k => ∑ j, c k j • (pointA hv ε i X true).bLie (y j)) →
      IsLatBasis C ((pointA hv ε i X false).latTSub ((embO hv τ).comp (starRingEnd (𝓞 E))))
        (fun k => ∑ j, c' k j • (pointA hv ε i X false).bLie (y' j)) →
      (∀ a, phiVP hv ε i X a ((pointA hv ε i X true).bLie (y 0)) = ∑ k, m a k • (pointB hv ε i X).bLie (x k)) →
      (∀ a, phiVQ hv ε i X a ((pointA hv ε i X false).bLie (y' 0)) = ∑ k, m' a k • (pointB hv ε i X).bLie (x' k)) →
      v c.det ^ p * v m.det * v g'.det * v (algebraMap O C δ) =
        v (algebraMap O C n) * (v c'.det ^ q * v m'.det) * v g.det := by
  letI := H.starRing
  intro x x' y y' g m g' m' c c' a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  obtain ⟨I₁, I₂, h₁, h₂, e⟩ := h
  obtain ⟨-, g₁, -, -, -, -, rfl⟩ := id h₁
  obtain ⟨-, g₂, -, -, -, -, rfl⟩ := id h₂
  rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_eq_span_singleton] at e
  obtain ⟨u, hu⟩ := e
  have e := congrArg (fun z => v (algebraMap O C z)) hu
  simp only [map_mul, hv.one_of_isUnit u.isUnit, mul_one] at e
  rw [val_det_frame hv h₁ a1 b1 c1 a3 b3 c3 d1, val_det_frame hv h₂ a2 b2 c2 a4 b4 c4 d2]
  calc _ = v g.det * v g'.det * (v (algebraMap O C g₁.det) * v (algebraMap O C δ)) := by ring
    _ = _ := by rw [e]; ring

end At

end Object

end GlobalTheory.HTIndex
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.CompHt GlobalTheory.CM GlobalTheory.PointMap GlobalTheory.FlatCM GlobalTheory.PointSig GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CMKernel

variable {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type}
  [CommRing O] [Algebra O C] [hO : Fact ¬IsUnit (ℓ : O)] [IsAdicComplete (Ideal.span {(ℓ : O)}) O] [Algebra ℤ_[ℓ] O]
  [Algebra ℤ_[ℓ] C] [IsScalarTower ℤ_[ℓ] O C] {Λ : Type} [CommRing Λ] [StarRing Λ]

omit [IsAlgClosed C] in

theorem exists_factor (ℓ : ℕ) [Fact ℓ.Prime] [hO : Fact ¬IsUnit (ℓ : O)] [Algebra ℤ_[ℓ] O] (hv : v.Integers O) {R : Type} [CommRing R] [Module.Finite ℤ R] (j : R →+* O) :
    ∃ (T : Type) (_ : CommRing T) (_ : IsDomain T) (_ : IsLocalRing T) (_ : IsNoetherianRing T) (_ : CharZero T)
      (_ : IsAdicComplete (maximalIdeal T) T) (φ : R →+* T) (g : T →+* O), g.comp φ = j ∧ IsLocalHom g := by
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : CharZero O := (algebraMap O C).charZero
  let f : ℤ_[ℓ] ⊗[ℤ] R →ₐ[ℤ_[ℓ]] O := Algebra.TensorProduct.lift (Algebra.ofId _ _) j.toIntAlgHom fun _ _ => .all _ _
  haveI : Module.Finite ℤ_[ℓ] f.range := Module.Finite.of_surjective f.rangeRestrict.toLinearMap f.rangeRestrict_surjective
  haveI : IsLocalRing f.range := GlobalTheory.isLocalRing_of_domain_finite_padicInt ℓ _
  haveI : IsAdicComplete (maximalIdeal ℤ_[ℓ]) ℤ_[ℓ] := inferInstance
  refine ⟨f.range, inferInstance, inferInstance, inferInstance, IsNoetherianRing.of_finite ℤ_[ℓ] _, inferInstance,
    CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[ℓ] _,
    f.rangeRestrict.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom, f.range.val.toRingHom,
    RingHom.ext fun a => by simp [f], ?_⟩
  have h1 : (((maximalIdeal O).comap f.range.val.toRingHom).comap (algebraMap ℤ_[ℓ] f.range)).IsMaximal := by
    refine Ideal.IsPrime.isMaximal inferInstance fun h => ?_
    have : (ℓ : ℤ_[ℓ]) ∈ ((maximalIdeal O).comap f.range.val.toRingHom).comap (algebraMap ℤ_[ℓ] f.range) := by
      rw [Ideal.mem_comap, Ideal.mem_comap, map_natCast, map_natCast]
      exact hO.out
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at this
    exact (Fact.out : ℓ.Prime).ne_zero this
  have h2 := eq_maximalIdeal (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ h1)
  exact ⟨fun a ha => by_contra fun hn => (h2.ge hn) ha⟩

omit [Algebra ℤ_[ℓ] C] [IsScalarTower ℤ_[ℓ] O C] in

theorem htChar_goodPoint (hv : v.Integers O) (ε : Eps ℓ C) {R : Type} [CommRing R] [Module.Finite ℤ R] (j : R →+* O)
    (B : Out.PolAV (Sp R)) (o : B.OAct Λ) : HTChar ℓ v (goodPoint hv ε j B o).Gt := by
  obtain ⟨T, _, _, _, _, _, _, φ, g, hg, hloc⟩ := exists_factor ℓ hv j
  have hL := GlobalTheory.firstFiveLaws.1
  let B' := StrictPull.polPull B (spMap φ)
  obtain ⟨A, eA, hA, w, hw⟩ := GoodReductionUnif.exists_baseChange hL.polBaseChange (Out.jK T) B'
  obtain ⟨D, -, -, ⟨U⟩⟩ := exists_unif_abelianScheme hL.globalFns hL.secBaseChange hL.cube T (maximalIdeal T) B' A eA hA
    ⟨w, hw⟩
  letI := g.toAlgebra
  have e : spMap g ≫ spMap φ = spMap j := by rw [spMap_spMap, hg]
  have hπ : IsGrpPullback (goodPoint hv ε j B o).G B.A (spMap j) (pullback.fst _ _) := isGrpPullback_pullback B.A _
  have hc : IsGrpPullback B'.A B.A (spMap φ) (pullback.fst _ _) := isGrpPullback_pullback B.A _
  have w' : pullback.fst B.A.hom (spMap j) ≫ B.A.hom = ((goodPoint hv ε j B o).G.hom ≫ spMap g) ≫ spMap φ := by
    rw [Category.assoc, e]
    exact hπ.1.w
  have hπ' : IsGrpPullback (goodPoint hv ε j B o).G B'.A (spMap g) (hc.1.lift _ _ w') :=
    hc.cancel (hπ.congr e.symm (hc.1.lift_fst _ _ _).symm) (hc.1.lift_snd _ _ _)
  haveI := B'.isAb.comm
  haveI := B'.smoothDim
  haveI : Smooth B'.A.hom := SmoothOfRelativeDimension.smooth B'.g _
  obtain ⟨d, x, hx⟩ := Chart.univChartLoc B'.A
  obtain ⟨F, hF⟩ := (JetSer.lawSt_of JetSer.jetAlg (JetSer.repSt_of_jetAlgSt JetSer.jetAlg) _ B'.A d x hx).1
  obtain ⟨x', hx'⟩ := ChartCharacter.exists_isChartJ B'.A x hx F hF
  obtain ⟨N, u, hu, hspan⟩ := ChF.hodgeTate_inclusion_chart ℓ T (fun h => hO.out (by simpa using h.map g)) B'.A
    D A U.toUnifPre d F x' hx' C v O hv g hloc
  intro a ha
  exact FormalChar.smul_mem_htSpan (goodPoint hv ε j B o) hπ' hx F hF hu (hspan a (by rwa [map_natCast]))

variable (P : Point ℓ v O Λ)

theorem cokernelBound_of_htChar (h : HTChar ℓ v P.Gt) : CokernelBound P := fun f => by
  have h1 : v (algebraMap O C (ℓ : O)) ^ (ℓ - 1) ≤ v (ℓ : C) := by
    have hle := P.integers.map_le_one (ℓ : O)
    rw [map_natCast] at hle ⊢
    exact pow_le_of_le_one zero_le hle (by have := (Fact.out : ℓ.Prime).two_le; omega)
  have h2 := h (ℓ : O) h1 f.1 f.2
  rw [← (weilChar_surjective_and_map_range_al ℓ C v O Λ P).2] at h2
  obtain ⟨t, ht, e⟩ := h2
  rw [sq, mul_smul, ← show t = (ℓ : O) • f from Subtype.ext e]
  exact Submodule.smul_mem _ _ ht

theorem finrank_span (hcok : CokernelBound P) : Module.finrank C (Submodule.span C (Set.range P.bLie)) = P.A.g := by
  have h1 := (GlobalTheory.T.hodge_tate_kernel_annihilator ℓ C v O Λ P).2
  have h2 := GlobalTheory.T.finrank_W_eq_dimension ℓ C v O Λ P hcok
  omega

theorem W_eq_of_isotropic (hcok : CokernelBound P) (h : ∀ x ∈ Submodule.span C (Set.range P.bLie),
    ∀ y ∈ Submodule.span C (Set.range P.bLie), P.pairV x y = 0) : P.W = Submodule.span C (Set.range P.bLie) := by
  refine (Submodule.eq_of_le_of_finrank_eq (fun y hy => ?_)
    ((finrank_span P hcok).trans (GlobalTheory.T.finrank_W_eq_dimension ℓ C v O Λ P hcok).symm)).symm
  exact (KerPerp.mem_W_iff ℓ C v O Λ P y).2 fun x => h _ (Submodule.subset_span ⟨x, rfl⟩) y hy

theorem actV_mem (a : Λ) {x : P.V} (hx : x ∈ Submodule.span C (Set.range P.bLie)) :
    P.actV a x ∈ Submodule.span C (Set.range P.bLie) :=
  (Submodule.span_le (p := (Submodule.span C (Set.range P.bLie)).comap (P.actV a))).2
    (by rintro _ ⟨y, rfl⟩; exact Submodule.subset_span ⟨_, P.bLie_act a y⟩) hx

theorem isotropic_of_types (hcok : CokernelBound P) {J : Type} [Fintype J] [DecidableEq J] {σ : J → Λ →+* O}
    (hs : IsSplitting (embC C σ)) (a : Λ) (h : ∀ k l, AvDefs.rTau P.Gt P.oGt (σ k) ≠ 0 → AvDefs.rTau P.Gt P.oGt (σ l) ≠ 0 →
      algebraMap O C (σ k a) ≠ algebraMap O C (σ l (star a))) :
    ∀ x ∈ Submodule.span C (Set.range P.bLie), ∀ y ∈ Submodule.span C (Set.range P.bLie), P.pairV x y = 0 := by
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  haveI : IsFractionRing O C := P.integers.isFractionRing
  have hinj := bLie_injective P hcok
  have key : ∀ k, AvDefs.rTau P.Gt P.oGt (σ k) = 0 → ∀ x ∈ Submodule.span C (Set.range P.bLie),
      proj hs P.actV k x = 0 := fun k hk x hx => by
    have h1 : ∀ t : C ⊗[ℤ] Λ, tensorAction P.actV t x ∈ Submodule.span C (Set.range P.bLie) := fun t => by
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add s t hs ht => rw [map_add, LinearMap.add_apply]; exact add_mem hs ht
      | tmul c a => rw [tensorAction_tmul]; exact Submodule.smul_mem _ _ (actV_mem P a hx)
    have h2 : proj hs P.actV k x ∈ P.eigV (σ k) := proj_mem hs P.actV k x
    obtain ⟨s, hs0, z, hz⟩ := HodgeTateEigenRank.exists_smul_mem_of_mem_span (C := C) P.latLie
      (show proj hs P.actV k x ∈ _ from h1 _)
    have hs' : algebraMap O C s ≠ 0 := fun h => hs0 (P.integers.hom_inj (by rw [h, map_zero]))
    have h3 : P.bLie z ∈ P.eigV (σ k) := by
      rw [hz, ← algebraMap_smul C s]
      exact Submodule.smul_mem _ _ h2
    have h4 : AvDefs.IsEig P.Gt P.oGt (σ k) z := fun a => hinj (by
      rw [P.bLie_act, P.bLie_scale, mem_eigenSub.1 h3 a, RingHom.comp_apply, algebraMap_smul])
    obtain ⟨e, -, -, he⟩ := exists_basis_wRec P hinj (σ k) hk
    have h5 : P.bLie z ∈ P.wRec (σ k) := ⟨⟨z, h4⟩, rfl⟩
    rw [← he, Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot, hz, ← algebraMap_smul C s] at h5
    exact (smul_eq_zero.1 h5).resolve_left hs'
  intro x hx y hy
  rw [← sum_proj hs P.actV x, ← sum_proj hs P.actV y]
  simp only [map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : AvDefs.rTau P.Gt P.oGt (σ k) = 0
  · rw [key k hk x hx, map_zero, LinearMap.zero_apply]
  by_cases hl : AvDefs.rTau P.Gt P.oGt (σ l) = 0
  · rw [key l hl y hy, map_zero]
  exact Model.pairV_eq_zero P (proj_mem hs P.actV k x) (proj_mem hs P.actV l y) a (h k l hk hl)

theorem isotropic_of_sum {A A' B : Point ℓ v O Λ} {p q : ℕ} (φ : Fin p → (A.V →ₗ[C] B.V)) (φ' : Fin q → (A'.V →ₗ[C] B.V))
    (hA : CokernelBound A) (hA' : CokernelBound A') (hB : CokernelBound B) (hg : B.A.g = p * A.A.g + q * A'.A.g)
    (hφ : ∀ a x, ∃ z, B.bLie z = φ a (A.bLie x)) (hφ' : ∀ a x, ∃ z, B.bLie z = φ' a (A'.bLie x))
    (hinj : Function.Injective fun z : (Fin p → A.V) × (Fin q → A'.V) => ∑ k, φ k (z.1 k) + ∑ k, φ' k (z.2 k))
    {g : Matrix (Fin p) (Fin p) Λ} {g' : Matrix (Fin q) (Fin q) Λ}
    (h₁ : ∀ a b x y, B.pairV (φ a x) (φ b y) = A.pairV (A.actV (g a b) x) y)
    (h₂ : ∀ a b x y, B.pairV (φ' a x) (φ' b y) = A'.pairV (A'.actV (g' a b) x) y)
    (h₃ : ∀ a b x y, B.pairV (φ a x) (φ' b y) = 0)
    (iA : ∀ x ∈ Submodule.span C (Set.range A.bLie), ∀ y ∈ Submodule.span C (Set.range A.bLie), A.pairV x y = 0)
    (iA' : ∀ x ∈ Submodule.span C (Set.range A'.bLie), ∀ y ∈ Submodule.span C (Set.range A'.bLie), A'.pairV x y = 0) :
    ∀ x ∈ Submodule.span C (Set.range B.bLie), ∀ y ∈ Submodule.span C (Set.range B.bLie), B.pairV x y = 0 := by
  let S := Submodule.span C (Set.range A.bLie)
  let S' := Submodule.span C (Set.range A'.bLie)
  let F : ((Fin p → S) × (Fin q → S')) →ₗ[C] B.V :=
    (∑ k, φ k ∘ₗ S.subtype ∘ₗ LinearMap.proj k).coprod (∑ k, φ' k ∘ₗ S'.subtype ∘ₗ LinearMap.proj k)
  have hF : ∀ z, F z = ∑ k, φ k (z.1 k) + ∑ k, φ' k (z.2 k) := fun z => by simp [F]
  have hFi : Function.Injective F := fun z z' e => by
    have := @hinj (fun k => z.1 k, fun k => z.2 k) (fun k => z'.1 k, fun k => z'.2 k) ((hF z).symm.trans (e.trans (hF z')))
    exact Prod.ext (funext fun k => Subtype.ext (congrFun (congrArg Prod.fst this) k))
      (funext fun k => Subtype.ext (congrFun (congrArg Prod.snd this) k))
  have hr : LinearMap.range F = Submodule.span C (Set.range B.bLie) := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro _ ⟨z, rfl⟩
      rw [hF]
      refine add_mem (Submodule.sum_mem _ fun k _ => ?_) (Submodule.sum_mem _ fun k _ => ?_)
      · exact (Submodule.span_le (p := (Submodule.span C (Set.range B.bLie)).comap (φ k))).2
          (by rintro _ ⟨y, rfl⟩; exact Submodule.subset_span (hφ k y)) (z.1 k).2
      · exact (Submodule.span_le (p := (Submodule.span C (Set.range B.bLie)).comap (φ' k))).2
          (by rintro _ ⟨y, rfl⟩; exact Submodule.subset_span (hφ' k y)) (z.2 k).2
    · rw [LinearMap.finrank_range_of_inj hFi, finrank_span B hB, hg, Module.finrank_prod, Module.finrank_pi_fintype,
        Module.finrank_pi_fintype, finrank_span A hA, finrank_span A' hA']
      simp
  rw [← hr]
  rintro _ ⟨z, rfl⟩ _ ⟨w, rfl⟩
  have h₄ : ∀ a b x y, B.pairV (φ' a x) (φ b y) = 0 := fun a b x y => by rw [B.pairV_swap, h₃, neg_zero]
  have h₅ : ∀ a b, A.pairV (A.actV (g a b) (z.1 a)) (w.1 b) = 0 := fun a b => iA _ (actV_mem A _ (z.1 a).2) _ (w.1 b).2
  have h₆ : ∀ a b, A'.pairV (A'.actV (g' a b) (z.2 a)) (w.2 b) = 0 := fun a b =>
    iA' _ (actV_mem A' _ (z.2 a).2) _ (w.2 b).2
  simp only [hF, map_add, map_sum, LinearMap.add_apply, LinearMap.sum_apply, h₁, h₂, h₃, h₄, h₅, h₆,
    Finset.sum_const_zero, add_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C)

theorem cokernelBound_patPoint (T : PAT H (Sp (𝓞 K))) : letI := H.starRing; CokernelBound (patPoint hv ε i T) :=
  letI := H.starRing
  cokernelBound_of_htChar _ (htChar_goodPoint hv ε _ _ _)

open Classical in

theorem isotropic_pure (T : PAT H (Sp (𝓞 K))) {ρ : 𝓞 K} (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) {m n : ℕ} (hT : HasType H T.t.act ρ m n)
    (h0 : m = 0 ∨ n = 0) : letI := H.starRing
    ∀ x ∈ Submodule.span C (Set.range (patPoint hv ε i T).bLie),
      ∀ y ∈ Submodule.span C (Set.range (patPoint hv ε i T).bLie), (patPoint hv ε i T).pairV x y = 0 := by
  letI := H.starRing
  refine isotropic_of_types _ (cokernelBound_patPoint hv ε i T) (σ := fun φ : E →+* C => embO hv φ) (isSplitting_embO hv)
    H.rt fun k l hk hl e => ?_
  rw [rTau_patPoint hv ε i T hT] at hk hl
  rw [show star H.rt = -H.rt from EigDec.bar_rt H, map_neg, map_neg] at e
  have sq : ∀ k : E →+* C, algebraMap O C (embO hv k H.rt) ^ 2 = i (ρ : K) ^ 2 := fun k => by
    rw [← map_pow, ← map_pow, H.rt_sq, RingOfIntegers.coe_eq_algebraMap, ← map_pow, ← map_pow, hρ]
    simp
  have ne : i (ρ : K) ≠ 0 := fun h => by
    rw [map_eq_zero, RingOfIntegers.coe_eq_algebraMap, map_eq_zero_iff _ RingOfIntegers.coe_injective] at h
    exact H.d_prime.ne_zero (by simpa [h] using hρ)
  rcases h0 with rfl | rfl
  · have h1 := (sq_eq_sq_iff_eq_or_eq_neg.1 (sq k)).resolve_left fun h => hk (if_pos h)
    have h2 := (sq_eq_sq_iff_eq_or_eq_neg.1 (sq l)).resolve_left fun h => hl (if_pos h)
    rw [h1, h2, neg_neg] at e
    exact ne (neg_eq_self.1 e)
  · have h1 := by_contra fun h => hk (if_neg h)
    have h2 := by_contra fun h => hl (if_neg h)
    rw [h1, h2] at e
    exact ne (neg_eq_self.1 e.symm)

theorem hasSigFrames_of_isotropic (T : PAT H (Sp (𝓞 K))) {ρ : 𝓞 K} {m n : ℕ} (hT : HasType H T.t.act ρ m n)
    (τ : E →+* C) (hτ : τ (H.rt : E) = i (ρ : K)) : letI := H.starRing
    (∀ x ∈ Submodule.span C (Set.range (patPoint hv ε i T).bLie),
      ∀ y ∈ Submodule.span C (Set.range (patPoint hv ε i T).bLie), (patPoint hv ε i T).pairV x y = 0) →
    HasSigFrames (patPoint hv ε i T) H.rt τ m n := by
  letI := H.starRing
  intro h
  refine hasSigFrames_of_rTau _ (cokernelBound_patPoint hv ε i T)
    (W_eq_of_isotropic _ (cokernelBound_patPoint hv ε i T) h) H.rt τ (fun h0 => conj_rt_ne H ?_) fun χ => ?_
  · rw [← H.bar_eq]
    exact τ.injective h0
  · rw [hτ]
    exact rTau_patPoint hv ε i T hT χ

theorem hasSigFrames_of_isGram {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ} (X : CMObj H K ρ σ₁ p q)
    {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)} (h : IsGram X gP gQ) (τ : E →+* C)
    (hτ : τ (H.rt : E) = i (ρ : K)) : letI := H.starRing
    HasSigFrames (pointB hv ε i X) H.rt τ p q ∧ HasSigFrames (pointA hv ε i X true) H.rt τ 1 0 ∧
      HasSigFrames (pointA hv ε i X false) H.rt τ 0 1 := by
  letI := H.starRing
  have iP := isotropic_pure hv ε i _ X.ρ_sq X.typeP (.inr rfl)
  have iQ := isotropic_pure hv ε i _ X.ρ_sq X.typeM (.inl rfl)
  obtain ⟨g₁, g₂, g₃⟩ := GramAt.gram_V hv ε i X h
  obtain ⟨d₁, d₂, -⟩ := GramAt.dims X
  refine ⟨hasSigFrames_of_isotropic hv ε i _ X.typeB τ hτ ?_, hasSigFrames_of_isotropic hv ε i _ X.typeP τ hτ iP,
    hasSigFrames_of_isotropic hv ε i _ X.typeM τ hτ iQ⟩
  refine isotropic_of_sum (A := pointA hv ε i X true) (A' := pointA hv ε i X false) (B := pointB hv ε i X)
    (phiVP hv ε i X) (phiVQ hv ε i X) (cokernelBound_patPoint hv ε i _) (cokernelBound_patPoint hv ε i _)
    (cokernelBound_patPoint hv ε i _) ?_ (fun a x => ⟨_, (patV_bLie (T := X.A true) hv ε i (X.lin (.inl a)) x).symm⟩)
    (fun a x => ⟨_, (patV_bLie (T := X.A false) hv ε i (X.lin (.inr a)) x).symm⟩)
    (GramAt.sumV_bijective hv ε i X).1 g₁ g₂ g₃ iP iQ
  change X.B.g = p * (X.A true).g + q * (X.A false).g
  rw [d₂, d₁, d₁]
  ring

end GlobalTheory.CMKernel
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open scoped TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.CompHt GlobalTheory.CM GlobalTheory.PointMap GlobalTheory.FlatCM GlobalTheory.IndexIdeal GlobalTheory.HTIndex GlobalTheory.PointSig
open GlobalTheory.LieIndex GlobalTheory.HTLat.OmegaRank

namespace GlobalTheory.CMIdeal

theorem ideal_eq_of_map_eq {K : Type} [Field K] [NumberField K] {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (h : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (i : K →+* ℂ_[ℓ]), ∃ d : 𝓞_ℂ_[ℓ],
      I.map (embO (PadicComplexInt.integers ℓ) i) = Ideal.span {d} ∧
      J.map (embO (PadicComplexInt.integers ℓ) i) = Ideal.span {d}) : I = J := by
  have key : ∀ P : Ideal (𝓞 K), Prime P → emultiplicity P I = emultiplicity P J := fun P hP => by
    let 𝔭 : HeightOneSpectrum (𝓞 K) := ⟨P, Ideal.isPrime_of_prime hP, hP.ne_zero⟩
    obtain ⟨ℓ, hℓ, hm⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 K) ∈ P := by
      have h0 : Ideal.absNorm P ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 hP.ne_zero
      have h1 := Ideal.absNorm_mem P
      rw [← Nat.prod_primeFactorsList h0, Nat.cast_list_prod, ← Ideal.Quotient.eq_zero_iff_mem, map_list_prod] at h1
      haveI := 𝔭.isPrime
      haveI : IsDomain (𝓞 K ⧸ P) := Ideal.Quotient.isDomain 𝔭.asIdeal
      obtain ⟨_, h2, h3⟩ := List.mem_map.1 (List.prod_eq_zero_iff.1 h1)
      obtain ⟨ℓ, h4, rfl⟩ := List.mem_map.1 h2
      exact ⟨ℓ, Nat.prime_of_mem_primeFactorsList h4, Ideal.Quotient.eq_zero_iff_mem.1 h3⟩
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    obtain ⟨i, he, hi⟩ := GlobalTheory.PrimeEmbedding.exists_embedding_norm_eq K 𝔭 ℓ hm
    obtain ⟨d, h1, h2⟩ := h ℓ i
    have e := (norm_of_map_eq_span he hi (algebraMap_embO _ i) hI h1).symm.trans
      (norm_of_map_eq_span he hi (algebraMap_embO _ i) hJ h2)
    have hℓ' : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.one_lt
    have he' : (Formalism.BasicNotions.vAdd 𝔭 (ℓ : K) : ℝ) ≠ 0 := by exact_mod_cast he.ne'
    have e' := (Real.strictMono_rpow_of_base_gt_one hℓ').injective e
    rw [neg_inj, div_left_inj' he', Nat.cast_inj] at e'
    rw [(FiniteMultiplicity.of_prime_left hP hI).emultiplicity_eq_multiplicity,
      (FiniteMultiplicity.of_prime_left hP hJ).emultiplicity_eq_multiplicity]
    exact congrArg _ e'
  exact le_antisymm
    (Ideal.le_of_dvd ((UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hJ).2 fun P hP => (key P hP).ge))
    (Ideal.le_of_dvd ((UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hI).2 fun P hP => (key P hP).le))

theorem cancel_shift {p q : ℕ} {κ₁ κ₂ : ℝ} {g g' c c' a b : ℝ≥0} (hg : g ≠ 0) (hg' : g' ≠ 0) (hc : c ≠ 0) (hc' : c' ≠ 0)
    (h₀ : Real.log g - Real.log g' = p * κ₁ + q * κ₂) (h₁ : Real.log c = κ₁) (h₂ : -Real.log c' = κ₂)
    (h : c ^ p * g' * a = c' ^ q * g * b) : a = b := by
  have e : c ^ p * g' = c' ^ q * g := by
    refine NNReal.coe_injective (Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity)) ?_)
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_pow]
    subst h₁ h₂
    linarith
  rw [e] at h
  exact mul_left_cancel₀ (mul_ne_zero (pow_ne_zero _ hc') hg) h

theorem exists_matrix_of_mem {O C U : Type} [CommRing O] [Field C] [Algebra O C] [AddCommGroup U] [Module C U]
    [Module O U] [IsScalarTower O C U] {n : ℕ} {x u : Fin n → U} (h : ∀ a, u a ∈ Submodule.span O (Set.range x)) :
    ∃ m : Matrix (Fin n) (Fin n) C, ∀ a, u a = ∑ k, m a k • x k := by
  choose m hm using fun a => (Submodule.mem_span_range_iff_exists_fun C).1 (Submodule.span_le_restrictScalars O C _ (h a))
  exact ⟨m, fun a => (hm a).symm⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ} {X : CMObj H K ρ σ₁ p q} {FP : GenFib (X.A true).pol}
  {FQ : GenFib (X.A false).pol} {FB : GenFib X.B.pol}
  {MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))} {MQ : Fin q → ((Fin FQ.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))}
  {τ : 𝓞 E →+* 𝓞 K}

section At

variable {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type}
  [CommRing O] [Algebra O C] [Fact ¬IsUnit (ℓ : O)] [IsAdicComplete (Ideal.span {(ℓ : O)}) O] [Algebra ℤ_[ℓ] O]
  [Algebra ℤ_[ℓ] C] [IsScalarTower ℤ_[ℓ] O C] (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C)

open Classical in

theorem map_eq_at (hD : IsDiffs FP FQ FB MP MQ) (hτ : τ H.rt = ρ) {φ : E →+* C} (hφ : embO hv φ = (embO hv i).comp τ)
    {n δ : O} (hR : IsIndexRel hv ε i X φ (Ideal.span {n}) δ) {κ₁ κ₂ : ℝ} : letI := H.starRing
    HasSigFrames (pointB hv ε i X) H.rt φ p q → HasSigFrames (pointA hv ε i X true) H.rt φ 1 0 →
    HasSigFrames (pointA hv ε i X false) H.rt φ 0 1 →
    (∀ (P : Point ℓ v O (𝓞 E)) (p q : ℕ),
      (∀ ψ : E →+* C, Module.finrank C (P.eigW (embO P.integers ψ)) = if ψ (H.rt : E) = φ (H.rt : E) then p else q) →
      ∀ (x : Fin p → LieG P.Gt) (x' : Fin q → LieG P.Gt) (g : Matrix (Fin p) (Fin p) C) (g' : Matrix (Fin q) (Fin q) C),
        Submodule.span O (Set.range fun i => P.bLie (x i)) = P.wRec (embO P.integers φ) →
        Submodule.span O (Set.range fun i => P.bLie (x' i)) = P.wRec ((embO P.integers φ).comp (starRingEnd (𝓞 E))) →
        IsLatBasis C (P.latTQuot (σ := fun φ : E →+* C => embO P.integers φ) (isSplitting_embO P.integers) φ)
          (fun i => ∑ j, g i j • P.bLie (x j)) →
        IsLatBasis C (P.latTSub ((embO P.integers φ).comp (starRingEnd (𝓞 E)))) (fun i => ∑ j, g' i j • P.bLie (x' j)) →
        Real.log (v g.det) - Real.log (v g'.det) = p * κ₁ + q * κ₂) →
    ∃ d : O, (idx K p (FB.eigLat X.B.t.act τ) (subP FP FB MP τ)).map (embO hv i) * Ideal.span {δ} = Ideal.span {d} ∧
      Ideal.span {n} * (idx K q (FB.eigLat X.B.t.act (τ.comp (H.bar : 𝓞 E →+* 𝓞 E)))
        (subQ FQ FB MQ (τ.comp (H.bar : 𝓞 E →+* 𝓞 E)))).map (embO hv i) = Ideal.span {d} := by
  letI := H.starRing
  rintro ⟨b0, x, x', g, g', b1, b2, b3, b4, b5, b6, -, -, b7, b8, b9, b10⟩
    ⟨p0, y, y₀, c, c₀, p1, p2, p3, p4, p5, -, -, -, -, -, p9, -⟩
    ⟨q0, z₀, z, e₀, e, q1, q2, q3, q4, -, q6, -, -, -, -, -, q10⟩ hS
  have sB := hS _ p q b0 x x' g g' b1 b2 b3 b4
  have sP := hS _ 1 0 p0 y y₀ c c₀ p1 p2 p3 p4
  have sQ := hS _ 0 1 q0 z₀ z e₀ e q1 q2 q3 q4
  simp only [Matrix.det_isEmpty, map_one, NNReal.coe_one, Real.log_one, sub_zero, zero_sub, Nat.cast_one, Nat.cast_zero,
    one_mul, zero_mul, add_zero, zero_add] at sP sQ
  obtain ⟨m, hm⟩ := exists_matrix_of_mem (C := C) fun a => b1.ge (patV_mem_wRec (T := X.A true) hv ε i (X.lin (.inl a)) _ _
    (p1.le (Submodule.subset_span ⟨0, rfl⟩)))
  obtain ⟨m', hm'⟩ := exists_matrix_of_mem (C := C) fun a => b2.ge (patV_mem_wRec (T := X.A false) hv ε i
    (X.lin (.inr a)) _ _ (q2.le (Submodule.subset_span ⟨0, rfl⟩)))
  have e₁ := hR.val_det x x' y z g m g' m' c e b5 b6 p5 q6 b9 b10 p9 q10 b3 b4 p3 q4 hm hm'
  obtain ⟨-, hP, hQ⟩ := lie_index hv ε i hD hτ
  rw [Set.range_unique] at p1 q2
  obtain ⟨d₁, hd₁, f₁⟩ := hP _ hφ x (fun _ => y 0) m b7 b1 (fun _ => p1) hm
  obtain ⟨d₂, hd₂, f₂⟩ := hQ ((embO hv φ).comp (starRingEnd (𝓞 E))) (by rw [hφ]; rfl) x' (fun _ => z 0) m' b8 b2
    (fun _ => q2) hm'
  have e₂ : v (algebraMap O C (d₁ * δ)) = v (algebraMap O C (n * d₂)) := by
    refine cancel_shift ((map_ne_zero v).2 b5) ((map_ne_zero v).2 b6) ((map_ne_zero v).2 p5) ((map_ne_zero v).2 q6)
      sB sP sQ ?_
    rw [map_mul, map_mul, map_mul, map_mul, hd₁, hd₂]
    calc _ = _ := by ring
      _ = _ := e₁
      _ = _ := by ring
  refine ⟨d₁ * δ, by rw [f₁, Ideal.span_singleton_mul_span_singleton], ?_⟩
  rw [f₂, Ideal.span_singleton_mul_span_singleton]
  exact le_antisymm (Ideal.span_singleton_le_span_singleton.2 (hv.le_iff_dvd.1 e₂.ge))
    (Ideal.span_singleton_le_span_singleton.2 (hv.le_iff_dvd.1 e₂.le))

end At

theorem ideal_of_frames (hS : PlaceShiftSt) (hH : GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H) (X : CMObj H K ρ σ₁ p q)
    {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)} (h : IsGram X gP gQ)
    (hF : ∀ (ℓ : ℕ) [Fact ℓ.Prime] [IsAdicComplete (Ideal.span {(ℓ : 𝓞_ℂ_[ℓ])}) 𝓞_ℂ_[ℓ]] (ε : Eps ℓ ℂ_[ℓ])
      (i : K →+* ℂ_[ℓ]) (τ : E →+* ℂ_[ℓ]), τ (H.rt : E) = i (ρ : K) →
      letI := H.starRing; letI := algPadicInt ℓ; letI := algPadicField ℓ; haveI := towerPadic ℓ; haveI := factPadic ℓ
      HasSigFrames (pointB (PadicComplexInt.integers ℓ) ε i X) H.rt τ p q ∧
        HasSigFrames (pointA (PadicComplexInt.integers ℓ) ε i X true) H.rt τ 1 0 ∧
        HasSigFrames (pointA (PadicComplexInt.integers ℓ) ε i X false) H.rt τ 0 1) :
    ∃ 𝔫 : Ideal (𝓞 E), 𝔫 * 𝔫.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {gP.det * gQ.det} ∧
      ∀ (FP : GenFib (X.A true).pol) (FQ : GenFib (X.A false).pol) (FB : GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)))
        (MQ : Fin q → ((Fin FQ.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))), IsDiffs FP FQ FB MP MQ →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ →
          idx K p (FB.eigLat X.B.t.act τ) (subP FP FB MP τ) * Ideal.span {τ gQ.det} =
            𝔫.map τ * idx K q (FB.eigLat X.B.t.act (τ.comp (H.bar : 𝓞 E →+* 𝓞 E)))
              (subQ FQ FB MQ (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) := by
  obtain ⟨𝔫, h1, h2⟩ := index_ideal X h
  refine ⟨𝔫, h1, fun FP FQ FB MP MQ hD τ hτ => ?_⟩
  obtain ⟨n1, n2⟩ := idx_sub_ne_bot hD hτ
  obtain ⟨g1, g2, -⟩ := GlobalTheory.GramAt.gram_det X h
  have hinj : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra h0
    have h := Ideal.absNorm_mem (RingHom.ker τ)
    rw [RingHom.mem_ker, map_natCast, Nat.cast_eq_zero] at h
    exact h0 (Ideal.absNorm_eq_zero_iff.1 h)
  have h𝔫 : 𝔫 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h1
    exact mul_ne_zero g1 g2 h1
  refine ideal_eq_of_map_eq (mul_ne_zero n1 (Ideal.span_singleton_eq_bot.not.2 ((map_ne_zero_iff τ hinj).2 g2)))
    (mul_ne_zero ((Ideal.map_eq_bot_iff_of_injective hinj).not.2 h𝔫) n2) fun ℓ _ i => ?_
  letI := H.starRing; letI := algPadicInt ℓ; letI := algPadicField ℓ; haveI := towerPadic ℓ; haveI := factPadic ℓ
  haveI := PadicComplexHost.isAdicComplete ℓ
  obtain ⟨ε⟩ : Nonempty (Eps ℓ ℂ_[ℓ]) := inferInstance
  obtain ⟨φ, hφ, hI⟩ := h2 ℓ ε i τ
  have hrt : φ (H.rt : E) = i (ρ : K) := by
    rw [← algebraMap_embO (PadicComplexInt.integers ℓ) φ, hφ, RingHom.comp_apply, hτ, algebraMap_embO]
  obtain ⟨fB, fP, fQ⟩ := hF ℓ ε i φ hrt
  have hR := isIndexRel_of_hasSigFrames (PadicComplexInt.integers ℓ) ε i X h φ fB fP fQ _ hI
  obtain ⟨-, n, -, -, -, -, hn⟩ := hI
  obtain ⟨κ₁, κ₂, hκ⟩ := PlaceShiftModel.pointShiftSt_of_placeShiftSt hS E H hH ℓ φ
  rw [← hn] at hR
  have hn' : ∀ x : ℂ_[ℓ], ‖x‖ = ((Valued.v x : ℝ≥0) : ℝ) := fun x => by
    rw [PadicComplex.norm_eq_norm, Valued.v.norm_def, PadicComplex.RankOne.hom_eq_embedding,
      Valuation.embedding_restrict]
  obtain ⟨d, e₁, e₂⟩ := map_eq_at (PadicComplexInt.integers ℓ) ε i hD hτ hφ hR fB fP fQ
    fun P p q a x x' g g' b c d e => by rw [← hn', ← hn']; exact hκ P p q a x x' g g' b c d e
  refine ⟨d, ?_, ?_⟩
  · rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton, ← e₁, hφ]
    rfl
  · rw [Ideal.map_mul, Ideal.map_map, ← hn, e₂]

theorem idealSt_of_placeShiftSt : PlaceShiftSt → IdealSt := fun hS _ _ _ _ H hH _ _ _ _ _ _ _ X _ _ h =>
  ideal_of_frames hS hH X h fun ℓ _ _ ε i τ hτ => by
    letI := algPadicInt ℓ; letI := algPadicField ℓ; haveI := towerPadic ℓ; haveI := factPadic ℓ
    exact CMKernel.hasSigFrames_of_isGram _ ε i X h τ hτ

end GlobalTheory.CMIdeal
end
end

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_from_place_shift : PlaceShiftSt → IdealSt := by
  atlas_forward_decl GlobalTheory.CMIdeal.idealSt_of_placeShiftSt
end
