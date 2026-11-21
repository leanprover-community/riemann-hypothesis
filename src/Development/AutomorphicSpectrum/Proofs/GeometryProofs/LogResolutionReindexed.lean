import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemAbLocusIff
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionCompatiblePullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInhab
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFourth
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGenFibreChartDeg
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartScalingIndep
import GroundTheory.HeightsAndTheta.Heights.Intersections.PAdjoinIndepRelfinrank
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsPowOfMemCellSec
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicElementHomogRelation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB

section
section
namespace GlobalTheory.CompanionTheory.Ggeo

theorem blockProjection_genericPoints_good : GroundTheory.Heights₂.Heights.Inter.GenericPointsAvoidBadLocus.Statement :=
  GlobalTheory.CompanionTheory.Ar.PB.BaseCount.generic_points_good_for_intersection

end GlobalTheory.CompanionTheory.Ggeo
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_points_good_statement : GroundTheory.Heights₂.Heights.Inter.GenericPointsAvoidBadLocus.Statement := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ggeo.blockProjection_genericPoints_good
end

section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg.GenFib

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

section Top

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [CharZero Ω]

theorem blockFnField_eq_top (y : (Σ k, J k) → Ω) (c : ∀ k, J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hb : Birational y) : blockFnField y = ⊤ := by
  have hy : ∀ f : MRing J,
      aeval (GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RowSecGlue.ratioPt y c) f ∈ blockFnField y := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, aeval_X]
      exact mul_mem hp (IntermediateField.subset_adjoin _ _ ⟨i, ⟨i.1, c i.1⟩, rfl, rfl⟩)
  refine eq_top_iff.2 fun s _ => ?_
  obtain ⟨d, g, h, hg, hh, hne, e⟩ := hb s
  have eg := GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RowSecGlue.aeval_eq_ratioPt y c hc hg
  have eh := GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RowSecGlue.aeval_eq_ratioPt y c hc hh
  have hU : (∏ k, y ⟨k, c k⟩ ^ d k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  rw [eh] at hne
  have hH := left_ne_zero_of_mul hne
  rw [eg, eh, ← _root_.mul_assoc] at e
  have e2 := mul_right_cancel₀ hU e
  have : s = aeval (GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RowSecGlue.ratioPt y c) g /
      aeval (GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RowSecGlue.ratioPt y c) h := by
    rw [e2]; field_simp
  rw [this]
  exact div_mem (hy g) (hy h)

end Top

section Gen

theorem exists_quot_of_mem_adjoin {L I : Type} [Field L] [CharZero L] (z : I → L) {c : L}
    (hc : c ∈ IntermediateField.adjoin ℚ (Set.range z)) :
    ∃ f g : MvPolynomial I ℤ, aeval z g ≠ 0 ∧ c = aeval z f / aeval z g := by
  induction hc using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact ⟨X p, 1, by simp, by simp⟩
  | algebraMap r =>
    refine ⟨C r.num, C (r.den : ℤ), by simp, ?_⟩
    simp [Rat.cast_def]
  | add x y _ _ hx hy =>
    obtain ⟨f₁, g₁, h₁, rfl⟩ := hx
    obtain ⟨f₂, g₂, h₂, rfl⟩ := hy
    refine ⟨f₁ * g₂ + f₂ * g₁, g₁ * g₂, by simpa using ⟨h₁, h₂⟩, ?_⟩
    simp only [map_add, map_mul]
    field_simp
  | inv x _ hx =>
    obtain ⟨f, g, h, rfl⟩ := hx
    by_cases h0 : aeval z f = 0
    · exact ⟨0, 1, by simp, by simp [h0]⟩
    · exact ⟨g, f, h0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨f₁, g₁, h₁, rfl⟩ := hx
    obtain ⟨f₂, g₂, h₂, rfl⟩ := hy
    refine ⟨f₁ * f₂, g₁ * g₂, by simpa using ⟨h₁, h₂⟩, ?_⟩
    simp only [map_mul]
    field_simp

end Gen

section Point

variable {K : Type} {J : K → Type} {Ω : Type} [Field Ω]

def Fn (K Ω : Type) [Field Ω] : Type := FractionRing (MvPolynomial K Ω)

instance : Field (Fn K Ω) := inferInstanceAs (Field (FractionRing (MvPolynomial K Ω)))

def emb (K Ω : Type) [Field Ω] : MvPolynomial K Ω →+* Fn K Ω :=
  algebraMap (MvPolynomial K Ω) (FractionRing (MvPolynomial K Ω))

theorem emb_injective : Function.Injective (emb K Ω) :=
  IsFractionRing.injective (MvPolynomial K Ω) (FractionRing (MvPolynomial K Ω))

def cst (K Ω : Type) [Field Ω] : Ω →+* Fn K Ω := (emb K Ω).comp C

def tv (Ω : Type) [Field Ω] (k : K) : Fn K Ω := emb K Ω (X k)

theorem tv_ne_zero (k : K) : tv Ω k ≠ 0 := by
  rw [tv, Ne, map_eq_zero_iff _ emb_injective]
  exact X_ne_zero k

instance [CharZero Ω] : CharZero (Fn K Ω) := charZero_of_injective_ringHom (cst K Ω).injective

def xPt (y : (Σ k, J k) → Ω) : (Σ k, J k) → Fn K Ω := fun p => cst K Ω (y p) * tv Ω p.1

theorem xPt_ne_zero {y : (Σ k, J k) → Ω} {p : Σ k, J k} (h : y p ≠ 0) : xPt y p ≠ 0 :=
  mul_ne_zero ((map_ne_zero _).2 h) (tv_ne_zero _)

theorem xPt_div_xPt (y : (Σ k, J k) → Ω) {p q : Σ k, J k} (h : p.1 = q.1) :
    xPt y p / xPt y q = cst K Ω (y p / y q) := by
  rw [xPt, xPt, h, mul_div_mul_right _ _ (tv_ne_zero _), map_div₀]

variable [∀ k, Fintype (J k)] [Fintype K]

theorem aeval_xPt (y : (Σ k, J k) → Ω) (f : MRing J) :
    aeval (xPt y) f = emb K Ω (mConeMap y f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp [map_mul, hp, mConeMap, xPt, cst, tv]

theorem aeval_xPt_eq_zero_iff (y : (Σ k, J k) → Ω) (f : MRing J) :
    aeval (xPt y) f = 0 ↔ f ∈ mCoordIdeal y := by
  rw [aeval_xPt, map_eq_zero_iff _ emb_injective]
  rfl

end Point

section Model

variable {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [CharZero Ω]

abbrev imgField (y : (Σ k, J k) → Ω) (v : (Σ k, J₀ k) → Σ k, J k) : IntermediateField ℚ (Fn K Ω) :=
  IntermediateField.adjoin ℚ (Set.range fun p => xPt y (v p))

def imgPt (y : (Σ k, J k) → Ω) (v : (Σ k, J₀ k) → Σ k, J k) : (Σ k, J₀ k) → imgField y v :=
  fun p => ⟨xPt y (v p), IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩⟩

theorem coe_aeval_imgPt (y : (Σ k, J k) → Ω) (v : (Σ k, J₀ k) → Σ k, J k) (f : MRing J₀) :
    ((aeval (imgPt y v) f : imgField y v) : Fn K Ω) = aeval (fun p => xPt y (v p)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, IntermediateField.coe_add, hp, hq]
  | mul_X p n hp => simp only [map_mul, MulMemClass.coe_mul, hp, aeval_X, imgPt]

def genFib (y : (Σ k, J k) → Ω) (v : (Σ k, J₀ k) → Σ k, J k) : GenFibre v (mCoordIdeal y) where
  Φ := imgField y v
  Φ' := Fn K Ω
  x := imgPt y v
  x' := xPt y
  ker_x := by
    ext f
    rw [RingHom.mem_ker]
    show _ ↔ rename v f ∈ mCoordIdeal y
    rw [← aeval_xPt_eq_zero_iff, aeval_rename, ← Subtype.coe_inj]
    exact (coe_aeval_imgPt y v f).symm ▸ Iff.rfl
  gen := by
    intro c
    obtain ⟨f, g, hg, e⟩ := exists_quot_of_mem_adjoin (fun p => xPt y (v p)) c.2
    refine ⟨f, g, ?_, ?_⟩
    · intro h0
      apply hg
      rw [← coe_aeval_imgPt, h0]
      rfl
    · apply Subtype.ext
      rw [IntermediateField.coe_div, coe_aeval_imgPt, coe_aeval_imgPt]
      exact e
  genericFibre_ker_target := by
    ext f
    rw [RingHom.mem_ker]
    exact aeval_xPt_eq_zero_iff y f
  compat := fun _ => rfl

end Model

section Degree

variable {K₀ : Type} {J₀ : K₀ → Type} {K : Type} {J : K → Type} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω]
  [CharZero Ω₀] [CharZero Ω]

theorem blockFnField_xPt (y : (Σ k, J k) → Ω) :
    blockFnField (xPt y) = (blockFnField y).map (cst K Ω).toRatAlgHom := by
  rw [blockFnField, blockFnField, IntermediateField.adjoin_map]
  congr 1
  ext t
  constructor
  · rintro ⟨p, q, h, rfl⟩
    exact ⟨_, ⟨p, q, h, rfl⟩, (xPt_div_xPt y h).symm⟩
  · rintro ⟨_, ⟨p, q, h, rfl⟩, rfl⟩
    exact ⟨p, q, h, (xPt_div_xPt y h).symm⟩

theorem blockFnField_xPt_comp (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K)
    (v : (Σ k, J₀ k) → Σ k, J k) (hv : ∀ p, (v p).1 = bk p.1) (i : Ω₀ →+* Ω)
    (hy : ∀ p, y (v p) = i (y₀ p)) :
    blockFnField (xPt y ∘ v) =
      ((blockFnField y₀).map i.toRatAlgHom).map (cst K Ω).toRatAlgHom := by
  have key : ∀ p q : Σ k, J₀ k, p.1 = q.1 →
      (xPt y ∘ v) p / (xPt y ∘ v) q = cst K Ω (i (y₀ p / y₀ q)) := by
    intro p q h
    rw [Function.comp, Function.comp, xPt_div_xPt y (by rw [hv, hv, h]), hy, hy, map_div₀ i]
  rw [blockFnField, blockFnField, IntermediateField.adjoin_map, IntermediateField.adjoin_map]
  congr 1
  ext t
  constructor
  · rintro ⟨p, q, h, rfl⟩
    exact ⟨_, ⟨_, ⟨p, q, h, rfl⟩, rfl⟩, (key p q h).symm⟩
  · rintro ⟨_, ⟨_, ⟨p, q, h, rfl⟩, rfl⟩, rfl⟩
    exact ⟨p, q, h, (key p q h).symm⟩

theorem finrank_map_top (i : Ω₀ →+* Ω) :
    Module.finrank ((⊤ : IntermediateField ℚ Ω₀).map i.toRatAlgHom) Ω =
      (letI := i.toAlgebra; Module.finrank Ω₀ Ω) := by
  letI := i.toAlgebra
  rw [← AlgHom.fieldRange_eq_map]
  let e := AlgEquiv.ofInjectiveField i.toRatAlgHom
  symm
  refine Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv (RingEquiv.refl Ω) ?_
  ext a
  rfl

theorem relfinrank_block (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K)
    (v : (Σ k, J₀ k) → Σ k, J k) (hv : ∀ p, (v p).1 = bk p.1) (i : Ω₀ →+* Ω)
    (hy : ∀ p, y (v p) = i (y₀ p)) (h₀ : blockFnField y₀ = ⊤) (h : blockFnField y = ⊤) :
    IntermediateField.relfinrank (blockFnField (xPt y ∘ v)) (blockFnField (xPt y)) =
      (letI := i.toAlgebra; Module.finrank Ω₀ Ω) := by
  rw [blockFnField_xPt_comp y₀ y bk v hv i hy, blockFnField_xPt, h₀, h,
    IntermediateField.relfinrank_map_map, IntermediateField.relfinrank_top_right, finrank_map_top]

end Degree

theorem exists_genFibre_chart_degree : ∀ (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (i : Ω₀ →+* Ω) (D d : ℕ), Function.Injective bk → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → IsArithVar (mCoordIdeal y₀) (D + 1) → IsArithVar (mCoordIdeal y) (D + 1) → Birational y₀ → Birational y → (letI := i.toAlgebra; Module.finrank Ω₀ Ω = d) → 0 < d → ∃ (Gf : GenFibre (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) (mCoordIdeal y)) (ch : ∀ k : FibreBlock bk, J k.1), (∀ k : FibreBlock bk, Gf.x' ⟨k.1, ch k⟩ ≠ 0) ∧ Module.finrank Gf.Φ (IntermediateField.adjoin Gf.Φ (Set.range fun q : Σ k : FibreBlock bk, J k.1 => Gf.x' ⟨q.1.1, q.2⟩ / Gf.x' ⟨q.1.1, ch q.1⟩)) = d := by
  intro K₀ K _ _ J₀ J _ _ Ω₀ Ω _ _ _ y₀ y bk bx i D d hbk hy hA₀ hA hb₀ hb hd _
  haveI : CharZero Ω₀ := i.charZero
  have hrel : ∀ {L : Type} {I : L → Type} [∀ k, Fintype (I k)] {F : Type} [Field F]
      (w : (Σ k, I k) → F) (_ : (mCoordIdeal w).IsPrime ∧ IsRelevant (mCoordIdeal w)),
      ∀ k, ∃ a, w ⟨k, a⟩ ≠ 0 := by
    intro L I _ F _ w h k
    obtain ⟨a, ha⟩ := h.2 k
    refine ⟨a, fun h0 => ha ?_⟩
    show mConeMap w (X ⟨k, a⟩) = 0
    simp [mConeMap, h0]
  choose c₀ hc₀ using hrel y₀ ⟨hA₀.2.1.1, hA₀.2.1.2.2⟩
  choose c hc using hrel y ⟨hA.2.1.1, hA.2.1.2.2⟩
  have hv := GlobalTheory.CompanionTheory.Ar.Chg.isBlockMap_blkV bx hbk
  let v := GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx
  have hyv : ∀ p, y (v p) = i (y₀ p) := fun p => hy p.1 p.2
  let G := genFib y v
  haveI : CharZero G.Φ' := inferInstanceAs (CharZero (Fn K Ω))
  let ch : ∀ k : FibreBlock bk, J k.1 := fun k => c k.1
  have hch : ∀ k : FibreBlock bk, G.x' ⟨k.1, ch k⟩ ≠ 0 := fun k => xPt_ne_zero (hc k.1)
  have hx : ∀ k, G.x ⟨k, c₀ k⟩ ≠ 0 := by
    intro k h0
    have h1 : xPt y (v ⟨k, c₀ k⟩) = 0 := congrArg Subtype.val h0
    refine xPt_ne_zero ?_ h1
    rw [hyv]
    exact (map_ne_zero i).2 (hc₀ k)
  refine ⟨G, ch, hch, ?_⟩
  have main := GroundTheory.Heights₂.Heights.Targets.GenFibreChartDeg.proof
    GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.proof
    GroundTheory.Heights₂.Heights.Inter.AdjoinIndepRelfinrank.proof
    K₀ J₀ K J bk v (mCoordIdeal y) G c₀ ch hv hA.2.1.2.1 hx hch
  refine main.trans ?_
  rw [← hd]
  exact relfinrank_block y₀ y bk v (fun _ => rfl) i hyv
    (blockFnField_eq_top y₀ c₀ hc₀ hb₀) (blockFnField_eq_top y c hc hb)

end GlobalTheory.CompanionTheory.Ar.Chg.GenFib
end
end

section
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_reindexed : ∀ (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (i : Ω₀ →+* Ω) (D d : ℕ), Function.Injective bk → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → IsArithVar (mCoordIdeal y₀) (D + 1) → IsArithVar (mCoordIdeal y) (D + 1) → Birational y₀ → Birational y → (letI := i.toAlgebra; Module.finrank Ω₀ Ω = d) → 0 < d → ∃ (Gf : GenFibre (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) (mCoordIdeal y)) (ch : ∀ k : FibreBlock bk, J k.1), (∀ k : FibreBlock bk, Gf.x' ⟨k.1, ch k⟩ ≠ 0) ∧ Module.finrank Gf.Φ (IntermediateField.adjoin Gf.Φ (Set.range fun q : Σ k : FibreBlock bk, J k.1 => Gf.x' ⟨q.1.1, q.2⟩ / Gf.x' ⟨q.1.1, ch q.1⟩)) = d := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.GenFib.exists_genFibre_chart_degree | exact GlobalTheory.CompanionTheory.Ar.Chg.GenFib.exists_genFibre_chart_degree | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.GenFib.exists_genFibre_chart_degree <;> assumption)
end

section
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_element_homog_relation : ∀ (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω] (y₀ : (Σ k, J₀ k) → Ω₀) (i : Ω₀ →+* Ω) (α : Ω), Birational y₀ → (letI := i.toAlgebra; IsAlgebraic Ω₀ α) → ∃ (n : ℕ) (c : ℕ → MRing J₀) (a : K₀ → ℕ) (G : MRing J₀) (b : K₀ → ℕ), (∀ j, IsMultiHomog (c j) a) ∧ IsMultiHomog G b ∧ G ∉ mCoordIdeal y₀ ∧ (∑ j ∈ Finset.range (n + 1), i (aeval y₀ (c j)) * α ^ j = 0) ∧ ∀ w ∈ mcPts (mCoordIdeal y₀), eval w (map (Int.castRingHom ℂ) G) ≠ 0 → ∀ τ : ℂ, ∑ j ∈ Finset.range (n + 1), eval w (map (Int.castRingHom ℂ) (c j)) * τ ^ j = 0 → ∑ j ∈ Finset.range (n + 1), (j : ℂ) * eval w (map (Int.castRingHom ℂ) (c j)) * τ ^ (j - 1) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AlgPoly.algebraic_form_poly | exact GlobalTheory.CompanionTheory.Ar.AlgPoly.algebraic_form_poly | (intros; apply GlobalTheory.CompanionTheory.Ar.AlgPoly.algebraic_form_poly <;> assumption)
end

section
section
open Filter Topology

namespace GlobalTheory.CompanionTheory.SimpleRoot

theorem exists_analytic_simple_root
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (n : ℕ)
    (c : ℕ → E → ℂ) (w₀ : E) (τ₀ : ℂ) (hc : ∀ j, AnalyticAt ℂ (c j) w₀)
    (h0 : ∑ j ∈ Finset.range (n + 1), c j w₀ * τ₀ ^ j = 0)
    (h1 : ∑ j ∈ Finset.range (n + 1), (j : ℂ) * c j w₀ * τ₀ ^ (j - 1) ≠ 0) :
    ∃ (V : Set E) (W : Set ℂ) (g : E → ℂ), IsOpen V ∧ w₀ ∈ V ∧ IsOpen W ∧ τ₀ ∈ W ∧
      AnalyticOnNhd ℂ g V ∧ ∀ w ∈ V, ∀ τ ∈ W,
        ∑ j ∈ Finset.range (n + 1), c j w * τ ^ j = 0 → τ = g w := by
  set F : E × ℂ → ℂ := fun p => ∑ j ∈ Finset.range (n + 1), c j p.1 * p.2 ^ j with hFdef
  have hFa : AnalyticAt ℂ F (w₀, τ₀) := by
    refine Finset.analyticAt_fun_sum _ fun j _ => ?_
    exact ((hc j).comp analyticAt_fst).mul (analyticAt_snd.pow j)
  have cdf : ContDiffAt ℂ (⊤ : WithTop ℕ∞) F (w₀, τ₀) := hFa.contDiffAt
  have pn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  set d : ℂ := ∑ j ∈ Finset.range (n + 1), (j : ℂ) * c j w₀ * τ₀ ^ (j - 1) with hd_def
  have hd : HasDerivAt (fun τ => F (w₀, τ)) d τ₀ :=
    HasDerivAt.fun_sum (u := Finset.range (n + 1)) (A := fun j τ => c j w₀ * τ ^ j)
      (A' := fun j => (j : ℂ) * c j w₀ * τ₀ ^ (j - 1)) fun j _ => by
        rw [show (j : ℂ) * c j w₀ * τ₀ ^ (j - 1) = c j w₀ * ((j : ℂ) * τ₀ ^ (j - 1)) by ring]
        exact (hasDerivAt_pow j τ₀).const_mul (c j w₀)
  have hfd : HasFDerivAt (fun τ => F (w₀, τ))
      ((fderiv ℂ F (w₀, τ₀)).comp (ContinuousLinearMap.inr ℂ E ℂ)) τ₀ :=
    hFa.differentiableAt.hasFDerivAt.comp τ₀ (hasFDerivAt_prodMk_right w₀ τ₀)
  have heq : (fderiv ℂ F (w₀, τ₀)).comp (ContinuousLinearMap.inr ℂ E ℂ) =
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d :=
    hfd.unique hd.hasFDerivAt
  have if₂ : ((fderiv ℂ F (w₀, τ₀)).comp (ContinuousLinearMap.inr ℂ E ℂ)).IsInvertible := by
    rw [heq]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 d h1), ?_⟩
    ext
    simp
  set g := cdf.implicitFunction pn if₂ with hg_def
  have hg : AnalyticAt ℂ g w₀ := (cdf.contDiffAt_implicitFunction pn if₂).analyticAt
  obtain ⟨V₂, W, hV₂o, hw₀V₂, hWo, hτ₀W, hsub⟩ :=
    mem_nhds_prod_iff'.1 (cdf.eventually_apply_eq_iff_implicitFunction pn if₂)
  refine ⟨{w | AnalyticAt ℂ g w} ∩ V₂, W, g, (isOpen_analyticAt ℂ g).inter hV₂o, ⟨hg, hw₀V₂⟩, hWo, hτ₀W,
    fun w hw => hw.1, ?_⟩
  intro w hw τ hτ hroot
  have hmem := hsub (Set.mk_mem_prod hw.2 hτ)
  simp only [Set.mem_ofPred_eq] at hmem
  have h' : F (w, τ) = F (w₀, τ₀) := by
    change (∑ j ∈ Finset.range (n + 1), c j w * τ ^ j) = ∑ j ∈ Finset.range (n + 1), c j w₀ * τ₀ ^ j
    rw [hroot, h0]
  exact (hmem.1 h').symm

end GlobalTheory.CompanionTheory.SimpleRoot
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.implicit_root_analytic : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (n : ℕ) (c : ℕ → E → ℂ) (w₀ : E) (τ₀ : ℂ), (∀ j, AnalyticAt ℂ (c j) w₀) → ∑ j ∈ Finset.range (n + 1), c j w₀ * τ₀ ^ j = 0 → ∑ j ∈ Finset.range (n + 1), (j : ℂ) * c j w₀ * τ₀ ^ (j - 1) ≠ 0 → ∃ (V : Set E) (W : Set ℂ) (g : E → ℂ), IsOpen V ∧ w₀ ∈ V ∧ IsOpen W ∧ τ₀ ∈ W ∧ AnalyticOnNhd ℂ g V ∧ ∀ w ∈ V, ∀ τ ∈ W, ∑ j ∈ Finset.range (n + 1), c j w * τ ^ j = 0 → τ = g w := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SimpleRoot.exists_analytic_simple_root
end

section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

theorem aeval_mul_homog {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)] {A : Type} [CommRing A] [Algebra ℤ A]
    (g : MRing J₀) (a : K₀ → ℕ) (hg : IsMultiHomog g a) (u : (Σ k, J₀ k) → A) (t : K₀ → A) :
    aeval (fun p => u p * t p.1) g = aeval u g * ∏ k, t k ^ a k := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hc : (∏ i : (Σ k, J₀ k), t i.1 ^ d i) = ∏ k, t k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ y, t k ^ d ⟨k, y⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hg d hd k]
  simp only [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem aeval_comp_ringHom {σ A B : Type} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B] (φ : A →+* B) (u : σ → A)
    (g : MvPolynomial σ ℤ) : aeval (fun p => φ (u p)) g = φ (aeval u g) := by
  induction g using MvPolynomial.induction_on with
  | C m => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp only [map_mul, hp, aeval_X]

theorem pow_mul_pow_sub_eq {F : Type} [Field F] (x b : F) (hb : b ≠ 0) {j n : ℕ} (hj : j ≤ n) :
    x ^ j * b ^ (n - j) = (x / b) ^ j * b ^ n := by
  have h : b ^ n = b ^ j * b ^ (n - j) := by rw [← pow_add]; congr 1; omega
  rw [h, div_pow]
  field_simp

theorem ratio_relation_at_complex_points :
    ∀ (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)]
      [∀ k, Fintype (J k)] (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω)
      (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (i : Ω₀ →+* Ω) (q r : Σ k, J k) (n : ℕ) (c : ℕ → MRing J₀)
      (a : K₀ → ℕ), (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → q.1 = r.1 → y r ≠ 0 →
      (∀ j, IsMultiHomog (c j) a) →
      (∑ j ∈ Finset.range (n + 1), i (aeval y₀ (c j)) * (y q / y r) ^ j = 0) →
      ∀ z ∈ mcPts (mCoordIdeal y), z r ≠ 0 → ∀ w : (Σ k, J₀ k) → ℂ,
        SameOrbit (fun p => z (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx p)) w →
        ∑ j ∈ Finset.range (n + 1), eval w (map (Int.castRingHom ℂ) (c j)) * (z q / z r) ^ j = 0 := by
  intro K₀ K _ _ J₀ J _ _ Ω₀ Ω _ _ y₀ y bk bx i q r n c a hy hqr hr hc hrel z hz hzr w hw
  have hcone : ∀ g : MRing J₀, IsMultiHomog g a →
      mConeMap y (rename (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) g) =
        MvPolynomial.C (i (aeval y₀ g)) * ∏ k, (MvPolynomial.X (bk k) : MvPolynomial K Ω) ^ a k := by
    intro g hg
    have h1 : mConeMap y (rename (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) g) =
        aeval (fun p : (Σ k, J₀ k) => (MvPolynomial.C (i (y₀ p)) : MvPolynomial K Ω) * MvPolynomial.X (bk p.1)) g := by
      simp only [mConeMap]
      rw [aeval_rename]
      have e : ((fun p : (Σ k, J k) => (MvPolynomial.C (y p) : MvPolynomial K Ω) * MvPolynomial.X p.1) ∘
          GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) =
          fun p : (Σ k, J₀ k) => (MvPolynomial.C (i (y₀ p)) : MvPolynomial K Ω) * MvPolynomial.X (bk p.1) := by
        funext p
        obtain ⟨k, b⟩ := p
        simp [GlobalTheory.CompanionTheory.Ar.Chg.blkV, hy]
      rw [e]
    rw [h1, aeval_mul_homog g a hg (fun p => (MvPolynomial.C (i (y₀ p)) : MvPolynomial K Ω)) (fun k => MvPolynomial.X (bk k))]
    congr 1
    exact aeval_comp_ringHom ((MvPolynomial.C : Ω →+* MvPolynomial K Ω).comp i) y₀ g
  have hXq : mConeMap y (MvPolynomial.X q) = MvPolynomial.C (y q) * MvPolynomial.X r.1 := by
    simp [mConeMap, hqr]
  have hXr : mConeMap y (MvPolynomial.X r) = MvPolynomial.C (y r) * MvPolynomial.X r.1 := by
    simp [mConeMap]
  let F : MRing J := ∑ j ∈ Finset.range (n + 1),
    rename (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) (c j) * MvPolynomial.X q ^ j * MvPolynomial.X r ^ (n - j)
  have hF : F ∈ mCoordIdeal y := by
    show mConeMap y F = 0
    simp only [F, map_sum, map_mul, map_pow, hcone _ (hc _), hXq, hXr]
    have hterm : ∀ j ∈ Finset.range (n + 1),
        MvPolynomial.C (i (aeval y₀ (c j))) * (∏ k, (MvPolynomial.X (bk k) : MvPolynomial K Ω) ^ a k) *
            (MvPolynomial.C (y q) * MvPolynomial.X r.1) ^ j * (MvPolynomial.C (y r) * MvPolynomial.X r.1) ^ (n - j) =
          (∏ k, (MvPolynomial.X (bk k) : MvPolynomial K Ω) ^ a k) * MvPolynomial.X r.1 ^ n *
            MvPolynomial.C (y r ^ n * (i (aeval y₀ (c j)) * (y q / y r) ^ j)) := by
      intro j hj
      have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      have e1 : y q ^ j * y r ^ (n - j) = (y q / y r) ^ j * y r ^ n := pow_mul_pow_sub_eq _ _ hr hjn
      have e2 : (MvPolynomial.X r.1 : MvPolynomial K Ω) ^ n = MvPolynomial.X r.1 ^ j * MvPolynomial.X r.1 ^ (n - j) := by
        rw [← pow_add]; congr 1; omega
      have e3 : (MvPolynomial.C (y q) : MvPolynomial K Ω) ^ j * MvPolynomial.C (y r) ^ (n - j) =
          MvPolynomial.C ((y q / y r) ^ j * y r ^ n) := by
        rw [← e1]; simp only [map_mul, map_pow]
      rw [mul_pow, mul_pow, e2]
      have e4 : (MvPolynomial.C (y r ^ n * (i (aeval y₀ (c j)) * (y q / y r) ^ j)) : MvPolynomial K Ω) =
          MvPolynomial.C (i (aeval y₀ (c j))) * MvPolynomial.C ((y q / y r) ^ j * y r ^ n) := by
        rw [← map_mul]; congr 1; ring
      rw [e4, ← e3]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← map_sum, ← Finset.mul_sum, hrel]
    simp
  obtain ⟨s, hs, he⟩ := hw
  have hev := hz.2 F hF
  have hren : ∀ j, eval z (map (Int.castRingHom ℂ) (rename (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) (c j))) =
      (∏ k, s k ^ a k) * eval w (map (Int.castRingHom ℂ) (c j)) := by
    intro j
    rw [map_rename, eval_rename]
    have : z ∘ GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx = fun p => s p.1 * w p := he
    rw [this, eval_smul_homog (c j) a (hc j) s w]
  simp only [F, map_sum, map_mul, map_pow, map_X, eval_X, hren] at hev
  have hP : (∏ k, s k ^ a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hs k)
  have hfin : (∏ k, s k ^ a k) * z r ^ n *
      ∑ j ∈ Finset.range (n + 1), eval w (map (Int.castRingHom ℂ) (c j)) * (z q / z r) ^ j = 0 := by
    rw [← hev, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rw [mul_assoc ((∏ k, s k ^ a k) * _), pow_mul_pow_sub_eq _ _ hzr hjn]
    ring
  exact (mul_eq_zero.1 hfin).resolve_left (mul_ne_zero hP (pow_ne_zero _ hzr))

end GlobalTheory.CompanionTheory.Ar.Rel
end
end

section
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homog_relation_ratio_reindex : ∀ (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (i : Ω₀ →+* Ω) (q r : Σ k, J k) (n : ℕ) (c : ℕ → MRing J₀) (a : K₀ → ℕ), (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → q.1 = r.1 → y r ≠ 0 → (∀ j, IsMultiHomog (c j) a) → (∑ j ∈ Finset.range (n + 1), i (aeval y₀ (c j)) * (y q / y r) ^ j = 0) → ∀ z ∈ mcPts (mCoordIdeal y), z r ≠ 0 → ∀ w : (Σ k, J₀ k) → ℂ, SameOrbit (fun p => z (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx p)) w → ∑ j ∈ Finset.range (n + 1), eval w (map (Int.castRingHom ℂ) (c j)) * (z q / z r) ^ j = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rel.ratio_relation_at_complex_points | exact GlobalTheory.CompanionTheory.Ar.Rel.ratio_relation_at_complex_points | (intros; apply GlobalTheory.CompanionTheory.Ar.Rel.ratio_relation_at_complex_points <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

open MvPolynomial GroundTheory.Heights₂.Heights.Inter
open scoped Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Chg.DegBlock

variable {K₀ K : Type} [Fintype K₀] [Fintype K] {J₀ : K₀ → Type} {J : K → Type} [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)]

theorem isMultiHomog_mul' {f g : MRing J₀} {a b : K₀ → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
  have h1 := hf m1 hm1 k
  have h2 := hg m2 hm2 k
  simp [Finset.sum_add_distrib, h1, h2]

theorem isMultiHomog_rename' {κ : K₀ → K} {v : (Σ k, J₀ k) → (Σ k, J k)} (hv : IsBlockMap κ v) {f : MRing J₀}
    {a : K₀ → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (rename v f : MRing J) (Function.extend κ a 0) := by
  intro m hm k'
  rw [support_rename_of_injective hv.2.1] at hm
  obtain ⟨m0, hm0, rfl⟩ := Finset.mem_image.mp hm
  by_cases hk : k' ∈ Set.range κ
  · obtain ⟨k, rfl⟩ := hk
    rw [hv.1.extend_apply, ← hf m0 hm0 k]
    have hex : ∀ i' : J (κ k), ∃ i : J₀ k, v ⟨k, i⟩ = ⟨κ k, i'⟩ := by
      intro i'
      obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
      have h1 : κ p.1 = κ k := by rw [← hv.2.2.1 p, hp]
      obtain ⟨k₁, i⟩ := p
      obtain rfl : k₁ = k := hv.1 h1
      exact ⟨i, hp⟩
    choose g hg using hex
    have hb : Function.Bijective g := by
      constructor
      · intro a b hab
        have : (⟨κ k, a⟩ : Σ k, J k) = ⟨κ k, b⟩ := by rw [← hg a, ← hg b, hab]
        exact eq_of_heq (Sigma.mk.inj this).2
      · intro i
        have hq : ∃ i', v ⟨k, i⟩ = ⟨κ k, i'⟩ := by
          have h1 := hv.2.2.1 ⟨k, i⟩
          generalize v ⟨k, i⟩ = q at h1
          obtain ⟨q1, q2⟩ := q
          simp only at h1
          subst h1
          exact ⟨q2, rfl⟩
        obtain ⟨i', hi'⟩ := hq
        refine ⟨i', ?_⟩
        have h2 : v ⟨k, g i'⟩ = v ⟨k, i⟩ := by rw [hg i', hi']
        exact eq_of_heq (Sigma.mk.inj (hv.2.1 h2)).2
    calc ∑ i', (Finsupp.mapDomain v m0) ⟨κ k, i'⟩ = ∑ i', m0 ⟨k, g i'⟩ := by
          refine Finset.sum_congr rfl fun i' _ => ?_
          rw [← hg i', Finsupp.mapDomain_apply hv.2.1]
      _ = ∑ i, m0 ⟨k, i⟩ := hb.sum_comp fun i => m0 ⟨k, i⟩
  · rw [Function.extend_apply' _ _ _ (by simpa using hk)]
    refine Finset.sum_eq_zero fun i' _ => ?_
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨p, hp⟩
    exact hk ⟨p.1, by rw [← hv.2.2.1 p, hp]⟩

theorem eval_map_rename' (zt : (Σ k, J k) → ℂ) (v : (Σ k, J₀ k) → (Σ k, J k)) (s : MRing J₀) :
    eval zt (map (Int.castRingHom ℂ) (rename v s : MRing J)) = eval (fun p => zt (v p)) (map (Int.castRingHom ℂ) s) := by
  rw [map_rename, eval_rename]
  rfl

theorem imageZ_eq {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] (i : Ω₀ →+* Ω) {y₀ : (Σ k, J₀ k) → Ω₀}
    {y : (Σ k, J k) → Ω} {bk : K₀ → K} (bx : ∀ k, J₀ k ≃ J (bk k)) (hbk : Function.Injective bk)
    (hy : ∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) :
    imageZ (blkV bk bx) (mCoordIdeal y) = mCoordIdeal y₀ := by
  refine le_antisymm ?_ (mCoordIdeal_le_imageZ i bx hy)
  intro f hf
  let Φ : MvPolynomial K₀ Ω₀ →+* MvPolynomial K Ω :=
    (rename bk : MvPolynomial K₀ Ω →ₐ[Ω] MvPolynomial K Ω).toRingHom.comp (MvPolynomial.map i)
  have hΦ : Function.Injective Φ :=
    (rename_injective bk hbk).comp (MvPolynomial.map_injective i i.injective)
  have key : ∀ f : MRing J₀, mConeMap y (rename (blkV bk bx) f) = Φ (mConeMap y₀ f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap, Φ]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p n hp =>
      obtain ⟨k, a⟩ := n
      simp only [map_mul, hp, rename_X]
      congr 1
      simp [mConeMap, Φ, blkV, hy]
  have h0 : mConeMap y (rename (blkV bk bx) f) = 0 := hf
  rw [key] at h0
  exact hΦ (h0.trans (map_zero Φ).symm)

theorem not_mem_mcPts_top {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] (z : (Σ k, J k) → ℂ) :
    z ∉ mcPts (⊤ : Ideal (MRing J)) := by
  intro h
  have := h.2 1 trivial
  simp at this

theorem sameOrbit_trans' {K : Type} {J : K → Type} {a b c : (Σ k, J k) → ℂ} (h1 : SameOrbit a b) (h2 : SameOrbit b c) :
    SameOrbit a c := by
  obtain ⟨s, hs, rfl⟩ := h1
  obtain ⟨t, ht, rfl⟩ := h2
  exact ⟨fun k => s k * t k, fun k => mul_ne_zero (hs k) (ht k), by funext p; ring⟩

theorem sameOrbit_symm' {K : Type} {J : K → Type} {a b : (Σ k, J k) → ℂ} (h : SameOrbit a b) : SameOrbit b a := by
  obtain ⟨s, hs, rfl⟩ := h
  refine ⟨fun k => (s k)⁻¹, fun k => inv_ne_zero (hs k), ?_⟩
  funext p
  exact (inv_mul_cancel_left₀ (hs p.1) _).symm

theorem sameOrbit_restr {bk : K₀ → K} (bx : ∀ k, J₀ k ≃ J (bk k)) {a b : (Σ k, J k) → ℂ} (h : SameOrbit a b) :
    SameOrbit (fun p => a (blkV bk bx p)) (fun p => b (blkV bk bx p)) := by
  obtain ⟨s, hs, rfl⟩ := h
  exact ⟨fun k => s (bk k), fun k => hs _, rfl⟩

theorem holoMap_id' {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) : HoloMap A A (id : X → X) :=
  ⟨continuous_id, fun j k => A.holo j k⟩

theorem isMultiHomog_one' : IsMultiHomog (1 : MRing J₀) (0 : K₀ → ℕ) := by
  intro m hm k
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  simp [hm]

theorem isMultiHomog_prod' {X : Type} (s : Finset X) {f : X → MRing J₀} {a : X → K₀ → ℕ}
    (h : ∀ x ∈ s, IsMultiHomog (f x) (a x)) : IsMultiHomog (∏ x ∈ s, f x) (∑ x ∈ s, a x) := by
  induction s using Finset.induction_on with
  | empty => simpa using isMultiHomog_one'
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    exact isMultiHomog_mul' (h x (Finset.mem_insert_self x s))
      (ih fun u hu => h u (Finset.mem_insert_of_mem hu))

theorem exists_local_section {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] [CharZero Ω] (y₀ : (Σ k, J₀ k) → Ω₀)
    (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (i : Ω₀ →+* Ω) (d : ℕ)
    (hy : ∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) (hprime : (mCoordIdeal y₀).IsPrime) (hB₀ : Birational y₀)
    (hfin : letI := i.toAlgebra; Module.finrank Ω₀ Ω = d) (hd : 0 < d) :
    ∃ (G : MRing J₀) (a : K₀ → ℕ), IsMultiHomog G a ∧ G ∉ mCoordIdeal y₀ ∧
      ∀ z ∈ mcPts (mCoordIdeal y), ∀ w₀ ∈ mcPts (mCoordIdeal y₀), SameOrbit (fun p => z (blkV bk bx p)) w₀ →
        eval w₀ (map (Int.castRingHom ℂ) G) ≠ 0 →
        ∃ (V : Set ((Σ k, J₀ k) → ℂ)) (V' : Set ((Σ k, J k) → ℂ)) (f : ((Σ k, J₀ k) → ℂ) → (Σ k, J k) → ℂ),
          IsOpen V ∧ w₀ ∈ V ∧ IsOpen V' ∧ z ∈ V' ∧ AnalyticOnNhd ℂ f V ∧
            ∀ z'' ∈ V' ∩ mcPts (mCoordIdeal y), ∀ w ∈ V ∩ mcPts (mCoordIdeal y₀),
              SameOrbit (fun p => z'' (blkV bk bx p)) w → SameOrbit (f w) z'' := by
  have halg : ∀ α : Ω, (letI := i.toAlgebra; IsAlgebraic Ω₀ α) := by
    letI := i.toAlgebra
    haveI : Module.Finite Ω₀ Ω := Module.finite_of_finrank_pos (by rw [hfin]; exact hd)
    exact fun α => Algebra.IsAlgebraic.isAlgebraic α
  have hdata := fun q r : Σ k, J k => GlobalTheory.T.algebraic_element_homog_relation K₀ J₀ Ω₀ Ω y₀ i (y q / y r) hB₀ (halg _)
  choose n c a G b hc hG hGn hsum hsimple using hdata
  refine ⟨∏ x : (Σ k, J k) × (Σ k, J k), G x.1 x.2, ∑ x : (Σ k, J k) × (Σ k, J k), b x.1 x.2,
    isMultiHomog_prod' _ fun x _ => hG x.1 x.2, ?_, ?_⟩
  · intro hm
    obtain ⟨x, -, hx⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hprime)).1 hm
    exact hGn _ _ hx
  intro z hz w₀ hw₀ hr h0
  have hGw : ∀ q r, eval w₀ (map (Int.castRingHom ℂ) (G q r)) ≠ 0 := by
    intro q r h
    apply h0
    rw [map_prod, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ (q, r)) h
  choose rr hrr using hz.1
  let r : ∀ k, Σ k, J k := fun k => ⟨k, rr k⟩
  have hyr : ∀ k, y (r k) ≠ 0 := by
    intro k h
    apply hrr k
    have hm : (X (r k) : MRing J) ∈ mCoordIdeal y := by
      show mConeMap y (X (r k)) = 0
      simp [mConeMap, h]
    simpa using hz.2 _ hm
  have hroot : ∀ q : Σ k, J k, ∃ (V : Set ((Σ k, J₀ k) → ℂ)) (W : Set ℂ) (g : ((Σ k, J₀ k) → ℂ) → ℂ),
      IsOpen V ∧ w₀ ∈ V ∧ IsOpen W ∧ z q / z (r q.1) ∈ W ∧ AnalyticOnNhd ℂ g V ∧
        ∀ w ∈ V, ∀ τ ∈ W, ∑ j ∈ Finset.range (n q (r q.1) + 1),
          eval w (map (Int.castRingHom ℂ) (c q (r q.1) j)) * τ ^ j = 0 → τ = g w := by
    intro q
    have h1 := GlobalTheory.T.homog_relation_ratio_reindex K₀ K J₀ J Ω₀ Ω y₀ y bk bx i q (r q.1) (n q (r q.1)) (c q (r q.1)) (a q (r q.1)) hy rfl
      (hyr _) (hc _ _) (hsum _ _) z hz (hrr _) w₀ hr
    exact GlobalTheory.T.implicit_root_analytic _ (n q (r q.1)) (fun j w => eval w (map (Int.castRingHom ℂ) (c q (r q.1) j))) w₀ _
      (fun j => AnalyticOnNhd.eval_mvPolynomial _ _ (Set.mem_univ _)) h1
      (hsimple _ _ w₀ hw₀ (hGw _ _) _ h1)
  choose V W g hVo hV hWo hW hga huniq using hroot
  refine ⟨⋂ q, V q, {z'' | ∀ q : Σ k, J k, z'' (r q.1) ≠ 0 ∧ z'' q / z'' (r q.1) ∈ W q}, fun w q => g q w,
    isOpen_iInter_of_finite hVo, Set.mem_iInter.2 hV, ?_, fun q => ⟨hrr _, hW q⟩, ?_, ?_⟩
  · rw [Set.setOf_forall]
    refine isOpen_iInter_of_finite fun q => ?_
    have hc1 : Continuous fun z'' : (Σ k, J k) → ℂ => z'' (r q.1) := continuous_apply _
    have hc2 : Continuous fun z'' : (Σ k, J k) → ℂ => z'' q := continuous_apply _
    have ho : IsOpen {z'' : (Σ k, J k) → ℂ | z'' (r q.1) ≠ 0} := isOpen_ne_fun hc1 continuous_const
    exact (ContinuousOn.isOpen_inter_preimage
      (hc2.continuousOn.div hc1.continuousOn fun _ h => h) ho (hWo q))
  · intro w hw
    have : ∀ q, AnalyticAt ℂ (g q) w := fun q => hga q w (Set.mem_iInter.1 hw q)
    exact AnalyticAt.pi this
  · rintro z'' ⟨hz1, hz2⟩ w ⟨hw1, -⟩ hR
    refine ⟨fun k => (z'' (r k))⁻¹, fun k => inv_ne_zero (hz1 (r k)).1, ?_⟩
    funext q
    have h1 := GlobalTheory.T.homog_relation_ratio_reindex K₀ K J₀ J Ω₀ Ω y₀ y bk bx i q (r q.1) (n q (r q.1)) (c q (r q.1)) (a q (r q.1)) hy rfl
      (hyr _) (hc _ _) (hsum _ _) z'' hz2 (hz1 q).1 w hR
    have h2 := huniq q w (Set.mem_iInter.1 hw1 q) _ (hz1 q).2 h1
    show g q w = (z'' (r q.1))⁻¹ * z'' q
    rw [← h2, div_eq_inv_mul]

theorem exists_count {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] [CharZero Ω] (y₀ : (Σ k, J₀ k) → Ω₀)
    (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (i : Ω₀ →+* Ω) (D d : ℕ)
    (hbk : Function.Injective bk) (hy : ∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩))
    (hA₀ : IsArithVar (mCoordIdeal y₀) (D + 1)) (hA : IsArithVar (mCoordIdeal y) (D + 1))
    (hB₀ : Birational y₀) (hB : Birational y) (hfin : letI := i.toAlgebra; Module.finrank Ω₀ Ω = d) (hd : 0 < d) :
    ∃ (G : MRing J₀) (a : K₀ → ℕ), IsMultiHomog G a ∧ G ∉ mCoordIdeal y₀ ∧
      ∀ w ∈ mcPts (mCoordIdeal y₀), eval w (map (Int.castRingHom ℂ) G) ≠ 0 →
        (ptsOverPt (mCoordIdeal y) (blkV bk bx) w).ncard = d := by
  have himg := imageZ_eq i bx hbk hy
  obtain ⟨Gf, ch, hch, hf⟩ := GlobalTheory.T.arith_variety_reindexed K₀ K J₀ J Ω₀ Ω y₀ y bk bx i D d hbk hy hA₀ hA hB₀ hB hfin hd
  obtain ⟨G, a, hG, hGn, hc⟩ := GlobalTheory.T.generic_points_good_statement K₀ J₀ K J bk (blkV bk bx) (mCoordIdeal y) D Gf ch
    (isBlockMap_blkV bx hbk) hA (by rw [himg]; exact hA₀) hch
  rw [himg] at hGn hc
  exact ⟨G, a, hG, hGn, fun w hw h0 => (hc w hw h0).trans hf⟩

theorem isDegreeOff_of_block : ∀ (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (i : Ω₀ →+* Ω) (D d : ℕ) (R₀ : AnLogRes (mCoordIdeal y₀) ⊤ D) (R : AnLogRes (mCoordIdeal y) ⊤ D) (h : R.X → R₀.X), Function.Injective bk → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → IsArithVar (mCoordIdeal y₀) (D + 1) → IsArithVar (mCoordIdeal y) (D + 1) → Birational y₀ → Birational y → HoloMap R.A R₀.A h → (∀ x, SameOrbit (R₀.lift (h x) (h x)) (fun p => R.lift x x (blkV bk bx p))) → (letI := i.toAlgebra; Module.finrank Ω₀ Ω = d) → 0 < d → ∃ br : Set R₀.X, IsDegreeOff R₀.A R.A h d br := by
  intro K₀ K _ _ J₀ J _ _ Ω₀ Ω _ _ _ y₀ y bk bx i D d R₀ R h hbk hy hA₀ hA hB₀ hB hh hlift hfin hd
  have hv : IsBlockMap bk (blkV bk bx) := isBlockMap_blkV bx hbk
  have hprime : (mCoordIdeal y₀).IsPrime := hA₀.2.1.1
  have himg := imageZ_eq i bx hbk hy
  obtain ⟨G₁, a₁, hG₁, hG₁n, hcount⟩ := exists_count y₀ y bk bx i D d hbk hy hA₀ hA hB₀ hB hfin hd
  obtain ⟨G₂, a₂, hG₂, hG₂n, hloc⟩ := exists_local_section y₀ y bk bx i d hy hprime hB₀ hfin hd
  have hGn : G₁ * G₂ ∉ mCoordIdeal y₀ := fun hm => (hprime.mem_or_mem hm).elim hG₁n hG₂n
  have hGh : IsMultiHomog (G₁ * G₂) (a₁ + a₂) := isMultiHomog_mul' hG₁ hG₂
  have hev : ∀ w : (Σ k, J₀ k) → ℂ, eval w (map (Int.castRingHom ℂ) (G₁ * G₂)) ≠ 0 →
      eval w (map (Int.castRingHom ℂ) G₁) ≠ 0 ∧ eval w (map (Int.castRingHom ℂ) G₂) ≠ 0 := by
    intro w hw
    simp only [map_mul] at hw
    exact ⟨fun h => hw (by rw [h]; simp), fun h => hw (by rw [h]; simp)⟩
  have hrn : rename (blkV bk bx) (G₁ * G₂) ∉ mCoordIdeal y := fun hm =>
    hGn (himg ▸ (show G₁ * G₂ ∈ imageZ (blkV bk bx) (mCoordIdeal y) from hm))
  refine ⟨_, GlobalTheory.T.log_resolution_compatible_pullback K₀ J₀ K J (mCoordIdeal y₀) ⊤ (mCoordIdeal y) ⊤ D R₀.X R₀.A R₀ id R h
    (fun z w => SameOrbit (fun p => z (blkV bk bx p)) w) (G₁ * G₂) (rename (blkV bk bx) (G₁ * G₂)) (a₁ + a₂)
    (Function.extend bk (a₁ + a₂) 0) d rfl hA₀ hA (holoMap_id' R₀.A) (isDegreeOff_id R₀.A) hh hGh hGn
    (isMultiHomog_rename' hv hGh) hrn
    (fun z z₁ w w₁ hr h1 h2 => sameOrbit_trans' (sameOrbit_restr bx h1)
      (sameOrbit_trans' hr (sameOrbit_symm' h2))) ?_ ?_ ?_ ?_ ?_ ?_⟩
  · intro x x₀ e
    have e' : x₀ = h x := e
    subst e'
    exact sameOrbit_symm' (hlift x)
  · intro x x₀ hr
    exact R₀.inj x₀ (h x) (not_mem_mcPts_top _) (sameOrbit_trans' (sameOrbit_symm' hr) (sameOrbit_symm' (hlift x)))
  · intro w hw h0
    exact hcount w hw (hev w h0).1
  · intro z hz hzJ
    exact absurd hzJ (not_mem_mcPts_top z)
  · intro z hz w hw hr h0
    rw [eval_map_rename']
    obtain ⟨c, hc, e⟩ := hr
    rw [e, ReciprocityTheory.ChartRestriction.G.Geo.eval_smul_homog _ _ hGh, h0, mul_zero]
  · intro z hz w₀ hw₀ hr h0
    exact hloc z hz w₀ hw₀ hr (hev w₀ h0).2

end GlobalTheory.CompanionTheory.Ar.Chg.DegBlock
end
end
