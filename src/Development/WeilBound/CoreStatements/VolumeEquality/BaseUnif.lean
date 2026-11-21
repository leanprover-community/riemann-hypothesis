import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifDefs
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspCorrespondenceBound
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsEmbLabel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelEmbCompInjective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Rt0NeZero
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifRiem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelTransformSymplecticImaginary
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelNormalFormOfHermitian
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallDomainIffPosDef
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetEqBallPotential
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SymmetricMatrixInBallImage
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugateEmbeddingsCriterion
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelTransformCommutesAction
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SpanStandardBasisEigenspace
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BigZe
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsNormalizedRiemannLattice
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsRiemannLatticeOfPeriod
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalHolomorphicPeriodFamily
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallDomainOpenConvexZero
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CongruenceSubgroupOfFormAutomorphisms
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyPeriodRiemannLatticeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreLatticeBaseChangeConjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartHolomorphic
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyUniformisationLocalPeriod
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDifferentiableOnTransfer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPair
import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifEx2
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RingOfIntegersHomInjective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicFamilyConjugate
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugateUniversalFamilyStatement
import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifDefsB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VerticalDerivativeInCoordinates
import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifVec

section
noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l}

def HasRk (H : Host E) (p q : ℕ) {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) : Prop :=
  ∀ s : E →+* ℂ, Module.finrank ℂ (eigSp R.B (s.comp (algebraMap (𝓞 E) E))) = if s (H.rt : E) = H.rt0 then p else q

theorem label_conj (κ : c.F →+* ℂ) (τ : CMType H) :
    κ.comp (labelEmb c (.inr τ)) = (starRingEnd ℂ).comp (κ.comp (labelEmb c (.inl τ))) := by
  refine RingHom.ext fun a => ?_
  let ψ : E →+* ℂ := κ.comp (τ.1.codRestrict c.F (c.conj τ.1))
  show ψ ((H.bar a : 𝓞 E) : E) = starRingEnd ℂ (ψ (a : E))
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]

theorem label_conj' (κ : c.F →+* ℂ) (τ : CMType H) :
    κ.comp (labelEmb c (.inl τ)) = (starRingEnd ℂ).comp (κ.comp (labelEmb c (.inr τ))) := by
  rw [label_conj]
  exact RingHom.ext fun a => by simp

theorem label_bij (κ : c.F →+* ℂ) : Function.Bijective fun lab : CMType H ⊕ CMType H => κ.comp (labelEmb c lab) :=
  LabPt.bijective_of_injective H _ (FamEx.labelEmb_comp_injective E H l c κ)

theorem label_cm (κ : c.F →+* ℂ) :
    IsCMFam (fun τ : CMType H => κ.comp (labelEmb c (.inl τ))) ∧ IsCMFam (fun τ : CMType H => κ.comp (labelEmb c (.inr τ))) := by
  refine LabPt.isCMFam_of_bijective _ _ ?_ (label_conj κ)
  convert label_bij (c := c) κ using 1
  funext s
  rcases s with τ | τ <;> rfl

theorem hasRk_iff (κ : c.F →+* ℂ) (ρ : c.F) (hρ : (ρ : ℂ) = H.rt0) (hκ : κ ρ = H.rt0) (p q : ℕ) {g : ℕ} {Λ : Type}
    [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) :
    HasRk H p q R ↔ ∀ τ : CMType H, Module.finrank ℂ (eigSp R.B (κ.comp (labelEmb c (.inl τ)))) = p ∧
      Module.finrank ℂ (eigSp R.B (κ.comp (labelEmb c (.inr τ)))) = q := by
  have hne : -H.rt0 ≠ H.rt0 := fun e => FamEx.rt0_ne_zero H (by linear_combination (-1/2 : ℂ) * e)
  constructor
  · intro h τ
    obtain ⟨s, hs, hv⟩ := FamEx.exists_emb_label E H l c κ (.inl τ)
    obtain ⟨s', hs', hv'⟩ := FamEx.exists_emb_label E H l c κ (.inr τ)
    have e := hv ρ hρ
    have e' := hv' ρ hρ
    simp only [Sum.elim_inl, Sum.elim_inr, hκ] at e e'
    rw [hs, hs', h s, h s', if_pos e, if_neg (by rw [e']; exact hne)]
    exact ⟨rfl, rfl⟩
  · intro h s
    obtain ⟨lab, hl⟩ := (label_bij (c := c) κ).2 (s.comp (algebraMap (𝓞 E) E))
    obtain ⟨s', hs', hv'⟩ := FamEx.exists_emb_label E H l c κ lab
    have e := hv' ρ hρ
    have hl' : κ.comp (labelEmb c lab) = s.comp (algebraMap (𝓞 E) E) := hl
    have e2 : s (H.rt : E) = s' (H.rt : E) := RingHom.congr_fun (hl'.symm.trans hs') H.rt
    rw [← hl', e2, e]
    rcases lab with τ | τ
    · simp only [Sum.elim_inl, hκ, if_true]
      exact (h τ).1
    · simp only [Sum.elim_inr, hκ, if_neg hne]
      exact (h τ).2

theorem hasSig_iff (κ : c.F →+* ℂ) (ρ : c.F) (hρ : (ρ : ℂ) = H.rt0) (hκ : κ ρ = H.rt0) (p q : ℕ)
    (sm : CMType H → CMType H ⊕ CMType H) (j j' : ℕ)
    (hs : sm = Sum.inr ∧ j = p ∧ j' = q ∨ sm = Sum.inl ∧ j = q ∧ j' = p) {g : ℕ} {Λ : Type}
    [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) :
    R.HasSig (fun τ => κ.comp (labelEmb c (sm τ))) j j' ↔ HasRk H p q R := by
  rw [hasRk_iff κ ρ hρ hκ]
  refine forall_congr' fun τ => ?_
  rcases hs with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · rw [label_conj' κ τ]
    exact and_comm
  · rw [label_conj κ τ]

theorem side_cm (κ : c.F →+* ℂ) (sm : CMType H → CMType H ⊕ CMType H) (hs : sm = Sum.inr ∨ sm = Sum.inl) :
    IsCMFam fun τ => κ.comp (labelEmb c (sm τ)) := by
  rcases hs with rfl | rfl
  · exact (label_cm κ).2
  · exact (label_cm κ).1

end SheetDecomposition
end
end

section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace SheetDecomposition.Univ

theorem imH_add_left {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    ((z + z') ⬝ᵥ M *ᵥ star w).im = (z ⬝ᵥ M *ᵥ star w).im + (z' ⬝ᵥ M *ᵥ star w).im := by
  rw [add_dotProduct, Complex.add_im]

theorem imH_smul_left {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (r : ℝ) (z w : Fin g → ℂ) :
    ((r • z) ⬝ᵥ M *ᵥ star w).im = r * (z ⬝ᵥ M *ᵥ star w).im := by
  rw [smul_dotProduct, Complex.smul_im, smul_eq_mul]

theorem imH_add_right {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    (z ⬝ᵥ M *ᵥ star (w + w')).im = (z ⬝ᵥ M *ᵥ star w).im + (z ⬝ᵥ M *ᵥ star w').im := by
  rw [star_add, mulVec_add, dotProduct_add, Complex.add_im]

theorem imH_smul_right {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (r : ℝ) (z w : Fin g → ℂ) :
    (z ⬝ᵥ M *ᵥ star (r • w)).im = r * (z ⬝ᵥ M *ᵥ star w).im := by
  have h : star (r • w) = (r : ℂ) • star w := by
    ext i
    simp
  rw [h, mulVec_smul, dotProduct_smul, smul_eq_mul, Complex.im_ofReal_mul]

theorem exists_realExt {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (R R' : RiemLat E g Λ) (hf : R'.form = R.form) :
    ∃ L : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ), (∀ x, L (R.P x) = R'.P x) ∧
      (∀ z w, (L z ⬝ᵥ R'.Hm *ᵥ star (L w)).im = (z ⬝ᵥ R.Hm *ᵥ star w).im) ∧
      ∀ a z, L (R.B a z) = R'.B a (L z) := by
  classical
  haveI := R.free
  haveI := R.fin
  have hspan : Submodule.span ℝ (Set.range R.P) = ⊤ := (SheetDecomposition.riemBasic E g Λ Unit R).2.1
  let b : Module.Basis (Fin (2 * g)) ℤ Λ := Module.finBasisOfFinrankEq ℤ Λ R.rank
  let v : Fin (2 * g) → Fin g → ℂ := fun k => R.P (b k)
  have hsum : ∀ (Q : Λ →+ (Fin g → ℂ)) (x : Λ), Q x = ∑ k, (b.repr x k : ℝ) • Q (b k) := by
    intro Q x
    conv_lhs => rw [← b.sum_repr x, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, Int.cast_smul_eq_zsmul]
  have hv : (⊤ : Submodule ℝ (Fin g → ℂ)) ≤ Submodule.span ℝ (Set.range v) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [hsum R.P x]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hcard : Fintype.card (Fin (2 * g)) = Module.finrank ℝ (Fin g → ℂ) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
  let c : Module.Basis (Fin (2 * g)) ℝ (Fin g → ℂ) := basisOfTopLeSpanOfCardEqFinrank v hv hcard
  have hc : ∀ k, c k = R.P (b k) := fun k => by
    simp [c, v, coe_basisOfTopLeSpanOfCardEqFinrank]
  let L : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) := c.constr ℝ fun k => R'.P (b k)
  have hLb : ∀ k, L (R.P (b k)) = R'.P (b k) := fun k => by
    rw [← hc k]
    exact c.constr_basis ℝ _ k
  have hL : ∀ x, L (R.P x) = R'.P x := by
    intro x
    rw [hsum R.P x, hsum R'.P x, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hLb]
  have hall : ∀ z : Fin g → ℂ, z ∈ Submodule.span ℝ (Set.range R.P) := fun z => hspan ▸ Submodule.mem_top
  refine ⟨L, hL, ?_, ?_⟩
  · have h1 : ∀ (x : Λ) (w : Fin g → ℂ),
        (L (R.P x) ⬝ᵥ R'.Hm *ᵥ star (L w)).im = (R.P x ⬝ᵥ R.Hm *ᵥ star w).im := by
      intro x w
      induction hall w using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨y, rfl⟩ := hw
        rw [hL, hL, R'.im, R.im, hf]
      | zero => simp
      | add w w' _ _ h h' => rw [map_add, imH_add_right, imH_add_right, h, h']
      | smul r w _ h => rw [map_smul, imH_smul_right, imH_smul_right, h]
    intro z w
    induction hall z using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      exact h1 x w
    | zero => simp
    | add z z' _ _ h h' => rw [map_add, imH_add_left, imH_add_left, h, h']
    | smul r z _ h => rw [map_smul, imH_smul_left, imH_smul_left, h]
  · intro a z
    induction hall z using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      rw [← R.act, hL, hL, R'.act]
    | zero => simp
    | add z z' _ _ h h' => simp only [map_add, h, h']
    | smul r z _ h =>
      rw [LinearMap.map_smul_of_tower, map_smul, h, map_smul, LinearMap.map_smul_of_tower]

end SheetDecomposition.Univ
end
end

section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace SheetDecomposition.Univ.Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

def Tan (_ : RiemLat E g Λ) : Type := Fin g → ℂ

instance (R : RiemLat E g Λ) : AddCommGroup (Tan R) := inferInstanceAs (AddCommGroup (Fin g → ℂ))

instance (R : RiemLat E g Λ) : Module ℂ (Tan R) := inferInstanceAs (Module ℂ (Fin g → ℂ))

instance (R : RiemLat E g Λ) : FiniteDimensional ℂ (Tan R) := inferInstanceAs (FiniteDimensional ℂ (Fin g → ℂ))

theorem ip_conj' (R : RiemLat E g Λ) (x y : Fin g → ℂ) : starRingEnd ℂ (R.ip x y) = R.ip y x := by
  show star (y ⬝ᵥ R.Hm *ᵥ star x) = x ⬝ᵥ R.Hm *ᵥ star y
  rw [← star_dotProduct_star, star_mulVec, star_star, R.herm.eq, dotProduct_mulVec]

theorem ip_add_right' (R : RiemLat E g Λ) (x y y' : Fin g → ℂ) : R.ip x (y + y') = R.ip x y + R.ip x y' := by
  simp [RiemLat.ip, add_dotProduct]

theorem ip_smul_right' (R : RiemLat E g Λ) (c : ℂ) (x y : Fin g → ℂ) : R.ip x (c • y) = c * R.ip x y := by
  simp [RiemLat.ip, smul_dotProduct]

theorem ip_add_left' (R : RiemLat E g Λ) (x x' y : Fin g → ℂ) : R.ip (x + x') y = R.ip x y + R.ip x' y := by
  rw [← ip_conj' R y, ip_add_right', map_add, ip_conj', ip_conj']

theorem ip_smul_left' (R : RiemLat E g Λ) (c : ℂ) (x y : Fin g → ℂ) :
    R.ip (c • x) y = starRingEnd ℂ c * R.ip x y := by
  rw [← ip_conj' R y, ip_smul_right', map_mul, ip_conj']

theorem ip_self_nonneg' (R : RiemLat E g Λ) (x : Fin g → ℂ) : 0 ≤ (R.ip x x).re := by
  by_cases hx : x = 0
  · subst hx
    simp [RiemLat.ip]
  · exact (R.pos x hx).le

theorem ip_self_zero' (R : RiemLat E g Λ) {x : Fin g → ℂ} (h : R.ip x x = 0) : x = 0 := by
  by_contra hx
  have := R.pos x hx
  change 0 < (R.ip x x).re at this
  rw [h] at this
  simp at this

def core (R : RiemLat E g Λ) : InnerProductSpace.Core ℂ (Tan R) where
  inner x y := R.ip x y
  conj_inner_symm x y := ip_conj' R y x
  re_inner_nonneg x := ip_self_nonneg' R x
  add_left x y z := ip_add_left' R x y z
  smul_left x y r := ip_smul_left' R r x y
  definite x h := ip_self_zero' R h

theorem exists_orthoBasis (R : RiemLat E g Λ) (S : Submodule ℂ (Fin g → ℂ)) (m : ℕ)
    (h : Module.finrank ℂ S = m) :
    ∃ e : Fin m → Fin g → ℂ, (∀ c, e c ∈ S) ∧ (∀ a b, R.ip (e a) (e b) = if a = b then 1 else 0) ∧
      S ≤ Submodule.span ℂ (Set.range e) := by
  letI : NormedAddCommGroup (Tan R) := (core R).toNormedAddCommGroup
  letI : InnerProductSpace ℂ (Tan R) := InnerProductSpace.ofCore (core R).toCore
  let S' : Submodule ℂ (Tan R) := S
  have h' : Module.finrank ℂ S' = m := h
  let b := (stdOrthonormalBasis ℂ S').reindex (finCongr h')
  refine ⟨fun c => ((b c : S') : Tan R), fun c => (b c).2, fun x y => ?_, fun x hx => ?_⟩
  · exact orthonormal_iff_ite.1 b.orthonormal x y
  · have hb : Submodule.span ℂ (Set.range b) = ⊤ := by simpa using b.toBasis.span_eq
    have hm := congrArg (Submodule.map S'.subtype) hb
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at hm
    have hx' : x ∈ S' := hx
    rw [← hm] at hx'
    exact hx'

theorem linearIndependent_of_ortho (R : RiemLat E g Λ) {I : Type} [DecidableEq I] (c : I → Fin g → ℂ)
    (h : ∀ i i', R.ip (c i) (c i') = if i = i' then 1 else 0) : LinearIndependent ℂ c := by
  letI : NormedAddCommGroup (Tan R) := (core R).toNormedAddCommGroup
  letI : InnerProductSpace ℂ (Tan R) := InnerProductSpace.ofCore (core R).toCore
  let c' : I → Tan R := c
  have ho : Orthonormal ℂ c' := orthonormal_iff_ite.2 h
  exact ho.linearIndependent

variable {Ψ : Type} [Fintype Ψ]

theorem cm_ne {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ) (τ τ' : Ψ) :
    σ τ ≠ (starRingEnd ℂ).comp (σ τ') := fun h =>
  ((hσ.2 (σ τ')).1 ⟨τ', rfl⟩) ⟨τ, h⟩

theorem conj_comp_conj (s : 𝓞 E →+* ℂ) : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s := by
  ext a
  simp

theorem cm_cover {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ) (s : 𝓞 E →+* ℂ) :
    (∃ τ, σ τ = s) ∨ ∃ τ, (starRingEnd ℂ).comp (σ τ) = s := by
  by_cases h : ∃ τ, σ τ = s
  · exact Or.inl h
  · right
    have h2 : ∃ τ, σ τ = (starRingEnd ℂ).comp s := by
      by_contra h3
      exact h ((hσ.2 s).2 h3)
    obtain ⟨τ, hτ⟩ := h2
    exact ⟨τ, by rw [hτ, conj_comp_conj]⟩

theorem exists_ortho_frame {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (R₀ : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (hσ : IsCMFam σ) (hs : R₀.HasSig σ j j') :
    ∃ (e : Ix Ψ j j' ≃ Fin g) (c : Ix Ψ j j' → Fin g → ℂ), (∀ i, c i ∈ eigSp R₀.B (emb σ i)) ∧
      ∀ i i', R₀.ip (c i) (c i') = if i = i' then 1 else 0 := by
  obtain ⟨-, -, h3, h4, h5⟩ := SheetDecomposition.riemBasic E g Λ Ψ R₀
  choose f hf1 hf2 hf3 using fun τ => exists_orthoBasis R₀ _ j' (hs τ).1
  choose f' hf1' hf2' hf3' using fun τ => exists_orthoBasis R₀ _ j (hs τ).2
  let c : Ix Ψ j j' → Fin g → ℂ := fun i => Sum.elim (f i.2) (f' i.2) i.1
  have hmem : ∀ i, c i ∈ eigSp R₀.B (emb σ i) := by
    rintro ⟨a | a, τ⟩
    · exact hf1 τ a
    · exact hf1' τ a
  have hinj' : ∀ {τ τ' : Ψ}, τ ≠ τ' → (starRingEnd ℂ).comp (σ τ) ≠ (starRingEnd ℂ).comp (σ τ') := by
    intro τ τ' hne h
    apply hne
    apply hσ.1
    rw [← conj_comp_conj (σ τ), h, conj_comp_conj]
  have hort : ∀ i i', R₀.ip (c i) (c i') = if i = i' then 1 else 0 := by
    rintro ⟨a | a, τ⟩ ⟨b | b, τ'⟩
    · by_cases ht : τ = τ'
      · subst ht
        have := hf2 τ a b
        simpa [c] using this
      · have := h5 _ _ (fun h => ht (hσ.1 h)) _ (hf1 τ a) _ (hf1 τ' b)
        simpa [c, ht] using this
    · have := h5 _ _ (cm_ne hσ τ τ') _ (hf1 τ a) _ (hf1' τ' b)
      simpa [c] using this
    · have := h5 _ _ (cm_ne hσ τ' τ).symm _ (hf1' τ a) _ (hf1 τ' b)
      simpa [c] using this
    · by_cases ht : τ = τ'
      · subst ht
        have := hf2' τ a b
        simpa [c] using this
      · have := h5 _ _ (hinj' ht) _ (hf1' τ a) _ (hf1' τ' b)
        simpa [c, ht] using this
  have hli : LinearIndependent ℂ c := linearIndependent_of_ortho R₀ c hort
  have hsp1 : ∀ τ, eigSp R₀.B (σ τ) ≤ Submodule.span ℂ (Set.range c) := fun τ =>
    (hf3 τ).trans (Submodule.span_mono (by
      rintro _ ⟨a, rfl⟩
      exact ⟨(Sum.inl a, τ), rfl⟩))
  have hsp2 : ∀ τ, eigSp R₀.B ((starRingEnd ℂ).comp (σ τ)) ≤ Submodule.span ℂ (Set.range c) := fun τ =>
    (hf3' τ).trans (Submodule.span_mono (by
      rintro _ ⟨a, rfl⟩
      exact ⟨(Sum.inr a, τ), rfl⟩))
  have hsp : ∀ s : 𝓞 E →+* ℂ, eigSp R₀.B s ≤ Submodule.span ℂ (Set.range c) := by
    intro s
    rcases cm_cover hσ s with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
    · exact hsp1 τ
    · exact hsp2 τ
  have htop : ⊤ ≤ Submodule.span ℂ (Set.range c) := by
    intro x _
    rw [← h4 x]
    exact Submodule.sum_mem _ fun s _ => hsp _ ((h3 _).1 x)
  have hcard : Fintype.card (Ix Ψ j j') = g := by
    have := Module.finrank_eq_card_basis (Module.Basis.mk hli htop)
    simpa using this.symm
  exact ⟨Fintype.equivFinOfCardEq hcard, c, hmem, hort⟩

end SheetDecomposition.Univ.Frame
end
end

section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace SheetDecomposition.Univ

section Tz

variable {I : Type} [Fintype I]

theorem tz_add (Z : Matrix I I ℂ) (z w : I → ℂ) : tz Z (z + w) = tz Z z + tz Z w := by
  simp only [tz, star_add, mulVec_add]
  abel

theorem tz_I (Z : Matrix I I ℂ) (z : I → ℂ) :
    tz Z (Complex.I • z) = Complex.I • (z + Z *ᵥ star z) := by
  have h : star (Complex.I • z) = (-Complex.I) • star z := by
    funext i
    simp
  rw [tz, h, mulVec_smul, smul_add]
  funext i
  simp

def tzR (Z : Matrix I I ℂ) : (I → ℂ) →ₗ[ℝ] (I → ℂ) where
  toFun := tz Z
  map_add' := tz_add Z
  map_smul' r z := by
    have h : star (r • z) = r • star z := by
      funext i
      simp
    simp only [tz, h, RingHom.id_apply, smul_sub]
    rw [mulVec_smul]

theorem tz_support [DecidableEq I] (Z : Matrix I I ℂ) (d : I → ℂ) (M : (I → ℂ) →ₗ[ℂ] (I → ℂ))
    (h : ∀ z, tz Z (d * z) = M (tz Z z)) (i k : I) : d i * Z i k = Z i k * star (d k) := by
  have h2 : ∀ z : I → ℂ, d * z + Z *ᵥ star (d * z) = M z + M (Z *ᵥ star z) := by
    intro z
    have e : d * (Complex.I • z) = Complex.I • (d * z) := by
      funext i
      simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have := h (Complex.I • z)
    rw [e, tz_I, tz_I, map_smul, map_add] at this
    exact smul_right_injective _ Complex.I_ne_zero this
  have h1 : ∀ z : I → ℂ, d * z - Z *ᵥ star (d * z) = M z - M (Z *ᵥ star z) := by
    intro z
    have := h z
    rwa [tz, tz, map_sub] at this
  have h3 : ∀ z : I → ℂ, d * z = M z := by
    intro z
    funext a
    have a1 := congrFun (h1 z) a
    have a2 := congrFun (h2 z) a
    simp only [Pi.sub_apply, Pi.add_apply] at a1 a2
    linear_combination (a1 + a2) / 2
  have h4 : ∀ z : I → ℂ, Z *ᵥ star (d * z) = d * (Z *ᵥ star z) := by
    intro z
    rw [h3 (Z *ᵥ star z)]
    funext a
    have a1 := congrFun (h1 z) a
    have a2 := congrFun (h2 z) a
    simp only [Pi.sub_apply, Pi.add_apply] at a1 a2
    linear_combination (a2 - a1) / 2
  have := congrFun (h4 (Pi.single k 1)) i
  have s1 : star (d * (Pi.single k 1 : I → ℂ)) = Pi.single k (star (d k)) := by
    funext a
    by_cases hak : a = k
    · subst hak
      simp
    · simp [Pi.single_eq_of_ne hak]
  have s2 : star (Pi.single k 1 : I → ℂ) = Pi.single k 1 := by
    funext a
    by_cases hak : a = k
    · subst hak
      simp
    · simp [Pi.single_eq_of_ne hak]
  rw [s1, s2] at this
  simp only [Pi.mul_apply, mulVec_single, MulOpposite.op_mul] at this
  simpa [mul_comm] using this.symm

theorem tz_unique [DecidableEq I] (S : Set (I → ℂ)) (hS : Submodule.span ℝ S = ⊤) (A A' : (I → ℂ) ≃ₗ[ℂ] (I → ℂ))
    (Z Z' : Matrix I I ℂ) (h : ∀ z ∈ S, A (tz Z z) = A' (tz Z' z)) : Z = Z' := by
  have hall : ∀ z, A (tz Z z) = A' (tz Z' z) := by
    have hf : (A.toLinearMap.restrictScalars ℝ) ∘ₗ tzR Z = (A'.toLinearMap.restrictScalars ℝ) ∘ₗ tzR Z' :=
      LinearMap.ext_on hS fun z hz => h z hz
    exact fun z => LinearMap.congr_fun hf z
  have h2 : ∀ z : I → ℂ, A (z + Z *ᵥ star z) = A' (z + Z' *ᵥ star z) := by
    intro z
    have := hall (Complex.I • z)
    rw [tz_I, tz_I, map_smul, map_smul] at this
    exact smul_right_injective _ Complex.I_ne_zero this
  have h3 : ∀ z : I → ℂ, A z = A' z := by
    intro z
    funext a
    have a1 := congrFun (hall z) a
    have a2 := congrFun (h2 z) a
    simp only [tz, map_sub, map_add, Pi.sub_apply, Pi.add_apply] at a1 a2
    linear_combination (a1 + a2) / 2
  have h4 : ∀ z : I → ℂ, Z *ᵥ star z = Z' *ᵥ star z := by
    intro z
    apply A.injective
    have := h2 z
    rw [map_add, map_add, h3 z] at this
    rw [h3 (Z' *ᵥ star z)]
    exact add_left_cancel this
  ext i k
  have := congrFun (h4 (Pi.single k 1)) i
  have s2 : star (Pi.single k 1 : I → ℂ) = Pi.single k 1 := by
    funext a
    by_cases hak : a = k
    · subst hak
      simp
    · simp [Pi.single_eq_of_ne hak]
  rw [s2] at this
  simpa using this

end Tz

section Big

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ}

theorem bigZe_symm (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) :
    (bigZe e q t)ᵀ = bigZe e q t := by
  unfold bigZe bigZ
  rw [transpose_submatrix, blockDiagonal_transpose]
  congr 2
  funext τ
  rw [fromBlocks_transpose]
  simp

theorem bigZ_entry (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (τ : Ψ) (a : Fin j) (b : Fin j') :
    bigZ q t (Sum.inr a, τ) (Sum.inl b, τ) = t (q (τ, a, b)) := by
  simp [bigZ, blockDiagonal_apply_eq, ballMat]

theorem bigZe_injective (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) :
    Function.Injective (bigZe e q) := by
  intro t t' h
  funext k
  obtain ⟨⟨τ, a, b⟩, rfl⟩ := q.surjective k
  have := congrFun (congrFun h (e (Sum.inr a, τ))) (e (Sum.inl b, τ))
  simpa [bigZe, bigZ_entry] using this

theorem bigZ_hol (q : Ψ × Fin j × Fin j' ≃ Fin n) (i k : Ix Ψ j j') :
    Differentiable ℂ (fun t => bigZ q t i k) := by
  obtain ⟨a, τ⟩ := i
  obtain ⟨b, τ'⟩ := k
  by_cases h : τ = τ'
  · subst h
    rcases a with a | a <;> rcases b with b | b <;>
      simp [bigZ, blockDiagonal_apply_eq, ballMat, differentiable_apply]
  · simp [bigZ, blockDiagonal_apply_ne _ _ _ h]

theorem bigZe_hol (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) (z : Fin g → ℂ) :
    Differentiable ℂ (fun t => tz (bigZe e q t) z) := by
  refine differentiable_pi.2 fun i => ?_
  simp only [tz, Pi.sub_apply, mulVec, dotProduct, bigZe, submatrix_apply]
  refine (differentiable_const _).sub (Differentiable.fun_sum fun k _ => ?_)
  exact (bigZ_hol q _ _).mul_const _

end Big

theorem member {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    (R₁ : RiemLat E g Λ) (Z : Matrix (Fin g) (Fin g) ℂ) (hH : R₁.Hm = 1) (hs : Zᵀ = Z) (hp : (1 - Zᴴ * Z).PosDef)
    (hc : ∀ a x, tz Z (R₁.B a x) = R₁.B a (tz Z x)) :
    ∃ R : RiemLat E g Λ, R.form = R₁.form ∧ R.B = R₁.B ∧ R.Hm = (1 - Zᴴ * Z)⁻¹ ∧ ∀ x, R.P x = tz Z (R₁.P x) := by
  have hinv : ((1 - Zᴴ * Z)⁻¹).PosDef := hp.inv
  let P : Λ →+ (Fin g → ℂ) :=
    { toFun := fun x => tz Z (R₁.P x)
      map_zero' := by simp [tz]
      map_add' := fun x y => by rw [map_add, tz_add] }
  refine ⟨{ free := R₁.free, fin := R₁.fin, rank := R₁.rank, form := R₁.form, alt := R₁.alt, unimod := R₁.unimod,
            adj := R₁.adj, P := P, Hm := (1 - Zᴴ * Z)⁻¹, herm := hinv.isHermitian, pos := ?_, im := ?_, B := R₁.B,
            act := ?_ }, rfl, rfl, rfl, fun _ => rfl⟩
  · intro z hz
    have h := (Matrix.posDef_iff_dotProduct_mulVec.1 hinv).2 (x := star z) (by simpa using hz)
    rw [star_star, Complex.lt_def] at h
    exact h.1
  · intro x y
    show (tz Z (R₁.P x) ⬝ᵥ (1 - Zᴴ * Z)⁻¹ *ᵥ star (tz Z (R₁.P y))).im = _
    rw [GlobalTheory.T.siegel_transform_symplectic_imaginary Z hs hp, ← R₁.im, hH, one_mulVec]
  · intro a x
    show tz Z (R₁.P (a • x)) = R₁.B a (tz Z (R₁.P x))
    rw [R₁.act, hc]

theorem exists_univFam : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R₀ : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (q : Ψ × Fin j × Fin j' ≃ Fin n), IsCMFam σ → R₀.HasSig σ j j' → ∃ F : UnivFam E Ψ j j' n g Λ, F.q = q ∧ F.σ = σ ∧ F.form = R₀.form := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ R₀ σ q hσ hsig
  classical
  obtain ⟨e, c, hc, hco⟩ := Frame.exists_ortho_frame R₀ σ hσ hsig
  obtain ⟨R₁, hform, hHm, hB⟩ := GlobalTheory.T.exists_normalized_riemann_lattice R₀ σ e c hc hco
  have hmem : ∀ t, ∃ R : RiemLat E g Λ, R.form = R₀.form ∧ (t ∈ ballDom q → R.B = R₁.B ∧
      R.Hm = (1 - (bigZe e q t)ᴴ * bigZe e q t)⁻¹ ∧ ∀ x, R.P x = tz (bigZe e q t) (R₁.P x)) := by
    intro t
    by_cases ht : t ∈ ballDom q
    · obtain ⟨R, h1, h2, h3, h4⟩ := member R₁ (bigZe e q t) hHm (bigZe_symm e q t)
        ((GlobalTheory.T.ball_domain_iff_pos_def e q t).1 ht) (GlobalTheory.T.siegel_transform_commutes_action σ e q t R₁.B hσ hB)
      exact ⟨R, h1.trans hform, fun _ => ⟨h2, h3, h4⟩⟩
    · exact ⟨R₁, hform, fun h => absurd h ht⟩
  choose R hRf hR using hmem
  have hfr := GlobalTheory.T.span_standard_basis_eigenspace σ e R₁.B hσ hB
  have hli : ∀ {m : ℕ} (f : Fin m → Ix Ψ j j'), Function.Injective f →
      LinearIndependent ℂ (fun i : Fin m => (Pi.single (e (f i)) 1 : Fin g → ℂ)) := by
    intro m f hf
    have := (Pi.basisFun ℂ (Fin g)).linearIndependent.comp (fun i => e (f i))
      (e.injective.comp hf)
    simpa [Function.comp_def, Pi.basisFun_apply] using this
  have hl : ∀ τ, LinearIndependent ℂ (fun i : Fin j' => (Pi.single (e (Sum.inl i, τ)) 1 : Fin g → ℂ)) := fun τ =>
    hli (fun i => (Sum.inl i, τ)) (fun a b h => by simpa using h)
  have hr : ∀ τ, LinearIndependent ℂ (fun i : Fin j => (Pi.single (e (Sum.inr i, τ)) 1 : Fin g → ℂ)) := fun τ =>
    hli (fun i => (Sum.inr i, τ)) (fun a b h => by simpa using h)
  refine ⟨{ q := q, σ := σ, cm := hσ, form := R₀.form, R := R, form_eq := hRf,
            hol := ?_, sig := ?_, b := fun τ i _ => Pi.single (e (Sum.inl i, τ)) 1,
            frames := ?_, logDet_eq := ?_, univ := ?_ }, rfl, rfl, rfl⟩
  · refine ⟨fun t _ t' _ => (hRf t).trans (hRf t').symm, fun x => ?_⟩
    exact ((bigZe_hol e q (R₁.P x)).differentiableOn).congr fun t ht => (hR t ht).2.2 x
  · intro t ht τ
    rw [(hR t ht).1, ← (hfr τ).1, ← (hfr τ).2]
    exact ⟨by rw [finrank_span_eq_card (hl τ)]; simp, by rw [finrank_span_eq_card (hr τ)]; simp⟩
  · refine ⟨fun τ i => differentiableOn_const _, fun t ht τ => ⟨hl τ, ?_⟩⟩
    show _ = eigSp (R t).B (σ τ)
    rw [(hR t ht).1]
    exact (hfr τ).1
  · intro t ht
    exact GlobalTheory.T.log_det_eq_ball_potential e q t (R t) ht (hR t ht).2.1
  · intro R' hR' _
    obtain ⟨L, hL1, hL2, hL3⟩ := exists_realExt R₁ R' (hR'.trans hform.symm)
    obtain ⟨A, Z, hZs, hZp, hLZ⟩ := GlobalTheory.T.siegel_normal_form_of_hermitian L R'.Hm R'.herm R'.pos (by
      intro z w
      rw [hL2, hHm, one_mulVec])
    have hsupp : ∀ (a : 𝓞 E) i k, emb σ (e.symm i) a * Z i k = Z i k * star (emb σ (e.symm k) a) := by
      intro a
      refine tz_support Z (fun k => emb σ (e.symm k) a)
        (A.symm.toLinearMap ∘ₗ (R'.B a) ∘ₗ A.toLinearMap) fun z => ?_
      have hz : (fun k => emb σ (e.symm k) a) * z = R₁.B a z := by
        funext k
        simp [hB]
      apply A.injective
      rw [hz]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      rw [← hLZ, ← hLZ, hL3]
    have hZ0 : ∀ i k, Z i k ≠ 0 → (e.symm i).2 = (e.symm k).2 ∧ (e.symm i).1.isLeft ≠ (e.symm k).1.isLeft := by
      intro i k hik
      refine (GlobalTheory.T.conjugate_embeddings_criterion σ hσ (e.symm i) (e.symm k)).1 fun a => ?_
      have := hsupp a i k
      rw [mul_comm] at this
      exact mul_left_cancel₀ hik this
    obtain ⟨t, rfl⟩ := GlobalTheory.T.symmetric_pattern_matrix_mem_range_bigZe e q Z hZs hZ0
    have ht : t ∈ ballDom q := (GlobalTheory.T.ball_domain_iff_pos_def e q t).2 hZp
    refine ⟨t, ⟨ht, A, fun x => ?_⟩, ?_⟩
    · rw [(hR t ht).2.2 x, ← hLZ, hL1]
      rfl
    · rintro t' ⟨ht', h', hh⟩
      have hspan := (SheetDecomposition.riemBasic E g Λ Ψ R₁).2.1
      refine bigZe_injective e q (tz_unique _ hspan h' A _ _ ?_)
      rintro _ ⟨x, rfl⟩
      rw [← (hR t' ht').2.2 x, ← hh x, ← hLZ, hL1]
      rfl

end SheetDecomposition.Univ

theorem SheetDecomposition.univExists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R₀ : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (q : Ψ × Fin j × Fin j' ≃ Fin n), IsCMFam σ → R₀.HasSig σ j j' → ∃ F : UnivFam E Ψ j j' n g Λ, F.q = q ∧ F.σ = σ ∧ F.form = R₀.form :=
  SheetDecomposition.Univ.exists_univFam
end
end

section
noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem exists_equiv_of_det {g : ℕ} (h : Matrix (Fin g) (Fin g) ℂ) (hd : IsUnit h.det) :
    ∃ e : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e z = h *ᵥ z :=
  ⟨h.toLinearEquiv' (h.invertibleOfIsUnitDet hd), fun z => Matrix.toLin'_apply h z⟩

theorem u_eq_of_equiv {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σ ty) (i : Fin FU.n)
    {P P' Q : (FU.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (FU.Di i) ty P) (hP' : IsPeriod (FU.Di i) ty P')
    (e e' : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (he : ∀ x, P x = e (Q x)) (he' : ∀ x, P' x = e' (Q x)) :
    FU.u i P = FU.u i P' :=
  (FU.fibre i P P' hP hP').2 ⟨LinearEquiv.refl _ _, e.symm.trans e', fun _ _ => rfl, fun a _ => ⟨0, by simp⟩,
    fun a => ⟨0, by simp⟩, fun a => by simp [he, he']⟩

theorem j_over (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (κ : c.F →+* ℂ) (x : Sp ℂ ⟶ Xo.XF c)
    (hx : x ≫ pullback.snd _ _ = spMap κ) : (x ≫ Y.j) ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F)) := by
  rw [Category.assoc, Model.j, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hx,
    spMap_comp]

theorem j_inj (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) {x x' : Sp ℂ ⟶ Xo.XF c}
    (hx : x ≫ pullback.snd _ _ = x' ≫ pullback.snd _ _) (h : x ≫ Y.j = x' ≫ Y.j) : x = x' := by
  have := Y.jQ_open
  rw [← cancel_mono Y.jQ]
  apply pullback.hom_ext
  · simpa [Model.j] using h
  · rw [Category.assoc, Category.assoc, Y.jQ_over, hx]

theorem j_interior (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (x : Sp ℂ ⟶ Xo.XF c) :
    centre (x ≫ Y.j) ∈ abLocus Y.t.G := by
  have h : Y.jQ (centre x) ∈ pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) ⁻¹' abLocus Y.t.G := by
    rw [Y.ab_gen]
    exact ⟨_, rfl⟩
  exact h

theorem exists_j (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (κ : c.F →+* ℂ) (p : Sp ℂ ⟶ Y.X)
    (hp : centre p ∈ abLocus Y.t.G) (hs : p ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F))) :
    ∃ x : Sp ℂ ⟶ Xo.XF c, x ≫ Y.j = p ∧ x ≫ pullback.snd _ _ = spMap κ := by
  have hc : p ≫ Y.s = spMap κ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by rw [hs, spMap_comp]
  let w : Sp ℂ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) := pullback.lift p (spMap κ) hc
  have hw₁ : w ≫ pullback.fst _ _ = p := pullback.lift_fst _ _ _
  have hw₂ : w ≫ pullback.snd _ _ = spMap κ := pullback.lift_snd _ _ _
  have := Y.jQ_open
  have hr : Set.range w ⊆ Set.range Y.jQ := by
    rintro _ ⟨u, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, hw₁]
    have hu : u = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst hu
    exact hp
  have hx : IsOpenImmersion.lift Y.jQ w hr ≫ Y.jQ = w := IsOpenImmersion.lift_fac _ _ _
  refine ⟨IsOpenImmersion.lift Y.jQ w hr, ?_, ?_⟩
  · rw [Model.j, ← Category.assoc, hx, hw₁]
  · rw [← Y.jQ_over, ← Category.assoc, hx, hw₂]

theorem isHolTo_of_j (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (κ : c.F →+* ℂ) {m : ℕ} {T : Set (Fin m → ℂ)}
    {x : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.XF c)} (hT : IsOpen T) (hs : ∀ b, x b ≫ pullback.snd _ _ = spMap κ)
    (h : IsHolTo T fun b => x b ≫ Y.j) : IsHolTo T x := by
  have := Y.jQ_open
  have he : ∀ b, (x b ≫ Y.j) ≫ Y.s = spMap κ ≫ spMap (algebraMap (𝓞 c.F) c.F) := fun b => by
    rw [j_over Y κ _ (hs b), spMap_comp]
  have hq : ∀ b, x b ≫ Y.jQ = pullback.lift (x b ≫ Y.j) (spMap κ) (he b) := fun b => by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc]
      rfl
    · rw [pullback.lift_snd, Category.assoc, Y.jQ_over, hs]
  have h₃ : IsHolTo T fun b => x b ≫ Y.jQ := by
    have := PullbackSections.holPair _ _ _ Y.s (spMap (algebraMap (𝓞 c.F) c.F)) m T (fun b => x b ≫ Y.j) (fun _ => spMap κ) he hT h
      (PullbackSections.isHolTo_spMap hT (Ψ := fun _ => κ) fun a => differentiableOn_const _)
    simpa only [hq] using this
  exact Flat.isHolTo_of_comp_openImmersion Y.jQ h₃

set_option maxHeartbeats 1600000 in
theorem kUnif_good (hV : VecOfPeriods) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (sm : CMType H → CMType H ⊕ CMType H)
    (j j' n g : ℕ) (q : CMType H × Fin j × Fin j' ≃ Fin n) (κ : c.F →+* ℂ) (ty : Fin g → (E →+* ℂ))
    (hty : IsTypeFn H D.p D.q ty) (hs : sm = Sum.inr ∧ j = D.p ∧ j' = D.q ∨ sm = Sum.inl ∧ j = D.q ∧ j' = D.p)
    (ρ : c.F) (hρ : (ρ : ℂ) = H.rt0) (hκ : κ ρ = H.rt0)
    (FU : FamilyUnif Xo (κ.comp (IntermediateField.inclusion c.le).toRingHom) ty) :
    Nonempty (KUnif Y sm j j' n g q κ) := by
  classical
  let ι : Type := {i : Fin FU.n // ∃ P, IsPeriod (FU.Di i) ty P}
  have htyi : ∀ i, IsTypeFn H (FU.Di i).p (FU.Di i).q ty := fun i => by
    rw [(FU.sig i).1, (FU.sig i).2]
    exact hty
  have hsig : ∀ {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ),
      R.HasSig (fun τ => κ.comp (labelEmb c (sm τ))) j j' ↔ HasRk H D.p D.q R :=
    fun R => hasSig_iff κ ρ hρ hκ D.p D.q sm j j' hs R
  have hriem : ∀ i P, IsPeriod (FU.Di i) ty P → ∃ R : RiemLat E g (FU.Di i).La, R.P = P ∧ R.form = (FU.Di i).EF ∧
      R.HasSig (fun τ => κ.comp (labelEmb c (sm τ))) j j' := fun i P hP => by
    obtain ⟨R, h₁, h₂, -, h₄⟩ := GlobalTheory.T.exists_riemann_lattice_of_period E H (FU.Di i) g ty P (htyi i) hP
    rw [(FU.sig i).1, (FU.sig i).2] at h₄
    exact ⟨R, h₁, h₂, (hsig R).2 h₄⟩
  have hF : ∀ k : ι, ∃ F : UnivFam E (CMType H) j j' n g (FU.Di k.1).La, F.q = q ∧
      F.σ = (fun τ => κ.comp (labelEmb c (sm τ))) ∧ F.form = (FU.Di k.1).EF := fun k => by
    obtain ⟨P, hP⟩ := k.2
    obtain ⟨R, -, h₂, h₃⟩ := hriem _ P hP
    obtain ⟨F, a₁, a₂, a₃⟩ := univExists E (CMType H) j j' n g _ R _ q
      (side_cm κ sm (hs.imp (·.1) (·.1))) h₃
    exact ⟨F, a₁, a₂, a₃.trans h₂⟩
  choose F hq hσ hform using hF
  have hΓ : ∀ k : ι, ∃ Γ : Subgroup ((FU.Di k.1).La ≃ₗ[𝓞 E] (FU.Di k.1).La), (F k).IsArith Γ ∧
      ∀ γ, γ ∈ Γ ↔ InLevel l (FU.Di k.1) γ := fun k => by
    haveI := ((F k).R 0).fin
    obtain ⟨Γ, a₁, a₂, a₃⟩ := GlobalTheory.T.congruence_subgroup_of_form_automorphisms E (FU.Di k.1).La (FU.Di k.1).EF (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) l.M l.A
      (by have := l.three_le; omega) l.A_pos
    refine ⟨Γ, ?_, a₃⟩
    unfold UnivFam.IsArith
    rw [hform]
    exact ⟨a₁, a₂⟩
  choose Γ hΓa hΓm using hΓ
  have hO : IsOpen (ballDom q) := (GlobalTheory.T.ball_domain_open_convex_zero _ j j' n q).1
  have hRf : ∀ k t, ((F k).R t).form = (FU.Di k.1).EF := fun k t => ((F k).form_eq t).trans (hform k)
  have hloc : ∀ k : ι, ∀ t₀ ∈ ballDom q, ∃ (V' : Set (Fin n → ℂ)) (P : (Fin n → ℂ) → ((FU.Di k.1).La →+ (Fin g → ℂ)))
      (h : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen V' ∧ t₀ ∈ V' ∧ V' ⊆ ballDom q ∧
      IsHolPeriods (FU.Di k.1) ty V' P ∧ (∀ a b, DifferentiableOn ℂ (fun t => h t a b) V') ∧
      ∀ t ∈ V', IsUnit (h t).det ∧ ∀ x, P t x = h t *ᵥ ((F k).R t).P x := fun k =>
    GlobalTheory.T.local_holomorphic_period_family E H (FU.Di k.1) g n ty (ballDom q) (F k).R (htyi _) hO (hq k ▸ (F k).hol) fun t ht => ⟨hRf k t, by
      rw [(FU.sig _).1, (FU.sig _).2]
      refine (hsig _).1 ?_
      rw [← hσ k]
      exact (F k).sig t (by rw [hq]; exact ht)⟩
  have hPt : ∀ (k : ι) (t : Fin n → ℂ), ∃ P, IsPeriod (FU.Di k.1) ty P ∧ (t ∈ ballDom q →
      ∃ e : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ x, P x = e (((F k).R t).P x)) := fun k t => by
    by_cases ht : t ∈ ballDom q
    · obtain ⟨V', P, h, -, hm, -, hP, -, hh⟩ := hloc k t ht
      obtain ⟨e, he⟩ := exists_equiv_of_det (h t) (hh t hm).1
      exact ⟨P t, hP.1 t hm, fun _ => ⟨e, fun x => by rw [he, (hh t hm).2]⟩⟩
    · obtain ⟨P, hP⟩ := k.2
      exact ⟨P, hP, fun h => absurd h ht⟩
  choose Pt hPt hPe using hPt
  have hu : ∀ (k : ι), ∀ t ∈ ballDom q, ∀ P, IsPeriod (FU.Di k.1) ty P → ∀ e : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ),
      (∀ x, P x = e (((F k).R t).P x)) → FU.u k.1 (Pt k t) = FU.u k.1 P := fun k t ht P hP e he => by
    obtain ⟨e₀, he₀⟩ := hPe k t ht
    exact u_eq_of_equiv FU k.1 (hPt k t) hP e₀ e he₀ he
  have hum : ∀ (k : ι), ∀ t ∈ ballDom q, ∀ P, IsPeriod (FU.Di k.1) ty P → ∀ h : Matrix (Fin g) (Fin g) ℂ, IsUnit h.det →
      (∀ x, P x = h *ᵥ ((F k).R t).P x) → FU.u k.1 (Pt k t) = FU.u k.1 P := fun k t ht P hP h hd hh => by
    obtain ⟨e, he⟩ := exists_equiv_of_det h hd
    exact hu k t ht P hP e fun x => by rw [he, hh]
  have hc : ∀ (k : ι) t, FU.u k.1 (Pt k t) ≫ Xo.s = spMap κ ≫ spMap (IntermediateField.inclusion c.le).toRingHom :=
    fun k t => by rw [FU.over_σ _ _ (hPt k t), spMap_comp]
  let xF : ι → (Fin n → ℂ) → (Sp ℂ ⟶ Xo.XF c) := fun k t => pullback.lift _ _ (hc k t)
  have hx₁ : ∀ k t, xF k t ≫ pullback.fst _ _ = FU.u k.1 (Pt k t) := fun k t => pullback.lift_fst _ _ _
  have hx₂ : ∀ k t, xF k t ≫ pullback.snd _ _ = spMap κ := fun k t => pullback.lift_snd _ _ _
  have hxhol : ∀ k, IsHolTo (ballDom q) (xF k) := fun k => by
    refine PullbackSections.holPair _ _ _ _ _ n _ _ _ (hc k) hO ?_
      (PullbackSections.isHolTo_spMap hO (Ψ := fun _ => κ) fun a => differentiableOn_const _)
    refine GlobalTheory.HolPeriods.isHolTo_of_local fun t₀ ht₀ => ?_
    obtain ⟨V', P, h, hVo, hm, hsub, hP, -, hh⟩ := hloc k t₀ ht₀
    exact ⟨V', hm, hsub, GlobalTheory.HolPeriods.isHolTo_congr (FU.hol _ n V' P hVo hP).1 fun t ht =>
      hum k t (hsub ht) _ (hP.1 t ht) _ (hh t ht).1 (hh t ht).2⟩
  have hpt : ∀ k k' t t', xF k t ≫ Y.j = xF k' t' ≫ Y.j ↔ FU.u k.1 (Pt k t) = FU.u k'.1 (Pt k' t') := fun k k' t t' => by
    constructor
    · intro h
      rw [← hx₁, ← hx₁, j_inj Y ((hx₂ k t).trans (hx₂ k' t').symm) h]
    · intro h
      congr 1
      apply pullback.hom_ext
      · rw [hx₁, hx₁, h]
      · rw [hx₂, hx₂]
  have hmono : ∀ {X : Scheme.{0}} {B B' : Set (Fin n → ℂ)} {y : (Fin n → ℂ) → (Sp ℂ ⟶ X)}, IsHolTo B y → IsOpen B' →
      B' ⊆ B → IsHolTo B' y := fun h hB hsub => GlobalTheory.HolPeriods.isHolTo_comp (φ := id) h hB differentiableOn_id hsub
  refine ⟨{
    ι := ι
    fin := inferInstance
    Di := fun k => FU.Di k.1
    sig := fun k => FU.sig k.1
    F := F
    q_eq := hq
    form_eq := fun k => Or.inl (hform k)
    σ_eq := fun k τ => by rw [hσ]
    Γ := Γ
    mem_Γ := hΓm
    arith := hΓa
    pt := fun k t => xF k t ≫ Y.j
    hol := fun k => PullbackSections.isHolTo_comp (hxhol k) Y.j
    comp_s_eq_spMap_of_isOver := fun k t _ => j_over Y κ _ (hx₂ k t)
    interior := fun k t _ => j_interior Y _
    disj := fun k k' t _ t' _ h => Subtype.ext (FU.disj _ _ _ _ (hPt k t) (hPt k' t') ((hpt k k' t t').1 h))
    fibre := fun k t ht t' ht' => ?_
    onto := fun p hp hps => ?_
    lat := fun k t ht => ?_
    vec := fun S Ω _ K _ J _ y 𝔐 k V z hVo hVs hz hzf t₀ ht₀ => ?_
    locc := fun m T y hT hTc hy hyi hys b hb b' hb' k k' t ht t' ht' e e' => ?_ }⟩
  · rw [hpt, FU.fibre _ _ _ (hPt k t) (hPt k t')]
    obtain ⟨e, he⟩ := hPe k t ht
    obtain ⟨e', he'⟩ := hPe k t' ht'
    constructor
    · rintro ⟨γ, h, a₁, a₂, a₃, a₄⟩
      refine ⟨γ, (hΓm k γ).2 ⟨a₁, a₂, a₃⟩, (e.trans h).trans e'.symm, fun x => ?_⟩
      have := a₄ x
      rw [he', he] at this
      simp [← this]
    · rintro ⟨γ, hγ, h, hh⟩
      obtain ⟨a₁, a₂, a₃⟩ := (hΓm k γ).1 hγ
      refine ⟨γ, (e.symm.trans h).trans e', a₁, a₂, a₃, fun x => ?_⟩
      rw [he', he, hh]
      simp
  · obtain ⟨x, hx, hxs⟩ := exists_j Y κ p hp hps
    obtain ⟨i, P, hP, hui⟩ := FU.onto (x ≫ pullback.fst _ _) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hxs, spMap_comp])
    obtain ⟨R, h₁, h₂, h₃⟩ := hriem i P hP
    let k : ι := ⟨i, P, hP⟩
    obtain ⟨t, ⟨ht, e, he⟩, -⟩ := (F k).univ R (h₂.trans (hform k).symm) (by rw [hσ]; exact h₃)
    rw [hq] at ht
    refine ⟨k, t, ht, ?_⟩
    rw [← hx]
    congr 1
    apply pullback.hom_ext
    · rw [hx₁, ← hui]
      exact hu k t ht P hP e fun a => by rw [← h₁]; exact he a
    · rw [hx₂, hxs]
  · obtain ⟨V', P, h, -, hm, -, hP, -, hh⟩ := hloc k t ht
    have h₁ : FibreLat Xo.univ.t (FU.u k.1 (P t)) ((F k).R t) :=
      GlobalTheory.T.family_period_riemann_lattice E H D l Xo _ g ty FU k.1 ((F k).R t) (P t) (h t) (hP.1 t hm) (hRf k t) (hh t hm).1 (hh t hm).2 Empty _ _
        fun a => a.elim
    rw [← hum k t ht _ (hP.1 t hm) _ (hh t hm).1 (hh t hm).2, ← hx₁] at h₁
    have h₂ := ((GlobalTheory.T.fibre_lattice_base_change_conj E H _ _ Xo.univ.t Y.oF.t _ g _ ((F k).R t) ((F k).R t) (xF k t)).1 ⟨Y.m0.toSABMap⟩).2 h₁
    exact ((GlobalTheory.T.fibre_lattice_base_change_conj E H _ _ Y.t Y.oF.t _ g _ ((F k).R t) ((F k).R t) (xF k t)).1 ⟨Y.m⟩).1 h₂
  · obtain ⟨V', P, h, hVo', hm, hsub, hP, hd, hh⟩ := hloc k t₀ (hVs ht₀)
    have hW : IsOpen (V ∩ V') := hVo.inter hVo'
    refine hV E H D l Xo c Y S Ω K J y 𝔐 κ _ g ty FU k.1 n (V ∩ V') z (xF k) (F k).R P h hW
      (hmono hz hW Set.inter_subset_left) (hmono (hxhol k) hW fun t ht => hsub ht.2)
      ⟨fun t ht => hP.1 t ht.2, fun x => (hP.2 x).mono Set.inter_subset_right⟩
      (fun a b => (hd a b).mono Set.inter_subset_right) (fun t ht => ?_) t₀ ⟨ht₀, hm⟩
    exact ⟨hRf k t, (hh t ht.2).1, (hh t ht.2).2, (hzf t ht.1).symm,
      (hx₁ k t).trans (hum k t (hsub ht.2) _ (hP.1 t ht.2) _ (hh t ht.2).1 (hh t ht.2).2), hx₂ k t⟩
  · have hx : ∀ a, ∃ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.snd _ _ = spMap κ ∧ (a ∈ T → x ≫ Y.j = y a) := fun a => by
      by_cases ha : a ∈ T
      · obtain ⟨x, h₁, h₂⟩ := exists_j Y κ _ (hyi a ha) (hys a ha)
        exact ⟨x, h₂, fun _ => h₁⟩
      · exact ⟨xF k t, hx₂ k t, fun h => absurd h ha⟩
    choose x hxs hxj using hx
    have hol := isHolTo_of_j Y κ hT hxs (GlobalTheory.HolPeriods.isHolTo_congr hy hxj)
    obtain ⟨i, hi⟩ := Flat.exists_index_of_isPreconnected E H D l Xo _ g ty FU m T (fun a => x a ≫ pullback.fst _ _) hT hTc
      ⟨b, hb⟩ (fun a _ => by rw [Category.assoc, pullback.condition, ← Category.assoc, hxs, spMap_comp])
      (PullbackSections.isHolTo_comp hol _)
    have key : ∀ a ∈ T, ∀ (k : ι) (t : Fin n → ℂ), y a = xF k t ≫ Y.j → k.1 = i := fun a ha k t e => by
      obtain ⟨B', P, -, haB, -, hP, hu'⟩ := hi a ha
      refine FU.disj _ _ _ _ (hPt k t) (hP.1 a haB) ?_
      rw [hu' a haB, ← hx₁, j_inj Y ((hxs a).trans (hx₂ k t).symm) ((hxj a ha).trans e)]
    exact Subtype.ext ((key b hb k t e).trans (key b' hb' k' t' e').symm)

end SheetDecomposition
end
end

section
noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem spMap_injective {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem baseUnif_of_kUnif (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (sm : CMType H → CMType H ⊕ CMType H) (j j' n g : ℕ)
    (q : CMType H × Fin j × Fin j' ≃ Fin n) (U : ∀ κ, KUnif Y sm j j' n g q κ) :
    ∃ B : BaseUnif Y sm j j' n, B.Locc := by
  classical
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  haveI : ∀ κ, Finite (U κ).ι := fun κ => (U κ).fin
  let C : Type := Σ κ : c.F →+* ℂ, (U κ).ι
  obtain ⟨np, ⟨e⟩⟩ := Finite.exists_equiv_fin C
  let a : Fin np → C := e.symm
  have hκ : ∀ κ κ' : c.F →+* ℂ, κ.comp (algebraMap (𝓞 c.F) c.F) = κ'.comp (algebraMap (𝓞 c.F) c.F) → κ = κ' :=
    fun κ κ' h => IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) h
  have hq : ∀ b : C, ((U b.1).F b.2).q = q := fun b => (U b.1).q_eq b.2
  have hdisj : ∀ b b' : C, ∀ t ∈ ballDom q, ∀ t' ∈ ballDom q, (U b.1).pt b.2 t = (U b'.1).pt b'.2 t' → b = b' := by
    rintro ⟨κ, k⟩ ⟨κ', k'⟩ t ht t' ht' h
    have h₁ := (U κ).comp_s_eq_spMap_of_isOver k t ht
    have h₂ := (U κ').comp_s_eq_spMap_of_isOver k' t' ht'
    dsimp only at h
    rw [h, h₂] at h₁
    obtain rfl := hκ _ _ (spMap_injective h₁)
    rw [(U κ').disj k k' t ht t' ht' h]
  have hemb : ∀ p : Sp ℂ ⟶ Y.X, ∃ κ : c.F →+* ℂ, p ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F)) := fun p => by
    obtain ⟨κ, hκρ⟩ := FamEx.exists_ringHom_extend (Spec.preimage (p ≫ Y.s)).hom
    refine ⟨κ, ?_⟩
    rw [hκρ]
    unfold spMap
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  refine ⟨{
    np := np
    g := g
    Di := fun k => (U (a k).1).Di (a k).2
    sig := fun k => (U _).sig _
    κ := fun k => (a k).1
    F := fun k => (U (a k).1).F (a k).2
    q_eq := fun k k' => (hq _).trans (hq _).symm
    form_eq := fun k => (U _).form_eq _
    σ_eq := fun k => (U _).σ_eq _
    Γ := fun k => (U (a k).1).Γ (a k).2
    mem_Γ := fun k => (U _).mem_Γ _
    arith := fun k => (U _).arith _
    pt := fun k => (U (a k).1).pt (a k).2
    hol := fun k => by rw [hq]; exact (U _).hol _
    comp_s_eq_spMap_of_isOver := fun k => by rw [hq]; exact (U _).comp_s_eq_spMap_of_isOver _
    interior := fun k => by rw [hq]; exact (U _).interior _
    disj := fun k k' => by
      rw [hq, hq]
      exact fun t ht t' ht' h => e.symm.injective (hdisj _ _ t ht t' ht' h)
    fibre := fun k => by rw [hq]; exact (U _).fibre _
    onto := fun p hp => ?_
    lat := fun k => by rw [hq]; exact (U _).lat _
    vec := fun S Ω _ K _ J _ y 𝔐 k V z hV hs => (U _).vec S Ω K J y 𝔐 _ V z hV (by rw [← hq (a k)]; exact hs) }, ?_⟩
  · obtain ⟨κ, hκ⟩ := hemb p
    obtain ⟨k, t, ht, h⟩ := (U κ).onto p hp hκ
    obtain ⟨i, hi⟩ := e.symm.surjective ⟨κ, k⟩
    refine ⟨i, t, by rw [hq]; exact ht, ?_⟩
    show (U (e.symm i).1).pt (e.symm i).2 t = p
    rw [hi]
    exact h
  · intro m T y hT hTc hy hyi b hb b' hb' k k' t ht t' ht' h h'
    choose κ hκy using fun b => hemb (y b)
    have hd : ∀ r : 𝓞 c.F, DifferentiableOn ℂ (fun b => κ b (r : c.F)) T := fun r => by
      have h3 := (PullbackSections.isHolTo_comp hy Y.s ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 c.F))).inv r)).2
      have hset : T ⊆ {b ∈ T | ⊤ ≤ (y b ≫ Y.s) ⁻¹ᵁ ⊤} := fun b hb => ⟨hb, le_top⟩
      refine (h3.mono hset).congr fun b _ => ?_
      show κ b (r : c.F) = valAt' (y b ≫ Y.s) ⊤ _
      rw [hκy b]
      exact (PullbackSections.valAt'_spMap ((κ b).comp (algebraMap (𝓞 c.F) c.F)) r).symm
    have hc : ∀ b₁ ∈ T, y b₁ ≫ Y.s = spMap ((κ b).comp (algebraMap (𝓞 c.F) c.F)) := fun b₁ hb₁ => by
      rw [hκy, FamEx.embedding_const_preconnected hTc κ hd hb₁ hb]
    have key : ∀ d d' : C, y b = (U d.1).pt d.2 t → y b' = (U d'.1).pt d'.2 t' → t ∈ ballDom q → t' ∈ ballDom q → d = d' := by
      rintro ⟨κ₁, k₁⟩ ⟨κ₂, k₂⟩ h₁ h₂ ht ht'
      dsimp only at h₁ h₂
      have e₁ := (U κ₁).comp_s_eq_spMap_of_isOver k₁ t ht
      have e₂ := (U κ₂).comp_s_eq_spMap_of_isOver k₂ t' ht'
      rw [← h₁, hc b hb] at e₁
      rw [← h₂, hc b' hb'] at e₂
      obtain rfl := hκ _ _ (spMap_injective e₁)
      obtain rfl := hκ _ _ (spMap_injective e₂)
      rw [(U (κ b)).locc m T y hT hTc hy hyi hc b hb b' hb' k₁ k₂ t ht t' ht' h₁ h₂]
    exact e.symm.injective (key (a k) (a k') h h' (by rw [← hq (a k)]; exact ht) (by rw [← hq (a k')]; exact ht'))

theorem baseUnifEx2_of (hV : VecOfPeriods) (hC : KUnifConj) : BaseUnifEx2 := by
  intro hG E _ _ _ H D l Xo c Y sm j j' n h1 hs hn
  have hN : N1c := hG.1.2.2.1
  obtain ⟨g, ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  have q : CMType H × Fin j × Fin j' ≃ Fin n := Fintype.equivFinOfCardEq (by simp [hn, mul_assoc])
  let ρ : c.F := (IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ
  have hρ : (ρ : ℂ) = H.rt0 := rfl
  have good : ∀ κ : c.F →+* ℂ, κ ρ = H.rt0 → Nonempty (KUnif Y sm j j' n g q κ) := fun κ hκ => by
    obtain ⟨FU⟩ := hN E H D l Xo (κ.comp (IntermediateField.inclusion c.le).toRingHom) g ty h1 hκ hty
    exact kUnif_good hV Y sm j j' n g q κ ty hty hs ρ hρ hκ FU
  have all : ∀ κ : c.F →+* ℂ, Nonempty (KUnif Y sm j j' n g q κ) := fun κ => by
    have e : ρ ^ 2 = -(H.d : c.F) := Subtype.ext (by show (ρ : ℂ) ^ 2 = -(H.d : ℂ); exact H.sqrt_neg_disc_sq)
    have e2 : (κ ρ) ^ 2 = H.rt0 ^ 2 := by
      rw [← map_pow, e, H.sqrt_neg_disc_sq]
      simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 e2 with h | h
    · exact good κ h
    · have h' := hC E H D l Xo c Y sm j j' n g q _ (good ((starRingEnd ℂ).comp κ) (by
        show starRingEnd ℂ (κ ρ) = _
        rw [h, map_neg, FamEx.rt0_conj_neg_ne_zero, neg_neg]))
      have e3 : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp κ) = κ := RingHom.ext fun x => by simp
      rwa [e3] at h'
  exact baseUnif_of_kUnif Y sm j j' n g q fun κ => (all κ).some

end SheetDecomposition
end
end

section
noncomputable section

namespace SheetDecomposition.Cj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped CategoryTheory.Obj ComplexOrder

section Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (φ : R →+* R') (ψ : R' →+* R'') :
    dualMap (ψ.comp φ) = (dualMap ψ).comp (dualMap φ) :=
  RingHom.ext fun a => TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

theorem dualMap_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (a : R) :
    dualMap φ (algebraMap R (DualNumber R) a) = algebraMap R' (DualNumber R') (φ a) := by
  change dualMap φ (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl (φ a)
  exact TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

theorem centre_conj (z : Spec (CommRingCat.of ℂ) ⟶ X) : centre (spMap (starRingEnd ℂ) ≫ z) = centre z := by
  have h : (spMap (starRingEnd ℂ)) (IsLocalRing.closedPoint ℂ) = IsLocalRing.closedPoint ℂ :=
    Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact congrArg (fun p => z p) h

theorem cj_cj (z : Sp ℂ ⟶ X) : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) ≫ z = z := by
  rw [← Category.assoc, GlobalTheory.ArchMetricCompare.cj_cj, Category.id_comp]

theorem extends_conj (M : LieModel G ξ E) {x x' : X} (hx : x = x') (h : genPt ξ ⤳ x) (h' : genPt ξ ⤳ x') (e : E)
    (v : epsAt (X.fromSpecStalk x) ⟶ G) (hv : M.Extends ⟨x, h⟩ e v)
    (φ : X.presheaf.stalk x ⟶ CommRingCat.of ℂ) (φ' : X.presheaf.stalk x' ⟶ CommRingCat.of ℂ)
    (H : Spec.map φ' ≫ X.fromSpecStalk x' = spMap (starRingEnd ℂ) ≫ Spec.map φ ≫ X.fromSpecStalk x) :
    ∃ v' : epsAt (X.fromSpecStalk x') ⟶ G, M.Extends ⟨x', h'⟩ e v' ∧
      Spec.map (CommRingCat.ofHom (dualMap φ'.hom)) ≫ v'.left =
        spMap (dualMap (starRingEnd ℂ)) ≫ Spec.map (CommRingCat.ofHom (dualMap φ.hom)) ≫ v.left := by
  subst hx
  refine ⟨v, hv, ?_⟩
  have h1 : Spec.map φ' = Spec.map (φ ≫ CommRingCat.ofHom (starRingEnd ℂ)) := by
    rw [← cancel_mono (X.fromSpecStalk x), H, Spec.map_comp, Category.assoc]
  have h2 : φ' = φ ≫ CommRingCat.ofHom (starRingEnd ℂ) := Spec.map_injective h1
  subst h2
  have h3 : dualMap (φ ≫ CommRingCat.ofHom (starRingEnd ℂ)).hom =
      (dualMap (starRingEnd ℂ)).comp (dualMap φ.hom) := dualMap_comp _ _
  rw [h3, CommRingCat.ofHom_comp, Spec.map_comp]
  exact Category.assoc _ _ _

theorem eps_sq : spMap (dualMap (starRingEnd ℂ)) ≫ spMap (algebraMap ℂ (DualNumber ℂ)) =
    spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (starRingEnd ℂ) := by
  have h2 : CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) ≫ CommRingCat.ofHom (dualMap (starRingEnd ℂ)) =
      CommRingCat.ofHom (starRingEnd ℂ) ≫ CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) :=
    CommRingCat.hom_ext (RingHom.ext fun a => dualMap_algebraMap (starRingEnd ℂ) a)
  have h3 := congrArg Spec.map h2
  simpa only [Spec.map_comp] using h3

def cjVec (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : epsAt z ⟶ G) : epsAt (spMap (starRingEnd ℂ) ≫ z) ⟶ G :=
  Over.homMk (spMap (dualMap (starRingEnd ℂ)) ≫ w.left) (by
    have h1 : w.left ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))) ≫ z := Over.w w
    simp only [Over.mk_hom, Category.assoc, h1]
    rw [← Category.assoc, eps_sq, Category.assoc])

theorem valAt_conj (M : LieModel G ξ E) (z : Spec (CommRingCat.of ℂ) ⟶ X) (e : E) (w : epsAt z ⟶ G)
    (hw : M.ValAt z e w) : M.ValAt (spMap (starRingEnd ℂ) ≫ z) e (cjVec z w) := by
  obtain ⟨h, v, hv, hl⟩ := hw
  have hc := centre_conj z
  have h' : genPt ξ ⤳ centre (spMap (starRingEnd ℂ) ≫ z) := hc ▸ h
  obtain ⟨v', hv', hl'⟩ := extends_conj M hc.symm h h' e v hv (Scheme.stalkClosedPointTo z)
    (Scheme.stalkClosedPointTo (spMap (starRingEnd ℂ) ≫ z)) (by
      refine (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (spMap (starRingEnd ℂ) ≫ z)).trans ?_
      exact congrArg (spMap (starRingEnd ℂ) ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z).symm)
  refine ⟨h', v', hv', ?_⟩
  have : (cjVec z w).left = spMap (dualMap (starRingEnd ℂ)) ≫ w.left := rfl
  rw [this, hl]
  exact hl'.symm

theorem isTangent_of_fibre {A : Over (Sp ℂ)} [GrpObj A] {z : Sp ℂ ⟶ X} {φ : A.left ⟶ G.left} (h : IsGrpPullback A G z φ)
    {v : epsAt z ⟶ G} (hv : IsTanAt G z v) {v' : epsR ℂ ⟶ A} (e : v'.left ≫ φ = v.left) : IsTangent v' := by
  refine h.1.hom_ext ?_ ?_
  · rw [Category.assoc, e]
    refine Eq.trans ?_ (GlobalTheory.PolBaseChange.eSec_comm h).symm
    refine Eq.trans hv ?_
    show (toUnit _ ≫ η[G]).left = _
    simp [eSec]
  · have z := congrArg (· ≫ A.hom) (GlobalTheory.ArchMetricCompare.isTangent_zero A)
    rw [← z, Category.assoc, Category.assoc, Over.w, Over.w]

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  [Module (𝓞 E) Λ]

theorem fibreLatVec_conj {X : Scheme.{0}} (t : SAB H X) (z : Sp ℂ ⟶ X) (R R' : RiemLat E g Λ) {A₀ : Type}
    (x : A₀ → Fin g → ℂ) (v : A₀ → (epsAt z ⟶ t.G)) (hP : ∀ x, R'.P x = star (R.P x))
    (hH : R'.Hm = R.Hm.map (starRingEnd ℂ)) (hB : ∀ a x, R'.B a x = star (R.B a (star x)))
    (htan : ∀ a, IsTanAt t.G z (v a)) (hF : FibreLatVec t z R x v) :
    FibreLatVec t (spMap (starRingEnd ℂ) ≫ z) R' (fun a => star (x a)) (fun a => cjVec z (v a)) := by
  obtain ⟨A, _, φ, u, χ, hpb, hAH, hact, hinj, hmem, hvec⟩ := hF
  have h := isGrpPullback_pullback A (spMap (starRingEnd ℂ))
  refine ⟨(Over.pullback (spMap (starRingEnd ℂ))).obj A, inferInstance, pullback.fst _ _ ≫ φ,
    GlobalTheory.ArchMetricCompare.cjUnif h u, fun l => star (χ ⟨star l.1, l.2⟩), h.comp hpb, ?_, fun a p => ?_, ?_,
    fun p => ?_, fun i => ?_⟩
  · rw [hH]
    exact GlobalTheory.ArchMetricCompare.cj_isAH h u hAH
  · show (GlobalTheory.ArchMetricCompare.cjPt h (u.ex (star (R'.B a p)))).left ≫ pullback.fst _ _ ≫ φ =
      (GlobalTheory.ArchMetricCompare.cjPt h (u.ex (star p))).left ≫ (pullback.fst _ _ ≫ φ) ≫ (t.act.act a).left
    rw [hB a p, star_star, GlobalTheory.ArchMetricCompare.cjPt_comp' h, Category.assoc, ← Category.assoc _ φ,
      ← Category.assoc _ (pullback.fst _ _ ≫ φ), GlobalTheory.ArchMetricCompare.cjPt_comp', hact a (star p)]
    simp only [Category.assoc]
  · intro x y e
    rw [hP, hP] at e
    exact hinj (star_injective e)
  · show star p ∈ u.Λ ↔ _
    rw [hmem]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, by rw [hP, hx, star_star]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, by rw [hP, star_star]⟩
  · obtain ⟨v', e, hd⟩ := hvec i
    have sq : (spMap (dualMap (starRingEnd ℂ)) ≫ v'.left) ≫ A.hom = (epsR ℂ).hom ≫ spMap (starRingEnd ℂ) := by
      rw [Category.assoc, Over.w]
      exact eps_sq
    let t'' : epsR ℂ ⟶ (Over.pullback (spMap (starRingEnd ℂ))).obj A :=
      Over.homMk (h.1.lift _ _ sq) (h.1.lift_snd _ _ _)
    have e' : t''.left ≫ pullback.fst _ _ = spMap (dualMap (starRingEnd ℂ)) ≫ v'.left := h.1.lift_fst _ _ _
    refine ⟨t'', ?_, GlobalTheory.ArchMetricCompare.cj_isDiff h u (isTangent_of_fibre hpb (htan i) e) e' hd⟩
    rw [← Category.assoc, e', Category.assoc, e]
    rfl

theorem eqvBy_conj {R₁ R₂ R₁' R₂' : RiemLat E g Λ} (h₁ : ∀ x, R₁'.P x = star (R₁.P x))
    (h₂ : ∀ x, R₂'.P x = star (R₂.P x)) {gm : Λ ≃ₗ[𝓞 E] Λ} (h : R₁.EqvBy R₂ gm) : R₁'.EqvBy R₂' gm := by
  obtain ⟨k, hk⟩ := h
  refine ⟨{ toFun := fun x => star (k (star x))
            invFun := fun x => star (k.symm (star x))
            map_add' := fun x y => by simp
            map_smul' := fun a x => by simp
            left_inv := fun x => by simp
            right_inv := fun x => by simp }, fun x => ?_⟩
  show R₂'.P (gm x) = star (k (star (R₁'.P x)))
  rw [h₁, h₂, hk, star_star]

theorem autGrp_neg (f : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) : autGrp (E := E) (-f) = autGrp f := by
  ext gm
  show (∀ x y, (-f) (gm x) (gm y) = (-f) x y) ↔ ∀ x y, f (gm x) (gm y) = f x y
  simp

theorem star_mem_ballDom {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} {q : Ψ × Fin j × Fin j' ≃ Fin n} {t : Fin n → ℂ}
    (ht : t ∈ ballDom q) : star t ∈ ballDom q := by
  intro τ
  have e : 1 - (ballMat q (star t) τ)ᴴ * ballMat q (star t) τ = (1 - (ballMat q t τ)ᴴ * ballMat q t τ)ᵀ := by
    ext a b
    simp [ballMat, Matrix.mul_apply, Matrix.one_apply, eq_comm, _root_.mul_comm]
  rw [e]
  exact (ht τ).transpose

theorem preimage_star_ballDom {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) :
    star ⁻¹' ballDom q = ballDom q := by
  ext t
  constructor
  · intro h
    have h' := star_mem_ballDom (q := q) (t := star t) h
    rwa [star_star] at h'
  · intro h
    exact star_mem_ballDom (q := q) (t := t) h

theorem analyticAt_star_star {n : ℕ} {f : (Fin n → ℂ) → Fin g → ℂ} {t₀ : Fin n → ℂ} (h : AnalyticAt ℂ f (star t₀)) :
    AnalyticAt ℂ (fun t => star (f (star t))) t₀ := by
  have h1 : ∀ᶠ t in 𝓝 t₀, AnalyticAt ℂ f (star t) :=
    (continuous_star.continuousAt (x := t₀)).tendsto.eventually h.eventually_analyticAt
  refine GlobalTheory.SCV.analyticAt_of_differentiableOn (s := {t | AnalyticAt ℂ f (star t)}) (fun t ht => ?_) h1
  have := (show AnalyticAt ℂ f (star t) from ht).differentiableAt.star_star
  rw [star_star] at this
  exact this.differentiableWithinAt

end SheetDecomposition.Cj
end
end

section
noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem vecAt_conj {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K]
    {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) {n g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    (R R' : (Fin n → ℂ) → RiemLat E g Λ) (z : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)) (t₀ : Fin n → ℂ)
    (hR : ∀ t, (∀ x, (R' t).P x = star ((R (star t)).P x)) ∧ (R' t).Hm = (R (star t)).Hm.map (starRingEnd ℂ) ∧
      ∀ a x, (R' t).B a x = star ((R (star t)).B a (star x)))
    (h : VecAt 𝔐 R (fun t => spMap (starRingEnd ℂ) ≫ z (star t)) (star t₀)) : VecAt 𝔐 R' z t₀ := by
  intro m s hs
  obtain ⟨x, hx, hev⟩ := h m s fun a => by
    obtain ⟨v, hv⟩ := hs a
    show ∃ v, 𝔐.M.ValAt (spMap (starRingEnd ℂ) ≫ z (star (star t₀))) (s a) v
    rw [star_star]
    exact ⟨_, Cj.valAt_conj 𝔐.M _ _ v hv⟩
  refine ⟨fun a t => star (x a (star t)), fun a => Cj.analyticAt_star_star (hx a), ?_⟩
  filter_upwards [(continuous_star.continuousAt (x := t₀)).tendsto.eventually hev] with t ht
  obtain ⟨v, hv, hF⟩ := ht
  have key : ∀ (w w' : Sp ℂ ⟶ 𝔐.X) (v : Fin m → (epsAt w ⟶ 𝔐.t.G)), w' = spMap (starRingEnd ℂ) ≫ w →
      (∀ a, 𝔐.M.ValAt w (s a) (v a)) → FibreLatVec 𝔐.t w (R (star t)) (fun a => x a (star t)) v →
      ∃ v' : Fin m → (epsAt w' ⟶ 𝔐.t.G), (∀ a, 𝔐.M.ValAt w' (s a) (v' a)) ∧
        FibreLatVec 𝔐.t w' (R' t) (fun a => star (x a (star t))) v' := by
    rintro w _ v rfl hv hF
    exact ⟨fun a => Cj.cjVec w (v a), fun a => Cj.valAt_conj 𝔐.M w _ _ (hv a),
      Cj.fibreLatVec_conj 𝔐.t w _ _ _ v (hR t).1 (hR t).2.1 (hR t).2.2 (fun a => (hv a).isTanAt) hF⟩
  exact key _ _ v (by rw [Cj.cj_cj, star_star]) hv hF

theorem kUnifConj : KUnifConj := by
  rintro E _ _ _ H D l Xo c Y sm j j' n g q κ ⟨U⟩
  choose F' hq hσ hform hR using fun k => GlobalTheory.T.conjugate_universal_family E (CMType H) j j' n g (U.Di k).La (U.F k)
  have hcanc : ∀ {X : Scheme.{0}} {a b : Sp ℂ ⟶ X}, spMap (starRingEnd ℂ) ≫ a = spMap (starRingEnd ℂ) ≫ b → a = b :=
    fun {X a b} e => by rw [← Cj.cj_cj a, e, Cj.cj_cj]
  have hs : spMap (((starRingEnd ℂ).comp κ).comp (algebraMap (𝓞 c.F) c.F)) =
      spMap (starRingEnd ℂ) ≫ spMap (κ.comp (algebraMap (𝓞 c.F) c.F)) :=
    Spec.map_comp (CommRingCat.ofHom (κ.comp (algebraMap (𝓞 c.F) c.F))) (CommRingCat.ofHom (starRingEnd ℂ))
  refine ⟨{
    ι := U.ι
    fin := U.fin
    Di := U.Di
    sig := U.sig
    F := F'
    q_eq := fun k => (hq k).trans (U.q_eq k)
    form_eq := fun k => ?_
    σ_eq := fun k τ => ?_
    Γ := U.Γ
    mem_Γ := U.mem_Γ
    arith := fun k => ?_
    pt := fun k t => spMap (starRingEnd ℂ) ≫ U.pt k (star t)
    hol := fun k => ?_
    comp_s_eq_spMap_of_isOver := fun k t ht => ?_
    interior := fun k t ht => ?_
    disj := fun k k' t ht t' ht' e =>
      U.disj k k' _ (Cj.star_mem_ballDom ht) _ (Cj.star_mem_ballDom ht') (hcanc e)
    fibre := fun k t ht t' ht' => ?_
    onto := fun p hp hps => ?_
    lat := fun k t ht => ?_
    vec := fun S Ω _ K _ J _ y 𝔐 k V z hV hVs hz hzf t₀ ht₀ => ?_
    locc := fun m T y hT hTc hy hyi hys b hb b' hb' k k' t ht t' ht' e e' => ?_ }⟩
  · rw [hform]
    rcases U.form_eq k with h | h <;> rw [h]
    · exact Or.inr rfl
    · exact Or.inl (neg_neg _)
  · rw [hσ, U.σ_eq]
    rfl
  · have h := U.arith k
    unfold UnivFam.IsArith at h ⊢
    rwa [hform, Cj.autGrp_neg]
  · have h := GlobalTheory.T.holomorphic_family_conjugate _ _ _ _ (U.hol k)
    rwa [Cj.preimage_star_ballDom] at h
  · rw [Category.assoc, U.comp_s_eq_spMap_of_isOver k _ (Cj.star_mem_ballDom ht), hs]
  · rw [Cj.centre_conj]
    exact U.interior k _ (Cj.star_mem_ballDom ht)
  · have h := U.fibre k _ (Cj.star_mem_ballDom ht) _ (Cj.star_mem_ballDom ht')
    constructor
    · intro e
      obtain ⟨γ, hγ, he⟩ := h.1 (hcanc e)
      exact ⟨γ, hγ, Cj.eqvBy_conj (hR k t).1 (hR k t').1 he⟩
    · rintro ⟨γ, hγ, he⟩
      have e := h.2 ⟨γ, hγ, Cj.eqvBy_conj (fun x => by rw [(hR k t).1, star_star])
        (fun x => by rw [(hR k t').1, star_star]) he⟩
      show spMap (starRingEnd ℂ) ≫ U.pt k (star t) = spMap (starRingEnd ℂ) ≫ U.pt k (star t')
      rw [e]
  · obtain ⟨k, t, ht, e⟩ := U.onto (spMap (starRingEnd ℂ) ≫ p) (by rwa [Cj.centre_conj])
      (by rw [Category.assoc, hps, hs, Cj.cj_cj])
    refine ⟨k, star t, Cj.star_mem_ballDom ht, ?_⟩
    show spMap (starRingEnd ℂ) ≫ U.pt k (star (star t)) = p
    rw [star_star, e, Cj.cj_cj]
  · have h := Cj.fibreLatVec_conj Y.t _ _ ((F' k).R t) _ _ (hR k t).1 (hR k t).2.1 (hR k t).2.2 (fun a => a.elim)
      (U.lat k _ (Cj.star_mem_ballDom ht))
    obtain ⟨A, i, φ, u, χ, h1, h2, h3, h4, h5, -⟩ := h
    exact ⟨A, i, φ, u, χ, h1, h2, h3, h4, h5, fun a => a.elim⟩
  · refine vecAt_conj 𝔐 (U.F k).R (F' k).R z t₀ (hR k) ?_
    refine U.vec S Ω K J y 𝔐 k (star ⁻¹' V) _ (hV.preimage continuous_star) (fun t ht => ?_)
      (GlobalTheory.T.holomorphic_family_conjugate _ _ _ _ hz) (fun t ht => ?_) _ (by simpa using ht₀)
    · simpa using Cj.star_mem_ballDom (hVs ht)
    · rw [Category.assoc, hzf _ ht, Cj.cj_cj, star_star]
  · have hpre : IsPreconnected (star ⁻¹' T : Set (Fin m → ℂ)) := by
      have e₀ : (star ⁻¹' T : Set (Fin m → ℂ)) = star '' T := by
        ext x
        constructor
        · intro h
          exact ⟨star x, h, star_star x⟩
        · rintro ⟨a, ha, rfl⟩
          show star (star a) ∈ T
          rwa [star_star]
      rw [e₀]
      exact hTc.image _ continuous_star.continuousOn
    refine U.locc m (star ⁻¹' T) _ (hT.preimage continuous_star) hpre (GlobalTheory.T.holomorphic_family_conjugate _ _ _ _ hy) (fun a ha => ?_)
      (fun a ha => ?_) (star b) (by simpa using hb) (star b') (by simpa using hb') k k' _ (Cj.star_mem_ballDom ht) _
      (Cj.star_mem_ballDom ht') ?_ ?_
    · rw [Cj.centre_conj]
      exact hyi _ ha
    · rw [Category.assoc, hys _ ha, hs, Cj.cj_cj]
    · show spMap (starRingEnd ℂ) ≫ y (star (star b)) = _
      rw [star_star, e, Cj.cj_cj]
    · show spMap (starRingEnd ℂ) ≫ y (star (star b')) = _
      rw [star_star, e', Cj.cj_cj]

end SheetDecomposition
end
end

section
noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.TangentOrigin

theorem spMap_fst_comp {R : Type} [CommRing R] (φ : R →+* DualNumber ℂ) :
    spMap fstC ≫ spMap φ = spMap (fstC.comp φ) := (Spec.map_comp _ _).symm

theorem evalPt_top {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (r : Γ(Sp R, ⊤)) :
    evalPt (spMap φ) ⊤ le_rfl r = φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) := by
  rw [← evalPt_spMap φ]
  congr 1
  simp

theorem mem_basicOpen_iff {R : Type} [CommRing R] (φ : R →+* DualNumber ℂ) (r : Γ(Sp R, ⊤)) :
    ⊤ ≤ spMap φ ⁻¹ᵁ (Sp R).basicOpen r ↔ (φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r)).fst ≠ 0 := by
  rw [top_le_preimage_iff, spMap_fst_comp, GlobalTheory.top_le_preimage_basicOpen_iff _ ⊤ r,
    valAt'_eq_evalPt _ _ le_rfl, evalPt_top]
  rfl

theorem exists_frac {Z : Scheme.{0}} {R : Type} [CommRing R] (v : Sp R ⟶ Z) (U : Z.Opens) (f : Γ(Z, U))
    (φ₀ : R →+* DualNumber ℂ) (h₀ : ⊤ ≤ (spMap φ₀ ≫ v) ⁻¹ᵁ U) :
    ∃ (a r : R) (k : ℕ), (φ₀ r).fst ≠ 0 ∧ ∀ φ : R →+* DualNumber ℂ, (φ r).fst ≠ 0 →
      ∃ h : ⊤ ≤ (spMap φ ≫ v) ⁻¹ᵁ U, evalPt (spMap φ ≫ v) U h f * φ r ^ k = φ a := by
  let p₀ : Sp R := (spMap fstC ≫ spMap φ₀) (default : PrimeSpectrum ℂ)
  have hmem : p₀ ∈ v ⁻¹ᵁ U := by
    have h1 : ⊤ ≤ spMap φ₀ ⁻¹ᵁ (v ⁻¹ᵁ U) := by rwa [Scheme.Hom.comp_preimage] at h₀
    exact (GlobalTheory.top_le_preimage_iff_mem _ _).1 ((top_le_preimage_iff _ _).1 h1)
  obtain ⟨r, hrU, hr0⟩ := (isAffineOpen_top (Sp R)).exists_basicOpen_le (V := v ⁻¹ᵁ U) ⟨p₀, hmem⟩ trivial
  obtain ⟨⟨hh, s⟩, hk⟩ := IsLocalization.surj (Submonoid.powers r) ((v.appLE U _ hrU).hom f)
  obtain ⟨k, hks⟩ := s.2
  dsimp only at hk hks
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom hh, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r, k, ?_,
    fun φ hφ => ?_⟩
  · rw [← mem_basicOpen_iff, top_le_preimage_iff]
    exact (GlobalTheory.top_le_preimage_iff_mem _ _).2 hr0
  · have hD := (mem_basicOpen_iff φ r).2 hφ
    have hU : ⊤ ≤ (spMap φ ≫ v) ⁻¹ᵁ U := by
      rw [Scheme.Hom.comp_preimage]
      exact hD.trans (Scheme.Hom.preimage_mono _ hrU)
    refine ⟨hU, ?_⟩
    have e := congrArg (evalPt (spMap φ) _ hD) hk
    have e2 : ∀ x : Γ(Sp R, ⊤), evalPt (spMap φ) _ hD (algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen r) x) =
        φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) := fun x =>
      (evalPt_res (spMap φ) le_top le_rfl hD x).trans (evalPt_top φ x)
    rw [map_mul, e2, e2, ← hks, map_pow, map_pow] at e
    rw [← e]
    congr 1

theorem analyticAt_det {n g : ℕ} {M : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ} {t₀ : Fin n → ℂ}
    (h : ∀ a b, AnalyticAt ℂ (fun t => M t a b) t₀) : AnalyticAt ℂ (fun t => (M t).det) t₀ := by
  simp only [Matrix.det_apply']
  exact Finset.analyticAt_fun_sum _ fun σ _ =>
    analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => h _ _)

theorem analyticAt_of_forms {n g : ℕ} (w : (Fin n → ℂ) → Fin g → ℂ) (t₀ : Fin n → ℂ)
    (h : ∀ z : Fin g → ℂ, z ≠ 0 → ∃ (Λ : (Fin n → ℂ) → (Fin g → ℂ) →ₗ[ℂ] ℂ) (r : (Fin n → ℂ) → ℂ),
      (∀ u, AnalyticAt ℂ (fun t => Λ t u) t₀) ∧ AnalyticAt ℂ r t₀ ∧ (∀ᶠ t in 𝓝 t₀, Λ t (w t) = r t) ∧ Λ t₀ z ≠ 0) :
    AnalyticAt ℂ w t₀ := by
  classical
  let S : Set ((Fin g → ℂ) →ₗ[ℂ] ℂ) := {μ | ∃ (Λ : (Fin n → ℂ) → (Fin g → ℂ) →ₗ[ℂ] ℂ) (r : (Fin n → ℂ) → ℂ),
      (∀ u, AnalyticAt ℂ (fun t => Λ t u) t₀) ∧ AnalyticAt ℂ r t₀ ∧ (∀ᶠ t in 𝓝 t₀, Λ t (w t) = r t) ∧ Λ t₀ = μ}
  have hS : Submodule.span ℂ S = ⊤ := Submodule.span_eq_top_of_ne_zero fun z hz => by
    obtain ⟨Λ, r, h1, h2, h3, h4⟩ := h z hz
    exact ⟨Λ t₀, ⟨Λ, r, h1, h2, h3, rfl⟩, h4⟩
  have hall : ∀ μ, μ ∈ S := fun μ => by
    have hμ : μ ∈ Submodule.span ℂ S := hS ▸ Submodule.mem_top
    induction hμ using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨fun _ => 0, fun _ => 0, fun _ => analyticAt_const, analyticAt_const, by simp, rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨Λ, r, h1, h2, h3, rfl⟩ := hx
      obtain ⟨Λ', r', h1', h2', h3', rfl⟩ := hy
      refine ⟨fun t => Λ t + Λ' t, fun t => r t + r' t, fun u => (h1 u).add (h1' u), h2.add h2', ?_, rfl⟩
      filter_upwards [h3, h3'] with t a b
      rw [LinearMap.add_apply, a, b]
    | smul c x _ hx =>
      obtain ⟨Λ, r, h1, h2, h3, rfl⟩ := hx
      refine ⟨fun t => c • Λ t, fun t => c * r t, fun u => analyticAt_const.mul (h1 u), analyticAt_const.mul h2, ?_, rfl⟩
      filter_upwards [h3] with t a
      rw [LinearMap.smul_apply, a, smul_eq_mul]
  choose Λ r h1 h2 h3 h4 using fun k : Fin g => hall (LinearMap.proj k)
  let M : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun t => Matrix.of fun k l => Λ k t (Pi.single l 1)
  have hM : ∀ t x k, (M t *ᵥ x) k = Λ k t x := fun t x k => by
    rw [LinearMap.pi_apply_eq_sum_univ (Λ k t) x]
    show ∑ l, M t k l * x l = _
    refine Finset.sum_congr rfl fun l _ => ?_
    have e : (fun j => if l = j then (1 : ℂ) else 0) = Pi.single l 1 := by
      funext j
      simp [Pi.single_apply, eq_comm]
    rw [e, smul_eq_mul, mul_comm]
    rfl
  have hM0 : M t₀ = 1 := by
    ext k l
    simp [M, h4, Pi.single_apply, Matrix.one_apply]
  have hd : AnalyticAt ℂ (fun t => (M t).det) t₀ := analyticAt_det fun a b => h1 a _
  have hd0 : (M t₀).det ≠ 0 := by rw [hM0]; simp
  refine analyticAt_pi_iff.2 fun k => ?_
  have hc : AnalyticAt ℂ (fun t => ((M t).updateCol k fun i => r i t).det) t₀ := analyticAt_det fun a b => by
    by_cases hb : b = k
    · subst hb
      simpa using h2 a
    · simp only [Matrix.updateCol_ne hb]
      exact h1 a (Pi.single b 1)
  refine (hc.div hd hd0).congr ?_
  filter_upwards [Filter.eventually_all.2 h3, hd.continuousAt.eventually_ne hd0] with t ht hne
  have e1 : (fun i => r i t) = M t *ᵥ w t := funext fun i => by rw [hM, ht]
  have e2 : (M t).cramer (M t *ᵥ w t) = (M t).det • w t := by
    rw [Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  have e3 := congrFun e2 k
  rw [Matrix.cramer_apply] at e3
  show ((M t).updateCol k fun i => r i t).det / (M t).det = w t k
  rw [e1, e3, Pi.smul_apply, smul_eq_mul, mul_div_cancel_left₀ _ hne]

theorem snd_of_mul_eq {x ρ α : DualNumber ℂ} (h : x * ρ = α) (hρ : ρ.fst ≠ 0) :
    x.snd = (α.snd * ρ.fst - α.fst * ρ.snd) / ρ.fst ^ 2 := by
  subst h
  simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op]
  field_simp
  ring

theorem holCoord : HolCoord := by
  intro Z n g B e A _ v ψ w hB hol hψ hder huniq t₀ ht₀
  refine analyticAt_of_forms w t₀ fun z hz => ?_

  obtain ⟨U, h₀, f, hf⟩ : ∃ (U : Z.Opens) (_ : ⊤ ≤ (spMap (dualMap (ψ t₀)) ≫ v) ⁻¹ᵁ U) (f : Γ(Z, U)),
      fderiv ℂ (fun z => valAt' (e t₀ z) U f) 0 z ≠ 0 := by
    by_contra hn
    push Not at hn
    have h' : IsDerivAt0 (e t₀) (w t₀ + z) (spMap (dualMap (ψ t₀)) ≫ v) :=
      ⟨(hder t₀ ht₀).1, fun U h f => by rw [map_add, hn U h f, add_zero]; exact (hder t₀ ht₀).2 U h f⟩
    have := huniq t₀ ht₀ _ _ _ h' (hder t₀ ht₀)
    exact hz (by simpa using this)
  have h00 : ⊤ ≤ e t₀ 0 ⁻¹ᵁ U := (GlobalTheory.FibreDeriv.top_le_preimage_eps _ _ (hder t₀ ht₀).1 U).1 h₀
  let G : (Fin n → ℂ) × (Fin g → ℂ) → ℂ := fun bz => valAt' (e bz.1 bz.2) U f
  have hG : AnalyticAt ℂ G (t₀, 0) :=
    GlobalTheory.SCV.analyticAt_of_differentiableOn (hol U f).2 ((hol U f).1.mem_nhds ⟨⟨ht₀, trivial⟩, h00⟩)
  have hι : AnalyticAt ℂ (fun t : Fin n → ℂ => ((t, 0) : (Fin n → ℂ) × (Fin g → ℂ))) t₀ :=
    analyticAt_id.prod analyticAt_const
  have hslice : ∀ t, DifferentiableAt ℂ G (t, 0) → ∀ u,
      fderiv ℂ (fun z => valAt' (e t z) U f) 0 u = fderiv ℂ G (t, 0) (0, u) := fun t ht u => by
    have h1 : HasFDerivAt (fun z : Fin g → ℂ => ((t, z) : (Fin n → ℂ) × (Fin g → ℂ)))
        (ContinuousLinearMap.inr ℂ _ _) 0 := hasFDerivAt_prodMk_right t 0
    have h2 := ht.hasFDerivAt.comp (0 : Fin g → ℂ) h1
    have h3 := h2.fderiv
    exact congrArg (fun T => T u) h3
  obtain ⟨a, r, k, hr0, hfr⟩ := exists_frac v U f (dualMap (ψ t₀)) h₀
  have hψa : ∀ x, AnalyticAt ℂ (fun t => ψ t x) t₀ := fun x =>
    GlobalTheory.SCV.analyticAt_of_differentiableOn (hψ x) (hB.mem_nhds ht₀)
  have hfst : ∀ t (x : DualNumber A), (dualMap (ψ t) x).fst = ψ t x.fst := fun t x => by simp [dualMap]
  have hsnd : ∀ t (x : DualNumber A), (dualMap (ψ t) x).snd = ψ t x.snd := fun t x => by simp [dualMap]
  have hpow : ∀ t, ψ t r.fst ≠ 0 → ψ t (r ^ k).fst ≠ 0 := fun t ht => by
    rw [TrivSqZeroExt.fst_pow, map_pow]
    exact pow_ne_zero _ ht
  rw [hfst] at hr0
  refine ⟨fun t => (fderiv ℂ G (t, 0)).toLinearMap.comp (LinearMap.inr ℂ _ _),
    fun t => (ψ t a.snd * ψ t (r ^ k).fst - ψ t a.fst * ψ t (r ^ k).snd) / ψ t (r ^ k).fst ^ 2, fun u => ?_, ?_, ?_, ?_⟩
  · have h1 : AnalyticAt ℂ (fun t : Fin n → ℂ => fderiv ℂ G (t, 0)) t₀ := hG.fderiv.comp_of_eq hι rfl
    exact ((ContinuousLinearMap.apply ℂ ℂ ((0, u) : (Fin n → ℂ) × (Fin g → ℂ))).analyticAt _).comp h1
  · exact (((hψa _).mul (hψa _)).sub ((hψa _).mul (hψa _))).div ((hψa _).pow 2) (pow_ne_zero _ (hpow _ hr0))
  · filter_upwards [hB.mem_nhds ht₀, (hψa r.fst).continuousAt.eventually_ne hr0,
      hι.continuousAt.eventually hG.eventually_analyticAt] with t ht hne hGt
    obtain ⟨hU, he⟩ := hfr (dualMap (ψ t)) (by rwa [hfst])
    rw [← map_pow] at he
    have h1 := snd_of_mul_eq he (by rw [hfst]; exact hpow t hne)
    rw [hfst, hfst, hsnd, hsnd] at h1
    rw [← h1]
    exact (hslice t hGt.differentiableAt (w t)).symm.trans ((hder t ht).2 U hU f).symm
  · exact fun h => hf ((hslice t₀ hG.differentiableAt z).trans h)

end SheetDecomposition
end
end

section
namespace SheetDecomposition

theorem baseUnifEx2 : BaseUnifEx2 := baseUnifEx2_of (vecOfPeriods_of holCoord) kUnifConj

theorem baseUnifEx : BaseUnifEx := fun hG E _ _ _ H D l Xo c Y sm j j' n h₁ h₂ h₃ =>
  (baseUnifEx2 hG E H D l Xo c Y sm j j' n h₁ h₂ h₃).elim fun B _ => ⟨B⟩

end SheetDecomposition
end
