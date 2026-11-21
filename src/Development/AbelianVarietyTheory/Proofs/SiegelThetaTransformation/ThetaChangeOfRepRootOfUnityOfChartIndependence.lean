import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MultAddMultConjugate
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.NeBotOfNorm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DetIdealSelfDualLatticeAndInterStandard
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreUnitFrameUniformisation
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CastFrMemDom
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSpanningHypotheses
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsUnitGramFrameBorelChange
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PushforwardPreservesHarmonicPolynomialsAndLattic
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariant
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaVacuumUnitaryColumnChangeUnitFactor
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaHeisenbergUnitaryColumnChange
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FgOfSmulLe
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FramedPointGeneratorIsThetaLevelOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsEvenRepsTensorLatticeAndSum
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaValueComplexPointEqClassicalThetaStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLiftOfProjective
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergVacuumProjectionRootOfUnityPhases
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MultiplierSqMulDetUnitaryColumnChange
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRowHighestHarmonicPolyDerivUnitaryAction
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FirstIffSecondAndResiduals
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detIdeal_selfDual_lattice_and_inter_standard : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Λ : GenLat E n), Λ.Unimod → ∃ J : Ideal (𝓞 E), J ≠ ⊥ ∧ Ideal.absNorm J = (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index ∧ Submodule.span (𝓞 E) (detSet Λ.Ln) = J • Submodule.span (𝓞 E) (detSet Λ.La) ∧ Submodule.span (𝓞 E) (detSet Λ.Ln) = Submodule.map (Algebra.linearMap (𝓞 E) E) (conjI J) ∧ ∀ h : Matrix (Fin n) (Fin n) E, Submodule.span (𝓞 E) (detSet (actLat h Λ).La) = Submodule.map (LinearMap.mulLeft (𝓞 E) h.det) (Submodule.span (𝓞 E) (detSet Λ.La)) := by
  first | exact @GlobalTheory.DetIdeal.detIdeal_selfDual | exact GlobalTheory.DetIdeal.detIdeal_selfDual | (intros; apply GlobalTheory.DetIdeal.detIdeal_selfDual <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

noncomputable section

namespace GlobalTheory.BetaChange

open GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.LatticeBetaCompare GlobalTheory.SW.Nbr
open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem form_adj (h : Matrix (Fin n) (Fin n) E) (v w : Fin n → E) :
    ∑ j, IsCMField.complexConj E (v j) * h.mulVec w j =
      ∑ j, IsCMField.complexConj E ((adjM h).mulVec v j) * w j := by
  simp only [Matrix.mulVec, dotProduct, adjM, Matrix.of_apply, map_sum, map_mul,
    IsCMField.complexConj_apply_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem unimod_act {h : Matrix (Fin n) (Fin n) E} (hu : IsUnitaryM h) {Λ : GenLat E n} (hΛ : Λ.Unimod) :
    (actLat h Λ).Unimod := by
  have h1 : adjM h * h = 1 := hu
  have h2 : h * adjM h = 1 := mul_eq_one_comm.1 h1
  intro v
  have e : v ∈ (actLat h Λ).La ↔ (adjM h).mulVec v ∈ Λ.La := by
    constructor
    · rintro ⟨u, hu, rfl⟩
      change (adjM h).mulVec (h.mulVec u) ∈ _
      rwa [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    · intro hv
      refine ⟨_, hv, ?_⟩
      change h.mulVec _ = _
      rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  rw [e, hΛ]
  constructor
  · rintro hv _ ⟨u, hu, rfl⟩
    exact (form_adj h v u).symm ▸ hv u hu
  · intro hv w hw
    rw [← form_adj]
    exact hv _ ⟨w, hw, rfl⟩

variable {H : Host E} (Dw : Datum H) {l : Geo.Tor.Level H} (c : Coeff l)

theorem reflexNorm_mul_conj (g : 𝓞 E) :
    reflexNorm Dw c ((g * co g : 𝓞 E) : E) = ((Ideal.absNorm (Ideal.span {g}) ^ (Dw.p + Dw.q) : ℕ) : c.F) := by
  have h := (isBe_principal Dw c g).2 c.F.val.toRingHom
  apply c.F.val.toRingHom.injective
  rw [map_natCast]
  have e : c.F.val.toRingHom (reflexNorm Dw c ((g * co g : 𝓞 E) : E)) =
      c.F.val.toRingHom (reflexNorm Dw c (g : E)) * conj (c.F.val.toRingHom (reflexNorm Dw c (g : E))) := by
    simp only [reflexNorm, map_prod, map_pow, ← Finset.prod_mul_distrib, ← mul_pow]
    refine Finset.prod_congr rfl fun σ _ => ?_
    congr 1
    change σ ((g : E) * IsCMField.complexConj E (g : E)) = σ g * conj (σ g)
    rw [map_mul, IsCMField.complexEmbedding_complexConj]
  rw [e, Complex.mul_conj', ← Complex.ofReal_pow, h]
  push_cast
  rfl

theorem isBe_mul_conj (J : Ideal (𝓞 E)) (hJ : J ≠ ⊥) :
    IsBe Dw c (J * conjI J) ((Ideal.absNorm J ^ (Dw.p + Dw.q) : ℕ) : c.F) := by
  let I₀ : (Ideal (𝓞 E))⁰ := ⟨J, mem_nonZeroDivisors_of_ne_zero hJ⟩
  obtain ⟨k, hk, e⟩ := (isOfFinOrder_of_finite (ClassGroup.mk0 I₀)).exists_pow_eq_one
  rw [← map_pow] at e
  obtain ⟨g, hg⟩ : (J ^ k).IsPrincipal := (ClassGroup.mk0_eq_one_iff (I₀ ^ k).2).1 e
  change J ^ k = Ideal.span {g} at hg
  refine isBe_of_pow hk ?_
  have e1 : (J * conjI J) ^ k = Ideal.span {g * co g} := by
    rw [mul_pow, conjI_eq, ← Ideal.map_pow, hg, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_mul_span_singleton]
  have e2 : ((Ideal.absNorm J ^ (Dw.p + Dw.q) : ℕ) : c.F) ^ k = reflexNorm Dw c ((g * co g : 𝓞 E) : E) := by
    rw [reflexNorm_mul_conj, ← hg, map_pow, ← Nat.cast_pow, ← pow_mul, ← pow_mul, mul_comm k]
  rw [e1, e2]
  exact isBe_principal Dw c _

theorem isBe_of_isBeta {Λ : GenLat E n} (hΛ : Λ.Unimod) {b : c.F} (hb : IsBeta Dw c Λ b) {J : Ideal (𝓞 E)}
    (hN : Ideal.absNorm J = (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index)
    (hJ : detSpan Λ.Ln = J • detSpan Λ.La) : IsBe Dw c J b := by
  have hu0 : IsUnit (detSpan Λ.La) :=
    isUnit_detSpan (GenusLatCompare.latEquiv.symm ⟨Λ, GenusLatCompare.isLat_of_unimod Λ hΛ⟩)
  have hu : IsUnit (∏ τ : E →+* ℂ, idealAt c Λ.La τ ^ Dw.mult τ) :=
    IsUnit.prod_iff.2 fun τ _ => by rw [idealAt_eq]; exact (hu0.map _).pow _
  obtain ⟨-, h1, h2⟩ := hb
  refine ⟨?_, fun s => by rw [hN]; exact h2 s⟩
  have e : ∀ τ, idealAt c Λ.Ln τ =
      coeI c.F (J.map (RingOfIntegers.mapRingHom (embF c τ))) * idealAt c Λ.La τ := fun τ => by
    rw [idealAt_eq, idealAt_eq, hJ, smul_eq_coeI_mul, map_mul, extend_coeI]
  rw [← span_eq_coeI_iff, coeI_reflexIdeal]
  rw [BetaIs] at h1
  simp only [e, mul_pow, Finset.prod_mul_distrib] at h1
  exact hu.mul_left_inj.1 h1

omit [IsCMField E] in
theorem map_mulLeft_eq (x : E) (M : Submodule (𝓞 E) E) :
    Submodule.map (LinearMap.mulLeft (𝓞 E) x) M = Submodule.span (𝓞 E) {x} * M := by
  ext y
  rw [Submodule.mem_span_singleton_mul]
  rfl

omit [IsCMField E] in
theorem coeI_span (u : 𝓞 E) : coeI E (Ideal.span {u}) = Submodule.span (𝓞 E) {(u : E)} :=
  IsLocalization.coeSubmodule_span_singleton E u

theorem beta_sq_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l), ∀ (n : ℕ) (Λ : GenLat E n) (h : Matrix (Fin n) (Fin n) E) (b b' : c.F), Λ.Unimod → IsUnitaryM h → IsBeta Dw c Λ b → IsBeta Dw c (actLat h Λ) b' → ∃ m : ℕ, 0 < m ∧ (b ^ 2 * ((((actLat h Λ).Ln.toAddSubgroup.addSubgroupOf (actLat h Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : c.F)) ^ m = (b' ^ 2 * ((((Λ).Ln.toAddSubgroup.addSubgroupOf (Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : c.F) * ∏ τ : E →+* ℂ, embF c τ h.det ^ Dw.mult τ) ^ m := by
  intro E _ _ _ H Dw l c n Λ h b b' hΛ hu hb hb'
  have hΛ' := unimod_act hu hΛ
  obtain ⟨J, hJ0, hN, hJ1, hJ2, hdet⟩ := GlobalTheory.T.detIdeal_selfDual_lattice_and_inter_standard E n Λ hΛ
  obtain ⟨J', hJ0', hN', hJ1', hJ2', -⟩ := GlobalTheory.T.detIdeal_selfDual_lattice_and_inter_standard E n _ hΛ'
  have hB := isBe_of_isBeta Dw c hΛ hb hN hJ1
  have hB' := isBe_of_isBeta Dw c hΛ' hb' hN' hJ1'
  obtain ⟨u, v, hv, huv⟩ := IsFractionRing.div_surjective (A := 𝓞 E) h.det
  have hv0 : v ≠ 0 := nonZeroDivisors.ne_zero hv
  have hvE : (v : E) ≠ 0 := by simpa using hv0
  have huv' : (u : E) = h.det * (v : E) := by
    rw [← huv]; exact (div_mul_cancel₀ _ hvE).symm
  have k1 : coeI E (conjI J) = coeI E J * detSpan Λ.La := by
    rw [← smul_eq_coeI_mul]; exact hJ2.symm.trans hJ1
  have k2 : coeI E (conjI J') = coeI E J' * (Submodule.span (𝓞 E) {h.det} * detSpan Λ.La) := by
    rw [← smul_eq_coeI_mul, ← map_mulLeft_eq]
    exact (hJ2'.symm.trans hJ1').trans (by rw [hdet]; rfl)
  have key : conjI J' * J * Ideal.span {v} = conjI J * J' * Ideal.span {u} := by
    apply IsFractionRing.coeSubmodule_injective (𝓞 E) E
    change coeI E _ = coeI E _
    simp only [map_mul, k1, k2, coeI_span]
    rw [huv', ← Set.singleton_mul_singleton, ← Submodule.span_mul_span]
    ring
  have a1 := isBe_mul (isBe_mul (isBe_pow hB 2) (isBe_mul_conj Dw c J' hJ0')) (isBe_principal Dw c v)
  have a2 := isBe_mul (isBe_mul (isBe_pow hB' 2) (isBe_mul_conj Dw c J hJ0)) (isBe_principal Dw c u)
  have e : J' ^ 2 * (J * conjI J) * Ideal.span {u} = J ^ 2 * (J' * conjI J') * Ideal.span {v} := by
    calc _ = J * J' * (conjI J * J' * Ideal.span {u}) := by ring
      _ = _ := by rw [← key]; ring
  rw [e] at a2
  have hc : conjI J' ≠ ⊥ := fun h0 => hJ0' (by
    rw [← conjI_conjI J', h0, conjI_eq, Ideal.map_bot])
  have hs : Ideal.span {v} ≠ (⊥ : Ideal (𝓞 E)) := by simpa using hv0
  obtain ⟨z, hz, ez⟩ := isBe_unique
    (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hJ0) (mul_ne_zero hJ0' hc)) hs) a2 a1
  obtain ⟨m, hm, hzm⟩ := hz.exists_pow_eq_one
  have hψ : reflexNorm Dw c (v : E) ≠ 0 := isBe_ne_zero hs (isBe_principal Dw c v)
  have hψu : reflexNorm Dw c (u : E) = (∏ τ : E →+* ℂ, embF c τ h.det ^ Dw.mult τ) * reflexNorm Dw c (v : E) := by
    simp only [huv', reflexNorm, map_mul, mul_pow, Finset.prod_mul_distrib]
  rw [hψu, ← _root_.mul_assoc, ← _root_.mul_assoc, hN, hN'] at ez
  have ez' := mul_right_cancel₀ hψ ez
  refine ⟨m, hm, ?_⟩
  rw [ez', _root_.mul_assoc z, mul_pow z, hzm, _root_.one_mul]

end GlobalTheory.BetaChange
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.Dict

theorem perFr_castFr_of_sameSp {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X' X : Data E r}
    (h : SameSp X' X) (x : Frame X'.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    Formalism.L2.PjFree.perFr X' x v τ i = Formalism.L2.PjFree.perFr X (castFr h.psi x) v τ i := by
  obtain ⟨h1, h2, h3, -, -⟩ := h
  cases X'
  cases X
  dsimp only at h1 h2 h3
  subst h1 h2 h3
  rfl

theorem exists_anFib_all_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ n : ℕ, Even n → ∃ s : c.F →+* ℂ, letI : Algebra c.F ℂ := s.toAlgebra; ∃ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (hr : X.p0 + Dw.p = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ Dw.p X.p0 (Fin n)), IsSympl X bas ∧ r = Dw.p + Dw.q ∧ (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) ∧ (∀ j, rowType X (idx j) = relab c s (e j).1) ∧ ∀ y : FrPt Xo c ℂ, ∃ (y₀ : FrPt Xo c ℂ) (t : Ix Dw → ℂˣ) (x : Frame X.Ψ r) (L : Lt E r), FrBor t y₀ y ∧ x ∈ X.dom ∧ SelfD X L ∧ Nonempty (AnFib X bas idx e x L y₀) := by
  intro E _ _ _ H Dw l Xo c h1 n hn
  obtain ⟨ξ, hξ, hξ0, hneg⟩ := GlobalTheory.SpanInhab.exists_imag_neg H
  obtain ⟨Gm, φ, hφ⟩ := GlobalTheory.exists_herm_coord_of_datum E H Dw (-ξ)
    (by rw [show cc (-ξ) = -cc ξ by simp [cc], hξ]) (neg_ne_zero.2 hξ0) _ rfl
  have hσ : Formalism.L2.PjFree.GoodEmb c c.F.val.toRingHom := rfl
  generalize c.F.val.toRingHom = σ at hσ
  obtain ⟨U, hU, -, ⟨k₀⟩, -, hG, -⟩ :=
    GlobalTheory.FrameUnif.exists_unf_hasPrinc E H Dw l Xo c σ _ ξ Gm φ h1 hσ hξ hneg hφ
  obtain ⟨W⟩ := nonempty_uw hU
  have huw := GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ _ U hσ hU h1 W
  have hsame : ∀ k, SameSp (U.X k) (U.X k₀) := fun k =>
    ⟨Finset.ext fun τ => ((hU.2.1 k).2 τ).trans ((hU.2.1 k₀).2 τ).symm, (hG k).1.trans (hG k₀).1.symm,
      (hU.2.1 k).1.trans (hU.2.1 k₀).1.symm, (hG k).2.trans (hG k₀).2.symm,
      by rw [(huw k).1, (huw k₀).1, (hG k).2, (hG k₀).2]⟩
  have hdom : Formalism.L2.Pj.Dom (fun _ : (E →+* ℂ) × ℕ => 0) n := ⟨fun _ => antitone_const, hn⟩
  choose Dc hDe using fun k => GlobalTheory.Dict.exists_dic E H Dw l c σ _ W.g n (U.X k) (fun _ => 0) W.e hσ rfl
    (hU.2.1 k).1 (hU.2.1 k).2 (huw k).2.1 hdom
  have hper : ∀ k x v j, pv (U.X k) (Dc k).idx x v j =
      Formalism.L2.PjFree.perFr (U.X k) x v (relab c σ (W.e j).1) (W.e j).2 := fun k x v j => by
    rw [(Dc k).per_eq, (hDe k).1]
  have hty : ∀ k j, rowType (U.X k) ((Dc k).idx j) = relab c σ (W.e j).1 := fun k j => by
    rw [(Dc k).ty_eq, (hDe k).1]
  refine ⟨σ, _, W.g, U.X k₀, (Dc k₀).bas, (Dc k₀).idx, W.e, (Dc k₀).hr, (Dc k₀).eL, (Dc k₀).sympl, rfl,
    fun ℓ => ?_, hty k₀, fun y => ?_⟩
  · rw [(Dc k₀).dir_eq, (hDe k₀).1]
  · let _ : Algebra c.F ℂ := σ.toAlgebra
    obtain ⟨k, x, t, hx, ht⟩ := (GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ _ U hσ hU).2 y
    obtain ⟨A, -⟩ := GlobalTheory.Dict.uw_anFib E H Dw l Xo c σ _ U hσ hU h1 W k (Dc k).bas (Dc k).idx (Dc k).sympl
      (hper k) (hty k) x hx
    obtain ⟨e1, -, e2, A', -⟩ := GlobalTheory.Dict.anFib_move E H Dw l Xo c _ W.g (U.X k) (U.X k₀) (hsame k)
      (Dc k).bas (Dc k).idx (Dc k₀).bas (Dc k₀).idx W.e x.1 (U.X k).Λ (unC U k x) A 1 (Dc k).sympl (Dc k₀).sympl
      x.2 (huw k).2.1 (by simp [IsUn])
      (fun v => funext fun j => by rw [hper, hper, perFr_castFr_of_sameSp (hsame k)])
      (fun j => by rw [hty, hty])
    exact ⟨unC U k x, t, _, _, ht, e1, e2, ⟨A'⟩⟩

end GlobalTheory.Dict
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.Dict.RootsMove

section Abstract

variable {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] {n : ℕ}

private theorem inv_lemma' {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] {M k : ℕ}
    (hM : ∀ x : Q, (M : R) • x = 0) (hk : k.Coprime M) :
    ∃ c : R, ∀ x : Q, (c * k) • x = x := by
  refine ⟨(Nat.gcdA k M : R), fun x => ?_⟩
  have h := Nat.gcd_eq_gcd_ab k M
  rw [hk.gcd_eq_one] at h
  have h2 : ((1 : ℤ) : R) = ((k * Nat.gcdA k M + M * Nat.gcdB k M : ℤ) : R) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : R)) h
  push_cast at h2
  have h3 : (Nat.gcdA k M : R) * k = 1 - (M : R) * Nat.gcdB k M := by linear_combination -h2
  rw [h3, sub_smul, one_smul, mul_smul, hM, sub_zero]

private theorem sum_smul_sum_smul_eq_mul_apply {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] {n : ℕ}
    (c d : Matrix (Fin n) (Fin n) R) (q : Fin n → Q) (i : Fin n) :
    ∑ j, c i j • ∑ l, d j l • q l = ∑ l, (c * d) i l • q l := by
  simp only [Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, mul_smul]
  exact Finset.sum_comm

private theorem sum_smul_one_apply_smul {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] {n : ℕ}
    (m : R) (q : Fin n → Q) (i : Fin n) :
    ∑ l, (m • (1 : Matrix (Fin n) (Fin n) R)) i l • q l = m • q i := by
  simp [Matrix.one_apply]

theorem exists_perm {M k m : ℕ} (hM : ∀ x : Q, (M : R) • x = 0) (hk : k.Coprime M) (hm : m.Coprime M)
    (a b : Matrix (Fin n) (Fin n) R) (hab : a * b = (m : R) • 1) (hba : b * a = (m : R) • 1) :
    ∃ e : (Fin n → Q) ≃ (Fin n → Q), ∀ q i, (k : R) • e q i = ∑ j, a i j • q j := by
  obtain ⟨ck, hck⟩ := inv_lemma' hM hk
  obtain ⟨cm, hcm⟩ := inv_lemma' hM hm
  have hfix : ∀ x : Q, ck • (cm * k) • (m : R) • x = x := fun x => by
    rw [smul_smul, smul_smul, show ck * (cm * k) * m = (ck * k) * (cm * m) by ring, mul_smul, hcm, hck]
  refine ⟨{ toFun := fun q i => ck • ∑ j, a i j • q j
            invFun := fun q i => (cm * k) • ∑ j, b i j • q j
            left_inv := ?_
            right_inv := ?_ }, fun q i => ?_⟩
  · intro q
    funext i
    show (cm * k) • ∑ j, b i j • (ck • ∑ l, a j l • q l) = q i
    have e1 : ∑ j, b i j • (ck • ∑ l, a j l • q l) = ck • ∑ j, b i j • ∑ l, a j l • q l := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
    rw [e1, sum_smul_sum_smul_eq_mul_apply, hba, sum_smul_one_apply_smul, smul_comm, hfix]
  · intro q
    funext i
    show ck • ∑ j, a i j • ((cm * k) • ∑ l, b j l • q l) = q i
    have e1 : ∑ j, a i j • ((cm * k) • ∑ l, b j l • q l) = (cm * k) • ∑ j, a i j • ∑ l, b j l • q l := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
    rw [e1, sum_smul_sum_smul_eq_mul_apply, hab, sum_smul_one_apply_smul, hfix]
  · show (k : R) • ck • ∑ j, a i j • q j = _
    rw [smul_smul, mul_comm, hck]

theorem int_of_coprime {x : ℚ} {s t : ℕ} (h : s.Coprime t) {a b : ℤ} (ha : (s : ℚ) * x = a)
    (hb : (t : ℚ) * x = b) : ∃ c : ℤ, x = c := by
  refine ⟨Nat.gcdA s t * a + Nat.gcdB s t * b, ?_⟩
  have h' := Nat.gcd_eq_gcd_ab s t
  rw [h.gcd_eq_one] at h'
  have h'' : ((1 : ℤ) : ℚ) = ((s * Nat.gcdA s t + t * Nat.gcdB s t : ℤ) : ℚ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) h'
  push_cast at h'' ⊢
  rw [← ha, ← hb]
  linear_combination x * h''

private theorem heisS_heisS {K1 K2 : Type} [Fintype K1] [Fintype K2] (a b a' b' : Matrix K1 K2 ℚ)
    (φ : Matrix K1 K2 ℚ → ℂ) :
    heisS a b (heisS a' b' φ) =
      cexp (Real.pi * I * ((∑ k, (a k ⬝ᵥ b' k - a' k ⬝ᵥ b k) : ℚ) : ℂ)) •
        heisS (a + a') (b + b') φ := by
  funext x
  have hq : (∑ k, (2 * ((x - b) k ⬝ᵥ a' k) - a' k ⬝ᵥ b' k)) +
      (∑ k, (2 * (x k ⬝ᵥ a k) - a k ⬝ᵥ b k)) =
      (∑ k, (a k ⬝ᵥ b' k - a' k ⬝ᵥ b k)) +
        ∑ k, (2 * (x k ⬝ᵥ (a + a') k) - (a + a') k ⬝ᵥ (b + b') k) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e1 : (x - b) k = x k - b k := rfl
    have e2 : (a + a') k = a k + a' k := rfl
    have e3 : (b + b') k = b k + b' k := rfl
    rw [e1, e2, e3]
    simp only [sub_dotProduct, add_dotProduct, dotProduct_add, dotProduct_comm (b k) (a' k)]
    ring
  simp only [heisS, Pi.smul_apply, smul_eq_mul]
  rw [sub_sub, _root_.mul_assoc, ← Complex.exp_add, _root_.mul_left_comm, ← Complex.exp_add, ← _root_.mul_add,
    ← _root_.mul_add]
  congr 3
  exact_mod_cast hq

end Abstract

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r n g : ℕ} {H : Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {X : Data E r} {L : Lt E r}

theorem heisG_comp {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (hs : IsSympl X bas)
    (y y' : Matrix (Fin n) (Fin r) E) {φ : TF n g} (hφ : IsSB φ) : heisG X bas y (heisG X bas y' φ) =
      cexp (-(Real.pi * I * ((∑ k, EF X (y k) (y' k) : ℚ) : ℂ))) • heisG X bas (y + y') φ := by
  have hA : (Matrix.of fun k i => crd X bas ((y + y') k) (Sum.inl i) : Matrix (Fin n) (Fin g) ℚ) =
      Matrix.of (fun k i => crd X bas (y k) (Sum.inl i)) +
        Matrix.of (fun k i => crd X bas (y' k) (Sum.inl i)) := by
    ext k i
    show crd X bas (y k + y' k) _ = _
    rw [crd_add hs]
    rfl
  have hB : (Matrix.of fun k i => crd X bas ((y + y') k) (Sum.inr i) : Matrix (Fin n) (Fin g) ℚ) =
      Matrix.of (fun k i => crd X bas (y k) (Sum.inr i)) +
        Matrix.of (fun k i => crd X bas (y' k) (Sum.inr i)) := by
    ext k i
    show crd X bas (y k + y' k) _ = _
    rw [crd_add hs]
    rfl
  have hE : (∑ k, ((Matrix.of fun k i => crd X bas (y k) (Sum.inl i) : Matrix (Fin n) (Fin g) ℚ) k ⬝ᵥ
        (Matrix.of fun k i => crd X bas (y' k) (Sum.inr i) : Matrix (Fin n) (Fin g) ℚ) k -
        (Matrix.of fun k i => crd X bas (y' k) (Sum.inl i) : Matrix (Fin n) (Fin g) ℚ) k ⬝ᵥ
        (Matrix.of fun k i => crd X bas (y k) (Sum.inr i) : Matrix (Fin n) (Fin g) ℚ) k)) =
      -∑ k, EF X (y k) (y' k) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [EF_crd hs]
    simp only [dotProduct, Matrix.of_apply, neg_neg, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [heisG]
  rw [heisS_heisS, hA, hB, hE]
  push_cast
  ring_nf

theorem sumEF_smul (s t : ℕ) (y y' : Matrix (Fin n) (Fin r) E) :
    ∑ k, EF X (((s : E) • y) k) (((t : E) • y') k) = s * t * ∑ k, EF X (y k) (y' k) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show EF X ((s : E) • y k) ((t : E) • y' k) = _
  have hs' : ((s : E) • y k) = ((s : ℚ) • y k) := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  have ht' : ((t : E) • y' k) = ((t : ℚ) • y' k) := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [hs', ht']
  change EFBil X ((s : ℚ) • y k) ((t : ℚ) • y' k) = _
  rw [LinearMap.map_smul₂, LinearMap.map_smul]
  change (s : ℚ) • (t : ℚ) • EF X (y k) (y' k) = _
  simp only [smul_eq_mul]
  ring

theorem heisG_add_two {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (hs : IsSympl X bas) (hL : SelfD X L) {M : ℕ}
    {Λ : Lt E n} (hΛ : Λ ∈ Vset E n M) {w : E} (hw : IsIntegral ℤ w) {u : TF n g}
    (hu : IsVac X bas w (tens Λ L) u) (y : Matrix (Fin n) (Fin r) E) {d : Matrix (Fin n) (Fin r) E}
    (hd : d ∈ tens Λ L) {c : ℤ} (hc : ∑ k, EF X (y k) (d k) = c) :
    heisG X bas (y + ((2 : ℕ) : E) • d) u = heisG X bas y u := by
  obtain ⟨hsb, -, hfix⟩ := hu
  have h2d : ((2 : ℕ) : E) • d ∈ tens Λ L := by
    rw [Nat.cast_smul_eq_nsmul]
    exact AddSubgroup.nsmul_mem _ hd 2
  obtain ⟨m, hm⟩ := (TensLat.tens_selfDual hΛ hL d).mp hd (w • d) (TensLat.smul_mem_tens hΛ hw hd)
  have heps : epsW X w (((2 : ℕ) : E) • d) = 1 := by
    unfold epsW
    have hsum : ∑ k, EF X ((((2 : ℕ) : E) • d) k) (w • (((2 : ℕ) : E) • d) k) =
        ∑ k, EF X ((((2 : ℕ) : E) • d) k) ((((2 : ℕ) : E) • (w • d)) k) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      show w • ((2 : ℕ) : E) • d k = ((2 : ℕ) : E) • w • d k
      exact smul_comm _ _ _
    have hq : ∑ k, EF X ((((2 : ℕ) : E) • d) k) ((((2 : ℕ) : E) • (w • d)) k) = ((4 * m : ℤ) : ℚ) := by
      rw [sumEF_smul, hm]
      push_cast
      ring
    rw [hsum, hq]
    have e : (Real.pi : ℂ) * I * (((4 * m : ℤ) : ℚ) : ℂ) = ((2 * m : ℤ) : ℂ) * (2 * Real.pi * I) := by
      push_cast
      ring
    rw [e]
    exact Complex.exp_int_mul_two_pi_mul_I _
  have h2fix : heisG X bas (((2 : ℕ) : E) • d) u = u := by
    have := hfix _ h2d
    rwa [heps, one_smul] at this
  have h1 := sumEF_smul (X := X) 1 2 y d
  simp only [Nat.cast_one, one_smul] at h1
  have hexp : cexp (-(Real.pi * I * ((∑ k, EF X (y k) ((((2 : ℕ) : E) • d) k) : ℚ) : ℂ))) = 1 := by
    have hq : ∑ k, EF X (y k) ((((2 : ℕ) : E) • d) k) = ((2 * c : ℤ) : ℚ) := by
      rw [h1, hc]
      push_cast
      ring
    rw [hq]
    have e : -((Real.pi : ℂ) * I * (((2 * c : ℤ) : ℚ) : ℂ)) = ((-c : ℤ) : ℂ) * (2 * Real.pi * I) := by
      push_cast
      ring
    rw [e]
    exact Complex.exp_int_mul_two_pi_mul_I _
  have hcomp := heisG_comp hs y (((2 : ℕ) : E) • d) hsb
  rw [h2fix, hexp, one_smul] at hcomp
  exact hcomp.symm

omit [IsCMField E] in

theorem mul_mem_tens {Λ Λ' : Lt E n} {h : Matrix (Fin n) (Fin n) E} (hh : ∀ v ∈ Λ, h *ᵥ v ∈ Λ')
    {y : Matrix (Fin n) (Fin r) E} (hy : y ∈ tens Λ L) : h * y ∈ tens Λ' L := by
  let f : Matrix (Fin n) (Fin r) E →+ Matrix (Fin n) (Fin r) E :=
    { toFun := fun z => h * z
      map_zero' := Matrix.mul_zero h
      map_add' := fun z z' => Matrix.mul_add h z z' }
  have key : tens Λ L ≤ (tens Λ' L).comap f := by
    refine TensLat.tens_le fun v hv u hu => ?_
    show h * vecMulVec v u ∈ tens Λ' L
    have e : h * vecMulVec v u = vecMulVec (h *ᵥ v) u := by
      ext i j
      simp [Matrix.mul_apply, vecMulVec_apply, mulVec, dotProduct, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    exact TensLat.pure_mem (hh v hv) hu
  exact key hy

omit [IsCMField E] in

theorem smul_mem_tens' {Λ Λ' : Lt E n} {s : E} (hh : ∀ v ∈ Λ, s • v ∈ Λ')
    {y : Matrix (Fin n) (Fin r) E} (hy : y ∈ tens Λ L) : s • y ∈ tens Λ' L := by
  have key : tens Λ L ≤ (tens Λ' L).comap
      (DistribSMul.toAddMonoidHom (Matrix (Fin n) (Fin r) E) s) := by
    refine TensLat.tens_le fun v hv u hu => ?_
    show s • vecMulVec v u ∈ tens Λ' L
    have e : s • vecMulVec v u = vecMulVec (s • v) u := by
      ext i j
      simp [vecMulVec_apply]
      ring
    rw [e]
    exact TensLat.pure_mem (hh v hv) hu
  exact key hy

theorem exists_int {M : ℕ} {Λ Λ' : Lt E n} (hΛ : Λ ∈ Vset E n M) (hΛ' : Λ' ∈ Vset E n M)
    {h : Matrix (Fin n) (Fin n) E} (hh : Moves h Λ Λ') :
    ∃ (k : ℕ) (a : Matrix (Fin n) (Fin n) (𝓞 E)), k.Coprime M ∧ ∀ i j, (a i j : E) = (k : E) * h i j := by
  obtain ⟨-, -, s, -, hsc, -, hs2⟩ := hΛ
  obtain ⟨-, -, s', -, hsc', hs1', -⟩ := hΛ'
  have hcol : ∀ j, ∃ c : Fin n → 𝓞 E, ∀ i, (c i : E) = ((s * s' : ℕ) : E) * h i j := by
    intro j
    have he : (Pi.single j (1 : E) : Fin n → E) ∈ stdL E n := Submodule.subset_span ⟨j, rfl⟩
    have h3 : (s' : E) • h *ᵥ ((s : E) • (Pi.single j (1 : E) : Fin n → E)) ∈ stdL E n :=
      hs1' _ ((hh _).mp (hs2 _ he))
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mp h3
    refine ⟨c, fun i => ?_⟩
    have hci := congrFun hc i
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, mulVec_smul, mulVec_single_one] at hci
    rw [Algebra.smul_def, _root_.mul_one] at hci
    rw [show (c i : E) = algebraMap (𝓞 E) E (c i) from rfl, hci]
    simp only [smul_eq_mul, Matrix.col_apply]
    push_cast
    ring
  choose c hc using hcol
  exact ⟨s * s', Matrix.of fun i j => c j i, Nat.Coprime.mul_left hsc hsc', fun i j => hc j i⟩

theorem exists_levPerm {Λ Λ' : Lt E n} (hΛ : Λ ∈ Vset E n l.M) (hΛ' : Λ' ∈ Vset E n l.M)
    {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1) (hh : Moves h Λ Λ') :
    ∃ e : (Fin n → LevQ Dw l) ≃ (Fin n → LevQ Dw l), ∀ q, LevMoves h q (e q) := by
  obtain ⟨k, a, hk, ha⟩ := exists_int hΛ hΛ' hh
  have hinv : h * ccT h = 1 := _root_.mul_eq_one_comm.mp hu
  have hh' : Moves (ccT h) Λ' Λ := by
    intro v
    rw [hh (ccT h *ᵥ v), mulVec_mulVec, hinv, one_mulVec]
  obtain ⟨k', b, hk', hb⟩ := exists_int hΛ' hΛ hh'
  have key : ∀ (A B : Matrix (Fin n) (Fin n) E), A * B = 1 → ∀ (c d : Matrix (Fin n) (Fin n) (𝓞 E))
      (kc kd : ℕ), (∀ i j, (c i j : E) = (kc : E) * A i j) → (∀ i j, (d i j : E) = (kd : E) * B i j) →
      c * d = ((kc * kd : ℕ) : 𝓞 E) • 1 := by
    intro A B hAB c d kc kd hc hd
    ext i j
    have e1 : ((c * d) i j : E) = ((kc * kd : ℕ) : E) * (A * B) i j := by
      simp only [Matrix.mul_apply, map_sum, map_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [show (algebraMap (𝓞 E) E (c i l)) = (c i l : E) from rfl,
        show (algebraMap (𝓞 E) E (d l j)) = (d l j : E) from rfl, hc, hd]
      push_cast
      ring
    rw [show (((c * d) i j : 𝓞 E) : E) = ((c * d) i j : E) from rfl, e1, hAB]
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have hab := key h (ccT h) hinv a b k k' ha hb
  have hba := key (ccT h) h hu b a k' k hb ha
  rw [Nat.mul_comm k' k] at hba
  have hMb : (l.M : 𝓞 E) ∈ l.Mb := by
    have : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]
      exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_inf (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) this).1
  have hM : ∀ x : LevQ Dw l, ((l.M : ℕ) : 𝓞 E) • x = 0 := by
    intro x
    refine Submodule.Quotient.induction_on _ x fun z => ?_
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hMb trivial
  obtain ⟨e, he⟩ := exists_perm hM hk (Nat.Coprime.mul_left hk hk') a b hab hba
  exact ⟨e, fun q => ⟨k, a, hk, ha, fun i => he q i⟩⟩

theorem exists_pow {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} {N : ℕ}
    {Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E} (hY : IsRoots l L mk N Y) (q : Fin n → LevQ Dw l) :
    ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ s ∈ l.Mb, ∃ U : Matrix (Fin n) (Fin r) E, (∀ b, U b ∈ L) ∧
      ((s : E) ^ j) • Y q = ((2 * N : ℕ) : E) • U := by
  have hb : ∀ b, ∃ j : ℕ, ∀ s ∈ l.Mb ^ j, ∃ u ∈ L, s • Y q b = (2 * N) • u := fun b => (hY q b).2
  choose j hj using hb
  refine ⟨Finset.univ.sup j, fun i hi s hs => ?_⟩
  have hu : ∀ b, ∃ u ∈ L, (s ^ i) • Y q b = (2 * N) • u := fun b =>
    hj b _ (Ideal.pow_le_pow_right (le_trans (Finset.le_sup (Finset.mem_univ b)) hi)
      (Ideal.pow_mem_pow hs i))
  choose U hUL hU using hu
  refine ⟨fun b => U b, hUL, ?_⟩
  funext b
  show ((s : E) ^ i) • Y q b = ((2 * N : ℕ) : E) • U b
  rw [Nat.cast_smul_eq_nsmul, ← hU b, ← algebraMap_smul E (s ^ i) (Y q b), map_pow]

theorem ef_int (hL : SelfD X L) {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (hmk : ∀ a, mk a ∈ L) {y d u : Fin r → E}
    {a : Dw.La} (ha : a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La)) (hy : y - (l.M : E)⁻¹ • mk a ∈ L) (hd : d ∈ L)
    (hu : u ∈ L) {s : 𝓞 E} (hs : 1 - s ∈ Mfr l) (hsd : (s : E) • d = (l.M : E) • u) : ∃ c : ℤ, EF X y d = c := by
  obtain ⟨-, hself⟩ := hL
  have hint : ∀ x ∈ L, ∀ z ∈ L, ∃ k : ℤ, EF X x z = k := fun x hx z hz => (hself x).mp hx z hz
  have hM0 : (l.M : E) ≠ 0 := by
    have h3 := l.three_le
    exact_mod_cast (show l.M ≠ 0 by omega)
  have addL : ∀ v v' z, EF X (v + v') z = EF X v z + EF X v' z := fun v v' z => by
    change EFBil X (v + v') z = EFBil X v z + EFBil X v' z
    rw [LinearMap.map_add₂]
  have addR : ∀ v z z', EF X v (z + z') = EF X v z + EF X v z' := fun v z z' => by
    change EFBil X v (z + z') = EFBil X v z + EFBil X v z'
    rw [LinearMap.map_add]
  have hs' : 1 - s ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := hs
  obtain ⟨p, hp, hpt⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).mp hs'
  have hpt' : H.bar p = 1 - s := hpt
  have hccp : cc (p : E) = 1 - (s : E) := by
    have hb := H.bar_eq p
    rw [hpt'] at hb
    change IsCMField.complexConj E (p : E) = _
    rw [← hb]
    push_cast
    rfl
  have hpa : p • a ∈ (Ideal.span {(l.M : 𝓞 E)}) • (⊤ : Submodule (𝓞 E) Dw.La) := by
    rw [← l.prod, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hp ha
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hpa
  obtain ⟨a', -, ha'⟩ := hpa
  have e3 : (p : E) • ((l.M : E)⁻¹ • mk a) = mk a' := by
    have h1 : (p : E) • mk a = mk (p • a) := by
      rw [LinearMap.map_smul]
      exact algebraMap_smul E p (mk a)
    have h2 : mk ((l.M : 𝓞 E) • a') = (l.M : E) • mk a' := by
      rw [LinearMap.map_smul, ← algebraMap_smul E (l.M : 𝓞 E) (mk a'), map_natCast]
    rw [smul_comm, h1, ← ha', h2, smul_smul, inv_mul_cancel₀ hM0, one_smul]
  have hccM : cc ((l.M : E)⁻¹) = (l.M : E)⁻¹ := by
    change IsCMField.complexConj E ((l.M : E)⁻¹) = _
    rw [map_inv₀, map_natCast]
  have split1 : EF X y d = EF X (y - (l.M : E)⁻¹ • mk a) d + EF X ((l.M : E)⁻¹ • mk a) d := by
    rw [← addL, sub_add_cancel]
  have split2 : EF X ((l.M : E)⁻¹ • mk a) d =
      EF X ((l.M : E)⁻¹ • mk a) ((s : E) • d) + EF X ((l.M : E)⁻¹ • mk a) ((1 - (s : E)) • d) := by
    rw [← addR, ← add_smul, add_sub_cancel, one_smul]
  have t2 : EF X ((l.M : E)⁻¹ • mk a) ((s : E) • d) = EF X (mk a) u := by
    rw [hsd, TensLat.EF_smul X, hccM, smul_smul, inv_mul_cancel₀ hM0, one_smul]
  have t3 : EF X ((l.M : E)⁻¹ • mk a) ((1 - (s : E)) • d) = EF X (mk a') d := by
    rw [← hccp, ← TensLat.EF_smul X, e3]
  obtain ⟨k1, hk1⟩ := hint _ hy d hd
  obtain ⟨k2, hk2⟩ := hint _ (hmk a) u hu
  obtain ⟨k3, hk3⟩ := hint _ (hmk a') d hd
  refine ⟨k1 + k2 + k3, ?_⟩
  rw [split1, split2, t2, t3, hk1, hk2, hk3]
  push_cast
  ring

private theorem mem_of_natCast_smul_mem_of_coprime {F V : Type} [Field F] [AddCommGroup V] [Module F V] (G : AddSubgroup V) {p q : ℕ}
    (hpq : p.Coprime q) {v : V} (hp : (p : F) • v ∈ G) (hq : (q : F) • v ∈ G) : v ∈ G := by
  have h := Nat.gcd_eq_gcd_ab p q
  rw [hpq.gcd_eq_one] at h
  have h2 : ((Nat.gcdA p q : ℤ) : F) * p + ((Nat.gcdB p q : ℤ) : F) * q = 1 := by
    have := congrArg (fun z : ℤ => (z : F)) h
    push_cast at this
    linear_combination -this
  have hv : v = Nat.gcdA p q • ((p : F) • v) + Nat.gcdB p q • ((q : F) • v) := by
    rw [← Int.cast_smul_eq_zsmul F, ← Int.cast_smul_eq_zsmul F, smul_smul, smul_smul, ← add_smul, h2,
      one_smul]
  rw [hv]
  exact add_mem (AddSubgroup.zsmul_mem _ hp _) (AddSubgroup.zsmul_mem _ hq _)

private theorem mem_mul_smul_of_mem_smul_of_sup_eq_top {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {I J : Ideal R}
    {P : Submodule R V} (hIJ : I ⊔ J = ⊤) {x : V} (hI : x ∈ I • P) (hJ : x ∈ J • P) :
    x ∈ (I * J) • P := by
  have h1 : (1 : R) ∈ I ⊔ J := by
    rw [hIJ]
    exact Submodule.mem_top
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp h1
  have hx : x = i • x + j • x := by rw [← add_smul, hij, one_smul]
  rw [hx]
  refine add_mem ?_ ?_
  · rw [Submodule.mul_smul]
    exact Submodule.smul_mem_smul hi hJ
  · rw [_root_.mul_comm, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hj hI

private theorem map_mul_row_mem_of_rows_mem {F : Type} [Field F] [NumberField F] {m s : ℕ} {L : Submodule (𝓞 F) (Fin s → F)}
    (B : Matrix (Fin m) (Fin m) (𝓞 F)) (W : Matrix (Fin m) (Fin s) F) (hW : ∀ i, W i ∈ L) (i : Fin m) :
    (B.map (algebraMap (𝓞 F) F) * W) i ∈ L := by
  have e : (B.map (algebraMap (𝓞 F) F) * W) i = ∑ j, B i j • W j := by
    funext c
    simp only [Matrix.mul_apply, Matrix.map_apply, Finset.sum_apply, Pi.smul_apply, Algebra.smul_def]
  rw [e]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hW j)

private theorem natCast_smul_mem_of_span_smul_stdLat_le {F : Type} [Field F] [NumberField F] {m N : ℕ} {Λ : Lt F m}
    (hle : Ideal.span {(N : 𝓞 F)} • stdLat F m ≤ (⟨Λ⟩ : GenLat F m).Ln) :
    ∀ v ∈ stdL F m, (N : F) • v ∈ Λ := by
  intro v hv
  have hv' : v ∈ stdLat F m := by
    refine Submodule.span_le.mpr ?_ hv
    rintro _ ⟨j, rfl⟩
    refine Submodule.mem_pi.mpr fun i _ => ?_
    rw [Submodule.mem_one]
    by_cases hij : i = j
    · subst hij
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [hij]⟩
  have h1 := hle (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (N : 𝓞 F)) hv')
  have h2 : (N : 𝓞 F) • v = (N : F) • v := by
    rw [← algebraMap_smul F (N : 𝓞 F) v, map_natCast]
  rw [← h2]
  exact h1.1

private theorem matrix_mul_row_eq_sum_smul {F : Type} [Field F] {m s : ℕ} (A : Matrix (Fin m) (Fin m) F)
    (Z : Matrix (Fin m) (Fin s) F) (i : Fin m) :
    (A * Z) i = ∑ j, A i j • Z j := by
  funext c
  simp [Matrix.mul_apply, Finset.sum_apply]

theorem roots_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (n : ℕ), IsSympl X bas → Even n → ∀ L : Lt E r, SelfD X L → ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ Λ ∈ Vset E n l.M, ∀ Λ' ∈ Vset E n l.M, Moves h Λ Λ' → ∀ N N' : ℕ, (⟨Λ⟩ : GenLat E n).LevOK N l.M → (⟨Λ'⟩ : GenLat E n).LevOK N' l.M → ∀ Y Y' : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E, IsRoots l L mk N Y → IsRoots l L mk N' Y' → (∃ e : (Fin n → LevQ Dw l) ≃ (Fin n → LevQ Dw l), ∀ q, LevMoves h q (e q)) ∧ ∀ q q', LevMoves h q q' → ∀ u : TF n g, IsVac X bas (H.w0 : E) (tens Λ' L) u → heisG X bas (Y' q') u = heisG X bas (h * Y q) u := by
  intro E _ _ _ H Dw l r X g bas n hs _ L hL mk hmk h hu Λ hΛ Λ' hΛ' hh N N' hN hN' Y Y' hY hY'
  refine ⟨exists_levPerm (Dw := Dw) hΛ hΛ' hu hh, ?_⟩
  intro q q' hmv u hvac
  obtain ⟨k1, g1, hk1, hg1, hq⟩ := hmv
  have cs : ∀ (x : 𝓞 E) (v : Fin r → E), x • v = (x : E) • v := fun x v => (algebraMap_smul E x v).symm
  have hM0 : (l.M : E) ≠ 0 := by
    have h3 := l.three_le
    exact_mod_cast (show l.M ≠ 0 by omega)
  have hMc : ((l.M : 𝓞 E) : E) = (l.M : E) := map_natCast (algebraMap (𝓞 E) E) l.M
  have hk1c : ((k1 : 𝓞 E) : E) = (k1 : E) := map_natCast (algebraMap (𝓞 E) E) k1
  have hMb : (l.M : 𝓞 E) ∈ l.Mb := by
    have : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]
      exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_inf (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) this).1
  have h1top : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.coprime]
    exact Submodule.mem_top
  obtain ⟨s0, hs0, t0, ht0, hst⟩ := Submodule.mem_sup.mp h1top
  obtain ⟨j1, hj1⟩ := exists_pow hY q
  obtain ⟨j2, hj2⟩ := exists_pow hY' q'
  obtain ⟨U1, hU1L, hU1⟩ := hj1 (max j1 j2) (le_max_left _ _) s0 hs0
  obtain ⟨U2, hU2L, hU2⟩ := hj2 (max j1 j2) (le_max_right _ _) s0 hs0
  obtain ⟨V1, hV1L, hV1⟩ := hj1 (max j1 j2) (le_max_left _ _) _ hMb
  obtain ⟨V2, hV2L, hV2⟩ := hj2 (max j1 j2) (le_max_right _ _) _ hMb
  rw [hMc] at hV1 hV2
  obtain ⟨J, hJ⟩ : ∃ J, J = max j1 j2 := ⟨_, rfl⟩
  rw [← hJ] at hU1 hU2 hV1 hV2
  have h1s : 1 - s0 ^ J ∈ Mfr l := by
    have hd := sub_dvd_pow_sub_pow (1 : 𝓞 E) s0 J
    rw [one_pow] at hd
    obtain ⟨c, hc⟩ := hd
    rw [hc]
    have : 1 - s0 = t0 := by rw [← hst]; ring
    rw [this]
    exact Ideal.mul_mem_right c _ ht0
  obtain ⟨-, ⟨n1, hn1⟩, hNle⟩ := hN
  obtain ⟨-, ⟨n2, hn2⟩, hN'le⟩ := hN'
  have hM2 : Nat.Coprime l.M 2 := by
    have ho := l.odd
    rw [Nat.odd_iff] at ho
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega))
  obtain ⟨t, -, htc, -, ht2⟩ := hΛ'.2.2

  have hrep : ∀ j, ∃ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), Submodule.Quotient.mk a = q j ∧
      Y q j - ((l.M : E)⁻¹) • mk a ∈ L := fun j => (hY q j).1
  choose A hAm hAq hAL using hrep
  have hrep' : ∀ j, ∃ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), Submodule.Quotient.mk a = q' j ∧
      Y' q' j - ((l.M : E)⁻¹) • mk a ∈ L := fun j => (hY' q' j).1
  choose A' hA'm hA'q hA'L using hrep'
  have hC : ∀ i, ∃ Ci : Dw.La, (l.M : 𝓞 E) • Ci = (k1 : 𝓞 E) • A' i - ∑ j, g1 i j • A j := by
    intro i
    have hxb : (k1 : 𝓞 E) • A' i - ∑ j, g1 i j • A j ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
      have h0 : (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ ((k1 : 𝓞 E) • A' i - ∑ j, g1 i j • A j) = 0 := by
        simp only [map_sub, map_smul, map_sum, Submodule.mkQ_apply, hAq, hA'q]
        rw [hq i, sub_self]
      exact (Submodule.Quotient.mk_eq_zero _).mp h0
    have hxf : (k1 : 𝓞 E) • A' i - ∑ j, g1 i j • A j ∈
        l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La) :=
      sub_mem (Submodule.smul_mem _ _ (hA'm i)) (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hAm j))
    have hx := mem_mul_smul_of_mem_smul_of_sup_eq_top l.coprime hxb hxf
    rw [l.prod, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨Ci, -, hCi⟩ := hx
    exact ⟨Ci, hCi⟩
  choose C hC using hC
  obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin n) (Fin r) E, D = Y' q' - h * Y q := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : Matrix (Fin n) (Fin r) E, W = (k1 : E) • D := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : Matrix (Fin n) (Fin r) E, d = (2 : E)⁻¹ • D := ⟨_, rfl⟩
  have hWi : ∀ i, W i = (k1 : E) • Y' q' i - ∑ j, (g1 i j : E) • Y q j := by
    intro i
    rw [hW, hD]
    show (k1 : E) • (Y' q' i - (h * Y q) i) = _
    rw [matrix_mul_row_eq_sum_smul, smul_sub, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, hg1]
  have hWL : ∀ i, W i ∈ L := by
    intro i
    have hCE : (l.M : E) • mk (C i) = (k1 : E) • mk (A' i) - ∑ j, (g1 i j : E) • mk (A j) := by
      have := congrArg mk (hC i)
      simp only [map_sub, map_sum, LinearMap.map_smul, cs, hMc, hk1c] at this
      exact this
    have hmkC : mk (C i) = (l.M : E)⁻¹ • ((k1 : E) • mk (A' i) - ∑ j, (g1 i j : E) • mk (A j)) := by
      rw [← hCE, smul_smul, inv_mul_cancel₀ hM0, one_smul]
    have hsplit : W i = mk (C i) + ((k1 : E) • (Y' q' i - (l.M : E)⁻¹ • mk (A' i)) -
        ∑ j, (g1 i j : E) • (Y q j - (l.M : E)⁻¹ • mk (A j))) := by
      rw [hWi, hmkC]
      simp only [smul_sub, Finset.smul_sum, Finset.sum_sub_distrib, smul_comm ((l.M : E)⁻¹)]
      abel
    rw [hsplit]
    refine add_mem (hmk.mem _) (sub_mem ?_ (Submodule.sum_mem _ fun j _ => ?_))
    · rw [Nat.cast_smul_eq_nsmul]
      exact Submodule.smul_of_tower_mem _ k1 (hA'L i)
    · rw [← cs]
      exact Submodule.smul_mem _ _ (hAL j)
  have hg : g1.map (algebraMap (𝓞 E) E) = (k1 : E) • h := by
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, ← hg1]
  obtain ⟨Um, hUm⟩ : ∃ Um : Matrix (Fin n) (Fin r) E, Um = ((2 * n2 * k1 : ℕ) : E) • U2 -
      ((2 * n1 : ℕ) : E) • (g1.map (algebraMap (𝓞 E) E) * U1) := ⟨_, rfl⟩
  have hUmL : ∀ i, Um i ∈ L := by
    intro i
    rw [hUm]
    show ((2 * n2 * k1 : ℕ) : E) • U2 i - ((2 * n1 : ℕ) : E) • (g1.map (algebraMap (𝓞 E) E) * U1) i ∈ L
    refine sub_mem ?_ ?_
    · rw [Nat.cast_smul_eq_nsmul]
      exact Submodule.smul_of_tower_mem _ _ (hU2L i)
    · rw [Nat.cast_smul_eq_nsmul]
      exact Submodule.smul_of_tower_mem _ _ (map_mul_row_mem_of_rows_mem g1 U1 hU1L i)
  have hsW : ((s0 : E) ^ J) • W = (l.M : E) • Um := by
    rw [hUm, hg, Matrix.smul_mul, hW, hD, smul_comm, smul_sub, ← Matrix.mul_smul, hU1, hU2, Matrix.mul_smul,
      hn1, hn2]
    push_cast
    module
  have hsd : ∀ i, (((s0 ^ J : 𝓞 E)) : E) • W i = (l.M : E) • Um i := by
    intro i
    have := congrFun hsW i
    have e : ((s0 ^ J : 𝓞 E) : E) = (s0 : E) ^ J := map_pow (algebraMap (𝓞 E) E) s0 J
    rw [e]
    exact this

  have addL : ∀ v v' z, EF X (v + v') z = EF X v z + EF X v' z := fun v v' z => by
    change EFBil X (v + v') z = EFBil X v z + EFBil X v' z
    rw [LinearMap.map_add₂]
  have hEF0 : ∀ v : Fin r → E, EF X v v = 0 := fun v => by
    have := TensLat.EF_swap X v v
    linarith
  have hYd : Y' q' = h * Y q + ((2 : ℕ) : E) • d := by
    rw [hd, smul_smul, Nat.cast_two, mul_inv_cancel₀ two_ne_zero, one_smul, hD, add_sub_cancel]

  have hN'V2 : (N' : E) • V2 ∈ tens Λ' L :=
    smul_mem_tens' (natCast_smul_mem_of_span_smul_stdLat_le hN'le) ((TensLat.mem_tens_stdL L V2).mpr hV2L)
  have hNV1 : (N : E) • (h * V1) ∈ tens Λ' L := by
    rw [← Matrix.mul_smul]
    exact mul_mem_tens (fun v hv => (hh v).mp hv)
      (smul_mem_tens' (natCast_smul_mem_of_span_smul_stdLat_le hNle) ((TensLat.mem_tens_stdL L V1).mpr hV1L))
  have hdmem : d ∈ tens Λ' L := by
    refine mem_of_natCast_smul_mem_of_coprime (F := E) (tens Λ' L) (p := l.M ^ J) (q := 2 * k1 * t)
      (Nat.Coprime.pow_left J (Nat.Coprime.mul_right (Nat.Coprime.mul_right hM2 hk1.symm) htc.symm)) ?_ ?_
    · have e : ((l.M ^ J : ℕ) : E) • d = (N' : E) • V2 - (N : E) • (h * V1) := by
        rw [hd, hD, smul_comm, smul_sub, ← Matrix.mul_smul, Nat.cast_pow, hV1, hV2, Matrix.mul_smul]
        push_cast
        module
      rw [e]
      exact sub_mem hN'V2 hNV1
    · have e : ((2 * k1 * t : ℕ) : E) • d = (t : E) • W := by
        rw [hd, hW, smul_smul, smul_smul]
        congr 1
        push_cast
        field_simp
      rw [e]
      exact smul_mem_tens' ht2 ((TensLat.mem_tens_stdL L W).mpr hWL)

  have hXeq : ∑ k, EF X ((h * Y q) k) (d k) = ∑ k, EF X (Y' q' k) (d k) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hYd]
    show EF X ((h * Y q) k) (d k) = EF X ((h * Y q) k + ((2 : ℕ) : E) • d k) (d k)
    rw [addL, Nat.cast_two, two_smul, addL, hEF0]
    ring
  have hXa : ∃ z : ℤ, ((l.M ^ J : ℕ) : ℚ) * ∑ k, EF X (Y' q' k) (d k) = z := by
    obtain ⟨m, hm⟩ := (TensLat.tens_selfDual hΛ' hL _).mp hN'V2 d hdmem
    refine ⟨2 * m, ?_⟩
    have e1 := sumEF_smul (X := X) (l.M ^ J) 1 (Y' q') d
    have e2 := sumEF_smul (X := X) 2 1 ((N' : E) • V2) d
    have hMV : ((l.M ^ J : ℕ) : E) • Y' q' = ((2 : ℕ) : E) • ((N' : E) • V2) := by
      rw [Nat.cast_pow, hV2, smul_smul]
      congr 1
      push_cast
      ring
    rw [hMV] at e1
    simp only [Nat.cast_one, one_smul, _root_.mul_one] at e1 e2
    rw [hm] at e2
    rw [← e1, e2]
    push_cast
    ring
  have hXb : ∃ z : ℤ, ((2 * k1 : ℕ) : ℚ) * ∑ k, EF X (Y' q' k) (d k) = z := by
    have e3 := sumEF_smul (X := X) 1 (2 * k1) (Y' q') d
    have e4 : ((2 * k1 : ℕ) : E) • d = W := by
      rw [hd, hW, smul_smul]
      congr 1
      push_cast
      field_simp
    rw [e4] at e3
    simp only [Nat.cast_one, one_smul, _root_.one_mul] at e3
    have hz : ∀ i, ∃ z : ℤ, EF X (Y' q' i) (W i) = z := fun i =>
      ef_int hL hmk.mem (hA'm i) (hA'L i) (hWL i) (hUmL i) h1s (hsd i)
    choose z hz using hz
    refine ⟨∑ i, z i, ?_⟩
    rw [← e3]
    push_cast
    exact Finset.sum_congr rfl fun i _ => hz i
  obtain ⟨za, hza⟩ := hXa
  obtain ⟨zb, hzb⟩ := hXb
  obtain ⟨c, hc⟩ := int_of_coprime
    (Nat.Coprime.pow_left J (Nat.Coprime.mul_right hM2 hk1.symm)) hza hzb
  have hcX : ∑ k, EF X ((h * Y q) k) (d k) = c := by rw [hXeq, hc]
  have hmain := heisG_add_two hs hL hΛ' (NumberField.RingOfIntegers.isIntegral_coe H.w0) hvac (h * Y q) hdmem hcX
  rw [hYd]
  exact hmain

end GlobalTheory.Dict.RootsMove
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.roots_levelPoints_same_vacuum_translates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (n : ℕ), IsSympl X bas → Even n → ∀ L : Lt E r, SelfD X L → ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ Λ ∈ Vset E n l.M, ∀ Λ' ∈ Vset E n l.M, Moves h Λ Λ' → ∀ N N' : ℕ, (⟨Λ⟩ : GenLat E n).LevOK N l.M → (⟨Λ'⟩ : GenLat E n).LevOK N' l.M → ∀ Y Y' : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E, IsRoots l L mk N Y → IsRoots l L mk N' Y' → (∃ e : (Fin n → LevQ Dw l) ≃ (Fin n → LevQ Dw l), ∀ q, LevMoves h q (e q)) ∧ ∀ q q', LevMoves h q q' → ∀ u : TF n g, IsVac X bas (H.w0 : E) (tens Λ' L) u → heisG X bas (Y' q') u = heisG X bas (h * Y q) u := by
  atlas_forward_decl GlobalTheory.Dict.RootsMove.roots_move
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

open GlobalTheory.Dict.ColPoly in

theorem GlobalTheory.Phase.polyDeriv_pushLet_eq_hAct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l), ∀ (s : c.F →+* ℂ) (r g : ℕ) (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (q0 n : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → (∀ j, rowType X (idx j) = relab c s (e j).1) → ∀ (h : Matrix (Fin n) (Fin n) E) (P : MvPolynomial (LtN Dw n) c.F) (F : (Fin n → Fin g → ℂ) → ℂ), AnalyticOnNhd ℂ F Set.univ → I2.polyDeriv (MvPolynomial.rename eL (MvPolynomial.map s (pushLet c h P))) (letterDir X hr idx) F 0 = I2.polyDeriv (MvPolynomial.rename eL (MvPolynomial.map s P)) (letterDir X hr idx) (fun z => F (Dict.hAct X idx h z)) 0 := by
  intro E _ _ _ H Dw l c s r g X idx e q0 n hr eL hdir htype h P F hF
  have hF' : ContDiff ℂ (⊤ : ℕ∞) F := hF.contDiff
  let a : Harm.Var X.Ψ q0 X.p0 (Fin n) → Fin n → ℂ := fun v k =>
    s (Formalism.L2.Pj.embF c (eL.symm v).1 (h k (eL.symm v).2.2))
  let j : Harm.Var X.Ψ q0 X.p0 (Fin n) → Fin n → Harm.Var X.Ψ q0 X.p0 (Fin n) := fun v k =>
    eL ⟨(eL.symm v).1, (eL.symm v).2.1, k⟩
  let Φ : MvPolynomial (Harm.Var X.Ψ q0 X.p0 (Fin n)) ℂ →ₐ[ℂ] MvPolynomial (Harm.Var X.Ψ q0 X.p0 (Fin n)) ℂ :=
    MvPolynomial.aeval fun v => ∑ k, MvPolynomial.C (a v k) * MvPolynomial.X (j v k)
  have ha : ∀ v k, a (eL v) k = s (Formalism.L2.Pj.embF c v.1 (h k v.2.2)) := fun v k => by
    simp only [a]; rw [Equiv.symm_apply_apply]
  have hj : ∀ v k, j (eL v) k = eL ⟨v.1, v.2.1, k⟩ := fun v k => by
    simp only [j]; rw [Equiv.symm_apply_apply]
  have hΦ : ∀ Q : MvPolynomial (LtN Dw n) c.F,
      MvPolynomial.rename eL (MvPolynomial.map s (pushLet c h Q)) =
        Φ (MvPolynomial.rename eL (MvPolynomial.map s Q)) := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C x => simp
    | add P Q hP hQ => simp only [map_add, hP, hQ]
    | mul_X P v hP =>
      simp only [map_mul, hP]
      congr 1
      simp [pushLet, letB, Φ, ha, hj]
  rw [hΦ, ColPoly.polyDeriv_subst hF' a j Φ (fun v => by simp [Φ])]
  refine Eq.symm ((polyDeriv_comp_linear hF' (hActL X idx h) _ _ 0).trans ?_)
  rw [map_zero]
  congr 1
  funext v k i
  obtain ⟨⟨τ, ρ, b⟩, rfl⟩ := eL.surjective v
  change Dict.hAct X idx h _ k i = _
  simp only [Dict.hAct, ha, hj, hdir, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single b (fun l _ hl => by simp [hl]) (by simp),
    Finset.sum_eq_single k (fun l _ hl => by simp [hl.symm]) (by simp)]
  by_cases hi : i = e.symm ⟨τ, ρ⟩
  · subst hi
    simp only [htype, Equiv.apply_symm_apply, Pi.single_eq_same]
    rfl
  · simp [hi]
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyDeriv_letter_pushforward_eq_column_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l), ∀ (s : c.F →+* ℂ) (r g : ℕ) (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (q0 n : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → (∀ j, rowType X (idx j) = relab c s (e j).1) → ∀ (h : Matrix (Fin n) (Fin n) E) (P : MvPolynomial (LtN Dw n) c.F) (F : (Fin n → Fin g → ℂ) → ℂ), AnalyticOnNhd ℂ F Set.univ → I2.polyDeriv (MvPolynomial.rename eL (MvPolynomial.map s (pushLet c h P))) (letterDir X hr idx) F 0 = I2.polyDeriv (MvPolynomial.rename eL (MvPolynomial.map s P)) (letterDir X hr idx) (fun z => F (Dict.hAct X idx h z)) 0 := by
  atlas_forward_decl GlobalTheory.Phase.polyDeriv_pushLet_eq_hAct
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pushforward_preserves_harmonic_polynomials_and_lattices : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l), ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (h : Matrix (Fin n) (Fin n) E), IsUnitaryM h → (∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), pushLet c h P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) ∧ ∀ Λ : GenLat E n, (Λ.Unimod → (actLat h Λ).Unimod) ∧ Moves h Λ.La (actLat h Λ).La ∧ ccT h * h = 1 ∧ ∀ P ∈ harmL (Dw := Dw) c Λ a, pushLet c h P ∈ harmL (Dw := Dw) c (actLat h Λ) a := by
  first | exact @GlobalTheory.PushKeeps.push_keeps | exact GlobalTheory.PushKeeps.push_keeps | (intros; apply GlobalTheory.PushKeeps.push_keeps <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.Phase.ChangePt

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem cmHost_idempotent_trace_eq_one (H : Host E) : (H.w0 : E) + cc (H.w0 : E) = 1 := by
  have h2 : 2 * (H.w0 : E) = 1 + (H.rt : E) := by
    simpa [map_ofNat] using congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
  have hs : (H.rt : E) ^ 2 = -(H.d : E) := by
    simpa using congrArg (algebraMap (𝓞 E) E) H.rt_sq
  have hc : cc (H.rt : E) = -(H.rt : E) := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by rw [← map_pow, hs]; simp
    have hre : (τ (H.rt : E)).re = 0 := by
      have a1 := congrArg Complex.re h1
      have a2 := congrArg Complex.im h1
      simp [pow_two] at a1 a2
      have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      by_contra hne
      have : (τ (H.rt : E)).im = 0 := by
        have : (τ (H.rt : E)).re * (τ (H.rt : E)).im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at a1
      nlinarith [mul_self_nonneg (τ (H.rt : E)).re]
    rw [cc, IsCMField.complexEmbedding_complexConj, map_neg]
    apply Complex.ext <;> simp [hre]
  have h3 : 2 * cc (H.w0 : E) = 1 + cc (H.rt : E) := by
    have := congrArg (IsCMField.complexConj E) h2
    simpa [cc, map_ofNat] using this
  have : 2 * ((H.w0 : E) + cc (H.w0 : E)) = 2 * 1 := by linear_combination h2 + h3 + hc
  exact mul_left_cancel₀ two_ne_zero this

theorem finite_levQ {H : Host E} (Dw : Datum H) (l : Geo.Tor.Level H) : Finite (LevQ Dw l) := by
  have hM : l.Mb ≠ ⊥ := by
    intro h
    have h₁ := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h₁
    have h₂ : l.M = 0 := by exact_mod_cast h₁
    have := l.three_le
    omega
  have := l.Mb.finiteQuotientOfFreeOfNeBot hM
  have := Dw.fin
  exact Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem mem_vset (Λ : GenLat E n) {M : ℕ} (hM : 3 ≤ M) (hU : Λ.Unimod) (hT : Λ.TrivAt M) :
    Λ.La ∈ Vset E n M := by
  obtain ⟨k, hk, h1, h2⟩ := hT
  rw [GenLatCmp.std_eq, GenLatCmp.span_smul_le] at h1 h2
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [Nat.coprime_zero_left] at hk
      omega
    · exact hk0
  exact ⟨GenLatCmp.fg_of_smul_le hk0 h1, (GenLatCmp.unimod_iff Λ.La).1 hU, k, hk0, hk, h1, h2⟩

theorem thA_sum (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {T : Type} (s : Finset T) (f : T → TF n g) (hf : ∀ i, IsSB (f i)) :
    thA X bas idx (∑ i ∈ s, f i) x = ∑ i ∈ s, thA X bas idx (f i) x := by
  induction s using Finset.induction_on with
  | empty => simpa using UnAct.thA_smul (X := X) (bas := bas) idx x 0 (0 : TF n g)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    exact UnAct.thA_add idx hs hx (hf a) (RecSum.isSB_sum s f hf)

theorem theta_sum₂ (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {T : Type} (s : Finset T) (W : T → ℂ) (f : T → TF n g) (hf : ∀ i, IsSB (f i))
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) :
    thP X hr bas idx (∑ i ∈ s, W i • f i) P x = ∑ i ∈ s, W i * thP X hr bas idx (f i) P x := by
  unfold thP
  rw [← Jet.polyDeriv_sum_fun P _ s W _ fun i _ => ThetaHol.differentiable_thA idx hs (hf i) hx,
    thA_sum idx hs hx s _ fun i => TensVac.sb_smul _ (hf i)]
  congr 1
  funext z
  simp only [Finset.sum_apply, UnAct.thA_smul, Pi.smul_apply, smul_eq_mul]

theorem theta_finsum (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) {T : Type} [Fintype T] (W : T → ℂ)
    (Y : T → Matrix (Fin n) (Fin r) E) (a : ℂ) {u : TF n g} (hu : IsSB u)
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) :
    thP X hr bas idx (∑ᶠ q, W q • heisG X bas (Y q) (a • u)) P x =
      a * ∑ q, W q * thP X hr bas idx (heisG X bas (Y q) u) P x := by
  have h1 (q) : W q • heisG X bas (Y q) (a • u) = (a * W q) • heisG X bas (Y q) u := by
    funext t
    simp only [heisG, heisS, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [h1]
  rw [finsum_eq_sum_of_fintype, theta_sum₂ hr idx hs hx _ _ _
    fun q => ((heisG_laws E r X g bas idx n hs hn).2.2.2 (Y q) u hu).1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => _root_.mul_assoc _ _ _

omit [IsCMField E] in

theorem index_Ln (Λ : GenLat E n) :
    (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index =
      (stdL E n).toAddSubgroup.relIndex Λ.La.toAddSubgroup := by
  rw [← GenLatCmp.std_eq, ← AddSubgroup.inf_relIndex_left]
  rfl

omit [IsCMField E] in

theorem zCard_eq (Λ : GenLat E n) {N M : ℕ} (hN : Λ.LevOK N M) (r : ℕ) :
    Λ.zCard N r = Λ.mIdx N r * ((stdL E n).toAddSubgroup.relIndex Λ.La.toAddSubgroup) ^ r := by
  rw [← index_Ln Λ, GenLat.zCard, GenLat.mIdx, ← mul_pow]
  congr 1
  exact (AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono hN.2.2)
    (Submodule.toAddSubgroup_mono (inf_le_left : Λ.Ln ≤ Λ.La))).symm

end Classical

theorem cancel_idx {b κ S Q : ℂ} {m z j : ℕ} (hb : b ≠ 0) (hz0 : 0 < z) (hz : z = m * j) :
    b⁻¹ * (m : ℂ)⁻¹ * Q * (z : ℂ) * κ * ((((Real.sqrt (j : ℝ) : ℝ) : ℂ))⁻¹ * S) * b =
      Q * κ * S * ((Real.sqrt (j : ℝ) : ℝ) : ℂ) := by
  subst hz
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mul_pos_right hz0).ne'
  have hj : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_mul_pos_left hz0
  have hs : ((Real.sqrt (j : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hj).ne'
  have h2 : (j : ℂ) = ((Real.sqrt (j : ℝ) : ℝ) : ℂ) * ((Real.sqrt (j : ℝ) : ℝ) : ℂ) := by
    exact_mod_cast (Real.mul_self_sqrt hj.le).symm
  rw [Nat.cast_mul]
  generalize ((Real.sqrt (j : ℝ) : ℝ) : ℂ) = s at hs h2
  rw [h2]
  field_simp

theorem change_at_point : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (q0 n : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), IsSympl X bas → r = Dw.p + Dw.q → Even n → (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → (∀ j, rowType X (idx j) = Formalism.L2.PjFree.relab c (algebraMap c.F ℂ) (e j).1) → ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (Λ : GenLat E n) (h : Matrix (Fin n) (Fin n) E), Λ.Unimod → IsUnitaryM h → Λ.TrivAt l.M → (actLat h Λ).TrivAt l.M → ∃ t : ℂ, ‖t‖ = 1 ∧ ∀ (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (_ : AnFib X bas idx e x L y), x ∈ X.dom → SelfD X L → IsMu (t ^ 2 * ∏ τ : E →+* ℂ, algebraMap c.F ℂ (embF c τ h.det) ^ Dw.mult τ) ∧ ∀ (wq : (Fin n → LevQ Dw l) → c.F), FixesDatum c h wq → ∀ N N' : ℕ, Λ.LevOK N l.M → (actLat h Λ).LevOK N' l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ), ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ (b b' : c.F) (v v' : ℂ), b ≠ 0 → b' ≠ 0 → ShortValAt Xo c nab wq Λ b N P y v → ShortValAt Xo c nab wq (actLat h Λ) b' N' (pushLet c h P) y v' → v' * algebraMap c.F ℂ b' * (Real.sqrt (((Λ).Ln.toAddSubgroup.addSubgroupOf (Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : ℝ) = t * algebraMap c.F ℂ b * (Real.sqrt (((actLat h Λ).Ln.toAddSubgroup.addSubgroupOf (actLat h Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : ℝ) * v := by
  intro hci E _ _ _ H Dw l Xo c _ r g X bas idx e q0 n hr eL hs hrr hn hdir hty _ nab hnab Λ h hU hh hT hT'
  have hw := cmHost_idempotent_trace_eq_one H
  have hwi : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  obtain ⟨hU', hmv, hu, -⟩ := (GlobalTheory.T.pushforward_preserves_harmonic_polynomials_and_lattices E H Dw l c n 0 h hh).2 Λ
  have hΛ := mem_vset Λ l.three_le hU hT
  have hΛ' := mem_vset (actLat h Λ) l.three_le (hU' hU) hT'
  have hΛ1 : Λ.La ∈ Vset E n 1 := (GenLatCmp.genLat_vset E n _).2.2.1 1 _ (one_dvd _) hΛ
  have hΛ1' : (actLat h Λ).La ∈ Vset E n 1 := (GenLatCmp.genLat_vset E n _).2.2.1 1 _ (one_dvd _) hΛ'
  obtain ⟨t, ht, hvac⟩ := thA_vacuum_hAct E r X g bas idx n hs hn _ hwi hw h hu _ hΛ1 _ hΛ1' hmv
  refine ⟨t, ht, fun x L y A hx hL => ?_⟩
  obtain ⟨⟨v₀, hv₀⟩, -⟩ := TensVac.vacua E r X g bas idx n hs hn _ hwi hw L hL 1 _ (Base.stdL_mem_Vset n 1)
  have hcol := hvac L hL v₀ hv₀ x hx
  refine ⟨?_, ?_⟩
  · have h1 := GlobalTheory.T.multiplier_sq_mul_det_unitary_column_change E r X g bas idx n hs hn _ hwi hw h hu _ hΛ1 _ hΛ1' L hL v₀ hv₀ x hx t ht hcol
    have h2 : ∏ i : Fin g, rowType X (idx i) h.det =
        ∏ τ : E →+* ℂ, algebraMap c.F ℂ (embF c τ h.det) ^ Dw.mult τ := by
      simp only [hty]
      rw [e.prod_comp (fun ℓ : Lt1 Dw => Formalism.L2.PjFree.relab c (algebraMap c.F ℂ) ℓ.1 h.det), Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun τ _ => ?_
      simp [Formalism.L2.PjFree.relab]
    rwa [h2] at h1
  intro wq hwq N N' hN hN' a P hP b b' v v' hb hb' hv hv'
  obtain ⟨θ, hθ, -⟩ := (reads_existsUnique_theta E H Dw l Xo c r g X bas idx e x L y A hs hx hL 1 y.s).1
  have hθ1 := isTheta1_of_reads_generator E H Dw l Xo c r g X bas idx e x L y A hs hx hL θ hθ
  obtain ⟨κ, hκ⟩ := VacProd.prod_eq_mul_thA E r X g bas idx n hs hn _ hwi hw L hL v₀ hv₀ x hx θ hθ1
  obtain ⟨mk, hmk, hA⟩ := exists_mark E H Dw l Xo c r g X bas idx e x L y A hs hx hL
  have hroots := (DualMark.dual_marking E H Dw l r X L mk _ hL hmk
    (Complex.isPrimitiveRoot_exp _ l.odd.pos.ne')).2.2.2.2 n
  obtain ⟨Y, hY⟩ := hroots N hN.1.pos
  obtain ⟨Y', hY'⟩ := hroots N' hN'.1.pos
  have e1 := GlobalTheory.T.shortThetaValue_complexPoint_eq_classicalTheta hci E H Dw l Xo c r g X bas idx e x L y A hs hx hL q0 n hr eL hrr hn hdir nab hnab
    θ v₀ κ hθ hv₀ hκ mk hmk hA Λ.La hΛ N hN Y hY a P hP wq b v hv
  have e2 := GlobalTheory.T.shortThetaValue_complexPoint_eq_classicalTheta hci E H Dw l Xo c r g X bas idx e x L y A hs hx hL q0 n hr eL hrr hn hdir nab hnab
    θ v₀ κ hθ hv₀ hκ mk hmk hA (actLat h Λ).La hΛ' N' hN' Y' hY' a _
    ((GlobalTheory.T.pushforward_preserves_harmonic_polynomials_and_lattices E H Dw l c n a h hh).1 P hP) wq b' v' hv'
  obtain ⟨_, -, hproj⟩ := GlobalTheory.T.heisenbergVacuum_projection_rootOfUnity_phases E r X g bas idx n hs hn _ hwi hw L hL v₀ hv₀
  obtain ⟨hu1, -, hp1⟩ := hproj _ hΛ1
  obtain ⟨hu2, -, hp2⟩ := hproj _ hΛ1'
  obtain ⟨⟨σ, hσ⟩, hmove⟩ := GlobalTheory.T.roots_levelPoints_same_vacuum_translates E H Dw l r X g bas n hs hn L hL mk hmk h hu _ hΛ _ hΛ' hmv N N' hN hN'
    Y Y' hY hY'
  obtain ⟨-, -, -, hz1, -⟩ := ZLat.exists_reps_sum E r X g bas idx n hs hn _ hwi hw L hL _ hΛ1 N hN.1
    (hN.2.2.trans inf_le_left)
  obtain ⟨-, -, -, hz2, -⟩ := ZLat.exists_reps_sum E r X g bas idx n hs hn _ hwi hw L hL _ hΛ1' N' hN'.1
    (hN'.2.2.trans inf_le_left)
  haveI := finite_levQ Dw l
  haveI := Fintype.ofFinite (Fin n → LevQ Dw l)
  generalize unitv (projA X bas (H.w0 : E) (tens Λ.La L) v₀) = u at hcol hu1 hp1
  generalize unitv (projA X bas (H.w0 : E) (tens (actLat h Λ).La L) v₀) = u' at hcol hu2 hp2
  rw [gphi, hp1, theta_finsum hr idx hs hn hx _ _ _ hu1.1] at e1
  rw [gphi, hp2, theta_finsum hr idx hs hn hx _ _ _ hu2.1] at e2
  have hsum : ∑ q, algebraMap c.F ℂ (wq q) * thP X hr bas idx (heisG X bas (Y' q) u')
        (MvPolynomial.rename eL (MvPolynomial.map (algebraMap c.F ℂ) (pushLet c h P))) x =
      t * ∑ q, algebraMap c.F ℂ (wq q) * thP X hr bas idx (heisG X bas (Y q) u)
        (MvPolynomial.rename eL (MvPolynomial.map (algebraMap c.F ℂ) P)) x := by
    rw [← σ.sum_comp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hsb := ((heisG_laws E r X g bas idx n hs hn).2.2.2 (Y q) u hu1.1).1
    have hsb' := ((heisG_laws E r X g bas idx n hs hn).2.2.2 (h * Y q) u' hu2.1).1
    have han := (theta_holomorphic_weight E r X g q0 hr bas idx n hs hn 0 0 _ hsb' 0 (zero_mem _)).2.2.2 x hx
    rw [hwq q _ (hσ q), hmove q _ (hσ q) u' hu2, thP, thP,
      GlobalTheory.T.polyDeriv_letter_pushforward_eq_column_action E H Dw l c _ r g X idx e q0 n hr eL hdir hty h P _ han,
      funext (thA_heisG_hAct E r X g bas idx n hs hn h hu u u' hu1.1 hu2.1 t x hx hcol (Y q)),
      mul_left_comm t, ← Jet.polyDeriv_smul_fun _ _ (ThetaHol.differentiable_thA idx hs hsb hx)]
    rfl
  rw [hsum] at e2
  simp only [map_mul, map_inv₀, map_natCast] at e1 e2
  have hb0 : algebraMap c.F ℂ b ≠ 0 := (map_ne_zero _).2 hb
  have hb0' : algebraMap c.F ℂ b' ≠ 0 := (map_ne_zero _).2 hb'
  rw [index_Ln, index_Ln, ← hrr, e2, cancel_idx hb0' hz2 (zCard_eq _ hN' r), mul_right_comm _ _ v,
    _root_.mul_assoc t, _root_.mul_comm _ v, e1, cancel_idx hb0 hz1 (zCard_eq _ hN r)]
  ring

end GlobalTheory.Phase.ChangePt
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.NaturalValues

theorem eq_of_points {K R Ω : Type} [Field K] [CommRing R] [Algebra K R] [IsReduced R] [Algebra.FiniteType K R]
    [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] {x y : R} (h : ∀ φ : R →ₐ[K] Ω, φ x = φ y) : x = y := by
  haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)
  rw [← sub_eq_zero]
  have hb : (⊥ : Ideal R).jacobson = ⊥ :=
    IsJacobsonRing.out inferInstance ((Ideal.isRadical_iff_quotient_reduced _).2
      (isReduced_of_injective (RingEquiv.quotientBot R) (RingEquiv.quotientBot R).injective))
  rw [← Ideal.mem_bot, ← hb]
  refine Ideal.mem_sInf.2 fun {m} hm => ?_
  haveI := hm.2
  letI := Ideal.Quotient.field m
  haveI : Module.Finite K (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ m)
  let ψ : (R ⧸ m) →ₐ[K] Ω := IsAlgClosed.lift
  have e := h (ψ.comp (Ideal.Quotient.mkₐ K m))
  rw [← sub_eq_zero, ← map_sub, AlgHom.comp_apply, map_eq_zero] at e
  exact Ideal.Quotient.eq_zero_iff_mem.1 e

theorem eq_of_eq_complex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (s : c.F →+* ℂ) (u u' : ∀ (S : Type) [CommRing S] [Algebra c.F S], FrPt Xo c S → S), (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → φ (u S y) = u T z) → (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → φ (u' S y) = u' T z) → (∀ y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra, @u ℂ _ s.toAlgebra y = @u' ℂ _ s.toAlgebra y) → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), u S y = u' S y := by
  intro E _ _ _ H Dw l Xo c s u u' hu hu' hc S _ _ y
  have hF := GlobalTheory.RepCompare.frameLaws Xo c
  letI := s.toAlgebra
  refine eq_of_locM (K := c.F) fun m hm => ?_
  obtain ⟨A, v, cw, -, -, -, ⟨wm, h1, h2⟩, -⟩ := hF.cover S y y rfl m
  have e : u A.R v = u' A.R v := by
    refine eq_of_points (K := c.F) (Ω := ℂ) fun φ => ?_
    obtain ⟨z, hz⟩ := hF.bc _ _ φ v
    rw [hu _ _ φ v z hz, hu' _ _ φ v z hz]
    exact hc z
  rw [hu _ _ _ y wm h1, hu' _ _ _ y wm h1, ← hu _ _ cw v wm h2, ← hu' _ _ cw v wm h2, e]

end GlobalTheory.NaturalValues
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.ConstRatio

theorem ratio_mem_range {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (T : Type) [Field T] [IsAlgClosed T] [Algebra c.F T]
    (u u' : FrPt Xo c T → T)
    (hu : ∀ (φ : T →ₐ[c.F] T) (y z : FrPt Xo c T), FrMap φ y z → φ (u y) = u z)
    (hu' : ∀ (φ : T →ₐ[c.F] T) (y z : FrPt Xo c T), FrMap φ y z → φ (u' y) = u' z)
    (z : T) (h : ∀ y, u' y = z * u y) (y : FrPt Xo c T) (hy : u y ≠ 0) :
    z ∈ Set.range (algebraMap c.F T) := by
  refine GlobalTheory.GaloisDescent.mem_range_algebraMap_of_forall_algEquiv z fun σ => ?_
  obtain ⟨y', hy'⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c T T σ.toAlgHom y
  have h1 := hu _ _ _ hy'
  have h2 := hu' _ _ _ hy'
  rw [h y, h y', map_mul, ← h1] at h2
  have hne : σ.toAlgHom (u y) ≠ 0 := by
    simpa using hy
  exact mul_right_cancel₀ hne h2

theorem exists_ratio : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (s : c.F →+* ℂ) (J : Type) (u u' : J → ∀ (S : Type) [CommRing S] [Algebra c.F S], FrPt Xo c S → S), (∀ j, (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → φ (u j S y) = u j T z)) → (∀ j, (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → φ (u' j S y) = u' j T z)) → ∀ z : ℂ, IsMu z → (∀ j (y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra), @u' j ℂ _ s.toAlgebra y = z * @u j ℂ _ s.toAlgebra y) → ∃ z₀ : c.F, (∃ k : ℕ, 0 < k ∧ z₀ ^ k = 1) ∧ ∀ j (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), u' j S y = algebraMap c.F S z₀ * u j S y := by
  intro E _ _ _ H Dw l Xo c s J u u' hu hu' z hz h
  have key : ∃ z₀ : c.F, (∃ k : ℕ, 0 < k ∧ z₀ ^ k = 1) ∧
      ∀ j (y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra),
        @u' j ℂ _ s.toAlgebra y = s z₀ * @u j ℂ _ s.toAlgebra y := by
    by_cases h0 : ∀ j (y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra), @u j ℂ _ s.toAlgebra y = 0
    · refine ⟨1, ⟨1, one_pos, one_pow 1⟩, fun j y => ?_⟩
      rw [h j y, h0 j y, mul_zero, mul_zero]
    · simp only [not_forall] at h0
      obtain ⟨j, y, hy⟩ := h0
      obtain ⟨z₀, hz₀⟩ := @ratio_mem_range E _ _ _ H Dw l Xo c ℂ _ _ s.toAlgebra
        (@u j ℂ _ s.toAlgebra) (@u' j ℂ _ s.toAlgebra)
        (@hu j ℂ ℂ _ s.toAlgebra _ s.toAlgebra) (@hu' j ℂ ℂ _ s.toAlgebra _ s.toAlgebra) z (h j) y hy
      have hz₀' : s z₀ = z := hz₀
      obtain ⟨m, hm, hzm⟩ := hz
      refine ⟨z₀, ⟨m, hm, s.injective ?_⟩, fun j y => ?_⟩
      · rw [map_pow, hz₀', hzm, map_one]
      · rw [hz₀', h j y]
  obtain ⟨z₀, hk, hz₀⟩ := key
  refine ⟨z₀, hk, fun j => ?_⟩
  refine GlobalTheory.NaturalValues.eq_of_eq_complex E H Dw l Xo c s (u' j) (fun S _ _ y => algebraMap c.F S z₀ * u j S y) (hu' j) ?_ ?_
  · intro S T _ _ _ _ φ y y' hyy
    rw [map_mul, φ.commutes, hu j S T φ y y' hyy]
  · intro y
    exact hz₀ j y

end GlobalTheory.ConstRatio
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory

theorem changeRoot_scalar_isMu (t b b' D : ℂ) (A A' m : ℕ) (hb' : b' ≠ 0) (hA : A ≠ 0) (hm : 0 < m)
    (h1 : (b ^ 2 * (A' : ℂ)) ^ m = (b' ^ 2 * (A : ℂ) * D) ^ m) (h2 : IsMu (t ^ 2 * D)) :
    IsMu (t * b * ((Real.sqrt (A' : ℝ) : ℝ) : ℂ) / (b' * ((Real.sqrt (A : ℝ) : ℝ) : ℂ))) := by
  obtain ⟨k, hk, h2⟩ := h2
  have e : ∀ B : ℕ, ((Real.sqrt (B : ℝ) : ℝ) : ℂ) ^ 2 = (B : ℂ) := fun B => by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg B)]; simp
  have hA' : (A : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hA
  refine ⟨2 * m * k, by positivity, ?_⟩
  have e2 : (t * b * ((Real.sqrt (A' : ℝ) : ℝ) : ℂ) / (b' * ((Real.sqrt (A : ℝ) : ℝ) : ℂ))) ^ 2 =
      t ^ 2 * (b ^ 2 * (A' : ℂ)) / (b' ^ 2 * (A : ℂ)) := by
    rw [div_pow, mul_pow, mul_pow, mul_pow, e, e, _root_.mul_assoc]
  have hne : (b' ^ 2 * (A : ℂ)) ^ m ≠ 0 := pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hb') hA')
  have e3 : (t ^ 2 * (b ^ 2 * (A' : ℂ)) / (b' ^ 2 * (A : ℂ))) ^ m = (t ^ 2 * D) ^ m := by
    rw [div_pow, mul_pow (t ^ 2), h1, mul_pow _ D, div_eq_iff hne, mul_pow (t ^ 2) D]; ring
  rw [pow_mul, pow_mul, e2, e3, ← pow_mul, mul_comm m k, pow_mul, h2, one_pow]

theorem changeRoot_complex (hC : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ]
    [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab) (n : ℕ) (hn : Even n)
    (hfib : ∃ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)
      (e : Fin g ≃ Lt1 Dw) (hr : X.p0 + Dw.p = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ Dw.p X.p0 (Fin n)),
      IsSympl X bas ∧ r = Dw.p + Dw.q ∧
      (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) ∧
      (∀ j, rowType X (idx j) = Formalism.L2.PjFree.relab c (algebraMap c.F ℂ) (e j).1) ∧
      ∀ y : FrPt Xo c ℂ, ∃ (y₀ : FrPt Xo c ℂ) (t : Ix Dw → ℂˣ) (x : Frame X.Ψ r) (L : Lt E r),
        FrBor t y₀ y ∧ x ∈ X.dom ∧ SelfD X L ∧ Nonempty (AnFib X bas idx e x L y₀))
    (Λ : GenLat E n) (h : Matrix (Fin n) (Fin n) E) (b b' : c.F) (hU : Λ.Unimod) (hh : IsUnitaryM h)
    (hT : Λ.TrivAt l.M) (hT' : (actLat h Λ).TrivAt l.M) (hb : IsBeta Dw c Λ b) (hb' : IsBeta Dw c (actLat h Λ) b') :
    ∃ z : ℂ, IsMu z ∧ ∀ (w : (Fin n → LevQ Dw l) → c.F), FixesDatum c h w →
      ∀ N N' : ℕ, Λ.LevOK N l.M → (actLat h Λ).LevOK N' l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ),
      ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)),
      ∀ (y : FrPt Xo c ℂ) (v v' : ℂ), ShortValAt Xo c nab w Λ b N P y v →
        ShortValAt Xo c nab w (actLat h Λ) b' N' (pushLet c h P) y v' → v' = z * v := by
  obtain ⟨r, g, X, bas, idx, e, hr, eL, hS, hr', hL, hrow, hy⟩ := hfib
  by_cases hne : Nonempty (FrPt Xo c ℂ)
  swap
  · exact ⟨1, isMu_one, fun _ _ _ _ _ _ _ _ _ y => (hne ⟨y⟩).elim⟩
  obtain ⟨y1⟩ := hne
  have hLaws : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨t, -, ht⟩ := GlobalTheory.Phase.ChangePt.change_at_point hC E H Dw l Xo c r g X bas idx e Dw.p n hr eL hS hr' hn hL hrow nab hnab
    Λ h hU hh hT hT'
  obtain ⟨m, hm, hbeta⟩ := GlobalTheory.BetaChange.beta_sq_compare E H Dw l c n Λ h b b' hU hh hb hb'
  obtain ⟨hP, hΛ⟩ : _ ∧ _ := ⟨fun a => (GlobalTheory.PushKeeps.push_keeps E H Dw l c n a h hh).1,
    ((GlobalTheory.PushKeeps.push_keeps E H Dw l c n 0 h hh).2 Λ).1 hU⟩
  set A := ((Λ).Ln.toAddSubgroup.addSubgroupOf (Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) with hAdef
  set A' := ((actLat h Λ).Ln.toAddSubgroup.addSubgroupOf (actLat h Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q)
    with hA'def
  have hb0 : algebraMap c.F ℂ b ≠ 0 := (map_ne_zero _).2 hb.1
  have hb0' : algebraMap c.F ℂ b' ≠ 0 := (map_ne_zero _).2 hb'.1
  have hA : A ≠ 0 := by
    intro h0
    have h1 := hb.2.2 (algebraMap c.F ℂ)
    rw [← Nat.cast_pow, ← hAdef, h0, Nat.cast_zero, pow_eq_zero_iff two_ne_zero, norm_eq_zero] at h1
    exact hb0 h1
  have hsq : ((Real.sqrt (A : ℝ) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hA))).ne'
  obtain ⟨y₀, t₀, x, L, -, hx, hSD, ⟨F⟩⟩ := hy y1
  have hmu := (ht x L y₀ F hx hSD).1
  have hbeta' := congrArg (algebraMap c.F ℂ) hbeta
  simp only [map_pow, map_mul, map_natCast, map_prod] at hbeta'
  refine ⟨_, changeRoot_scalar_isMu t _ _ _ A A' m hb0' hA hm hbeta' hmu, ?_⟩
  intro w hw N N' hN hN' a P hPa y v v' hv hv'
  obtain ⟨y₀, t₀, x, L, hB, hx, hSD, ⟨F⟩⟩ := hy y
  have ex1 := (GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n Λ N hU hT hN a P hPa w b).1 ℂ
  have ex2 := (GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n (actLat h Λ) N' hΛ hT' hN' a _ (hP a P hPa) w b').1 ℂ
  obtain ⟨u, hu, -⟩ := ex1 y₀
  obtain ⟨u', hu', -⟩ := ex2 y₀
  have k1 := (ex1 y).unique hv
    ((GlobalTheory.thetaValue_weight hLaws hC E H Dw l Xo c nab hnab ℂ y₀ y t₀ hB n a P).2 hPa w Λ b N u hu)
  have k2 := (ex2 y).unique hv'
    ((GlobalTheory.thetaValue_weight hLaws hC E H Dw l Xo c nab hnab ℂ y₀ y t₀ hB n a _).2 (hP a P hPa) w _ b' N' u' hu')
  have k3 := (ht x L y₀ F hx hSD).2 w hw N N' hN hN' a P hPa b b' u u' hb.1 hb'.1 hu hu'
  have k4 : u' = t * algebraMap c.F ℂ b * ((Real.sqrt (A' : ℝ) : ℝ) : ℂ) /
      (algebraMap c.F ℂ b' * ((Real.sqrt (A : ℝ) : ℝ) : ℂ)) * u := by
    rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hb0' hsq), ← _root_.mul_assoc]
    exact k3
  rw [k1, k2, k4]; ring

theorem changeRoot_of_chartIndep : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c) (n : ℕ), ChangeRoot Xo c nab n := by
  intro hC E _ _ _ H Dw l Xo c _ nab n hs bad hbad Λ h b b' hU hh hT hT' hb hb'
  obtain ⟨-, hodd, hn, hnab⟩ := hs
  have hLaws : Out.Laws := GlobalTheory.firstFiveLaws.1
  have triv : ∀ Λ : GenLat E n, Λ.TrivAt bad → Λ.TrivAt l.M := fun Λ ⟨k, hk, h1⟩ =>
    ⟨k, hk.coprime_dvd_right hbad.2.2.1, h1⟩
  have hT := triv _ hT
  have hT' := triv _ hT'
  obtain ⟨s, hfib⟩ := GlobalTheory.Dict.exists_anFib_all_points E H Dw l Xo c hodd.pos n hn
  obtain ⟨z, hz, hid⟩ := @changeRoot_complex hC E _ _ _ H Dw l Xo c s.toAlgebra _ nab hnab n hn hfib
    Λ h b b' hU hh hT hT' hb hb'
  have hP := fun a => (GlobalTheory.PushKeeps.push_keeps E H Dw l c n a h hh).1
  have hΛ := ((GlobalTheory.PushKeeps.push_keeps E H Dw l c n 0 h hh).2 Λ).1 hU
  let J : Type := {p : ((Fin n → LevQ Dw l) → c.F) × ℕ × ℕ × ((E →+* ℂ) × ℕ → ℕ) × MvPolynomial (LtN Dw n) c.F //
    FixesDatum c h p.1 ∧ Λ.LevOK p.2.1 l.M ∧ (actLat h Λ).LevOK p.2.2.1 l.M ∧
      p.2.2.2.2 ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => p.2.2.2.1 (τ, i))}
  have ex1 := fun j : J => GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n Λ j.1.2.1 hU hT j.2.2.1 j.1.2.2.2.1
    j.1.2.2.2.2 j.2.2.2.2 j.1.1 b
  have ex2 := fun j : J => GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n (actLat h Λ) j.1.2.2.1 hΛ hT' j.2.2.2.1
    j.1.2.2.2.1 _ (hP _ _ j.2.2.2.2) j.1.1 b'
  choose u hu using fun (j : J) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) => ((ex1 j).1 S y).exists
  choose u' hu' using fun (j : J) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) => ((ex2 j).1 S y).exists
  obtain ⟨z₀, hz₀, hfin⟩ := GlobalTheory.ConstRatio.exists_ratio E H Dw l Xo c s J u u'
    (fun j S T _ _ _ _ φ y y' hy => (ex1 j).2 S T φ y y' hy _ _ (hu j S y) (hu j T y'))
    (fun j S T _ _ _ _ φ y y' hy => (ex2 j).2 S T φ y y' hy _ _ (hu' j S y) (hu' j T y')) z hz
    (fun j y => hid j.1.1 j.2.1 _ _ j.2.2.1 j.2.2.2.1 _ _ j.2.2.2.2 y _ _
      (@hu j ℂ _ s.toAlgebra y) (@hu' j ℂ _ s.toAlgebra y))
  refine ⟨z₀, hz₀, ?_⟩
  intro w hw N N' hN hN' a P hPa S _ _ y v v' hv hv'
  let j : J := ⟨(w, N, N', a, P), hw, hN, hN', hPa.1⟩
  rw [((ex1 j).1 S y).unique hv (hu j S y), ((ex2 j).1 S y).unique hv' (hu' j S y)]
  exact hfin j S y

end GlobalTheory
end
