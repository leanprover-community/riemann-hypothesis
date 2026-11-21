import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.DictKAOfParts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PureFiniteAdelicTestFunctionContinuousCompact
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.LeftInvOfIsSection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilSchrodingerRealParameter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCell
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentMapContinuousAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHalfTr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainFourierUnfoldingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCellInvariantUnipotentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellCosetsHermitianParamStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorizationStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.RationalHermitianCountable.CountableRatHerm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftInvSubtypeSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralContinuous
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperateMultiplierPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacOfMemSchwartzA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralCompChar
import GroundTheory.LocalFields.CompleteTrivialLocal

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.HandIAdd

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS

section SlopeTestRemainingChoices

open NumberField IsDedekindDomain
open PI.VolStabS.PositiveNearLattice PI.VolStabS.AdmissibleCompactSupport GlobalTheory.GaugeEx GlobalTheory.PureFinite Set

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) {n M : ℕ}
  (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ)

theorem isLocallyConstant_finprod (hSB : ∀ v, IsSB (Φv v))
    (hae : ∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1) :
    IsLocallyConstant (fun X : Fin n → Fin M → Af F ⊗[F] E => ∏ᶠ v, Φv v (projV v X)) := by
  classical
  rw [IsLocallyConstant.iff_eventually_eq]
  intro X
  have hS := Filter.eventually_cofinite.1 (hae.and (eventually_mem_latV b X))
  let O : Set (Af F) := {x | ∀ v, x v ∈ v.adicCompletionIntegers F}
  have hOo : IsOpen O :=
    RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring _)
  let U : Set (Fin n → Fin M → Af F ⊗[F] E) := {Y | ∀ a i k, crd b (Af F) ((Y - X) a i) k ∈ O}
  have hUo : IsOpen U := by
    have e : U = ⋂ a, ⋂ i, ⋂ k, (fun Y : Fin n → Fin M → Af F ⊗[F] E =>
        crd b (Af F) ((Y - X) a i) k) ⁻¹' O := by
      ext Y; simp [U]
    rw [e]
    exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i =>
      isOpen_iInter_of_finite fun k => hOo.preimage ((continuous_crd b (Af F) k).comp
        ((continuous_apply i).comp ((continuous_apply a).comp (continuous_id.sub continuous_const))))
  have hXU : X ∈ U := by
    intro a i k v
    simp only [sub_self, crd, Pi.zero_apply, map_zero, Finsupp.zero_apply]
    exact zero_mem (v.adicCompletionIntegers F)
  have hfin : ∀ Y ∈ U, ∏ᶠ v, Φv v (projV v Y) = ∏ v ∈ hS.toFinset, Φv v (projV v Y) := by
    intro Y hY
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    rw [Set.Finite.coe_toFinset]
    intro h
    apply hv
    have hYX : projV v (Y - X) ∈ latV b v := by
      intro a i k
      have := crd_projV b (Y - X) v a i k
      simp only [crd] at this
      rw [this]
      exact hY a i k v
    have hmem : projV v Y ∈ latV b v := by
      have e : projV v Y = projV v (Y - X) + projV v X := by
        rw [← projV_add]; simp
      rw [e]
      exact latV_add b v hYX h.2
    show Φv v (projV v Y) = 1
    rw [h.1, Set.indicator_of_mem hmem]
    rfl
  have hloc : ∀ᶠ Y in nhds X, ∀ v ∈ hS.toFinset, Φv v (projV v Y) = Φv v (projV v X) :=
    (Filter.eventually_all_finset _).2 fun v _ =>
      ((hSB v).1.comp_continuous (continuous_projV_fin b v)).eventually_eq X
  filter_upwards [hUo.mem_nhds hXU, hloc] with Y hY hY'
  rw [hfin Y hY, hfin X hXU]
  exact Finset.prod_congr rfl hY'

theorem isSB_of_isPureFin (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
    (h : HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin b Φf Φv) : IsLocallyConstant Φf ∧ HasCompactSupport Φf := by
  obtain ⟨hSB, hae, hprod⟩ : IsPureFin b Φf Φv := h
  have e : Φf = fun X => ∏ᶠ v, Φv v (projV v X) := funext hprod
  subst e
  exact ⟨isLocallyConstant_finprod b Φv hSB hae, hasCompactSupport_finprod b Φv hSB hae⟩

def transpH (A : Type) [TopologicalSpace A] (r n : ℕ) : (Fin r → Fin n → A) ≃ₜ (Fin n → Fin r → A) where
  toFun X := fun i j => X j i
  invFun X := fun i j => X j i
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end SlopeTestRemainingChoices

theorem mem_SB_of_isPureFin {D : D7} {r n d : ℕ} (bs : Module.Basis (Fin d) D.host.F D.host.E)
    (g : (Fin r → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (gv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      (Fin n → Fin r → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E) → ℂ)
    (h : HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin bs (fun X => g fun i j => X j i) gv) :
    g ∈ GlobalTheory.WeilM.SB (Fin r → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := by
  haveI : FiniteDimensional D.host.F D.host.E := Module.Finite.of_basis bs
  obtain ⟨h1, h2⟩ := isSB_of_isPureFin bs gv _ h
  exact ⟨h1.comp_continuous (transpH _ r n).continuous, h2.comp_homeomorph (transpH _ r n)⟩

end PositivityTheory.PfSWUS.HandIAdd

end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.HandIAdd

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

section Unfolding

open GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.StdUnn.PolesModel GlobalTheory.StdUnn.HeightExists GlobalTheory.Eis
open GlobalTheory.CompanionTheory.SwUnf GlobalTheory.CompanionTheory.HermPoisson GlobalTheory.CompanionTheory.SiegelUnip
open PositivityTheory.PfSWUS.HUnfold (majorant countable_cosets countable_ratHerm sec_det_one)

theorem isSection_npow_height {D : D7} {n : ℕ} {H : G D n → ℝ≥0} (hH : IsHeight H) (s : ℂ) :
    IsSection 1 s (fun x => npow (H x) (s + (n : ℂ) / 2)) := by
  haveI := t2Space_adeleRing' (F := D.host.F)
  rw [height_eq hH]
  exact isSection_iff.2
    (isIwasawa.npow_iwAbs_mem HeightExists.isClosed_P continuous_modP HeightExists.isCompact_K _)

theorem stdSec_self {D : D7} {n : ℕ} (H : G D n → ℝ≥0) (φ : G D n → ℂ) (s : ℂ) : stdSec H φ s s = φ := by
  funext x
  simp [stdSec, npow]

theorem integrable_bigCell_spherical {D : D7} {n : ℕ} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    {H : G D n → ℝ≥0} (hH : IsHeight H) {nb : hermA D n → G D n} {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)}
    (hCD : CoefData nb lam 𝓖) {w : G D n} (hw : mat w = blk4 0 1 (-1) 0) (β : HermE D n) (hβ : β.1.det ≠ 0)
    {s : ℂ} (hs : (n : ℝ) / 2 < s.re) (g : G D n) :
    Integrable (fun b : hermA D n => npow (H (w * nb b * g)) (s + (n : ℂ) / 2)) lam := by
  obtain ⟨hnb, hHaar, hD, hD1⟩ := hCD
  let φ : G D n → ℂ := fun x => npow (H x) (s + (n : ℂ) / 2)
  have hsz : IsSection 1 s φ := isSection_npow_height hH s
  have hstd : stdSec H φ s s = φ := stdSec_self H φ s
  have hLI : LeftInv (P D n ⊓ GF D n) φ := leftInv_of_isSection ⟨continuous_const, fun _ => rfl⟩ hsz
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  haveI : SecondCountableTopology (Mx D n n) := i3
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : SecondCountableTopology (hermA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : ContinuousAdd (hermA D n) := ⟨Continuous.subtype_mk ((continuous_subtype_val.comp continuous_fst).add
    (continuous_subtype_val.comp continuous_snd)) _⟩
  haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
  haveI : MeasurableAdd (hermA D n) := ContinuousAdd.measurableAdd
  haveI := hHaar
  haveI := countable_ratHerm (D := D) (n := n)
  haveI := countable_cosets (D := D) (n := n)
  let F : Cosets (P D n) (GF D n) → hermA D n → ℂ := fun q b => term (P D n) (GF D n) φ (nb b * g) q
  let F0 : hermA D n → ℂ := fun b => φ (w * nb b * g)
  let ch : hermA D n → ℂ := chi ψ (-(β.1.map (incA D)))
  have hch : ∀ b, ch b = ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) :=
    fun b => chi_neg_left ψ _ b
  have hβr : -(β.1.map (incA D)) ∈ ratMx D n n := neg_mem (mem_ratMx.2 ⟨β.1, rfl⟩)
  have hcont : Continuous φ := hsz.2.1
  have hnbc : Continuous nb := nb_continuous hnb
  have hγ : ∀ l : ratHerm D n, nb l.1 ∈ GF D n := fun l => nb_rat hnb l.2
  obtain ⟨-, K0, hK0, hK0x⟩ := GlobalTheory.CompanionTheory.HermVol.isCoLat_herm (D := D) (r := n)
  obtain ⟨u, hu, hub⟩ := majorant hH hsz hs (hK0.image (hnbc.mul continuous_const (g := fun _ => g)))
  have hbound : ∀ b, Summable (fun q => ‖F q b‖) ∧ ∑' q, ‖F q b‖ ≤ ∑' q, u q := by
    intro b
    obtain ⟨γ, hγm, hγK⟩ := hK0x b
    let γ' : GF D n := ⟨nb γ, nb_rat hnb hγm⟩
    have hle : ∀ q, ‖F q b‖ ≤ u ((rmulEquiv (P D n) (GF D n) γ').symm q) := by
      intro q
      have h2 := term_mul_left hLI γ' (nb b * g) ((rmulEquiv (P D n) (GF D n) γ').symm q)
      rw [Equiv.apply_symm_apply] at h2
      have h1 : F q b = term (P D n) (GF D n) φ (nb (γ + b) * g)
          ((rmulEquiv (P D n) (GF D n) γ').symm q) := by
        show term (P D n) (GF D n) φ (nb b * g) q = _
        rw [← h2, nb_add hnb, mul_assoc]
      rw [h1]
      have h3 := hub ((rmulEquiv (P D n) (GF D n) γ').symm q) _ ⟨γ + b, hγK, rfl⟩
      rw [hstd] at h3
      exact h3
    have hsu : Summable (fun q => u ((rmulEquiv (P D n) (GF D n) γ').symm q)) :=
      (Equiv.summable_iff (rmulEquiv (P D n) (GF D n) γ').symm).2 hu
    have hsF : Summable (fun q => ‖F q b‖) := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsu
    refine ⟨hsF, ?_⟩
    calc ∑' q, ‖F q b‖ ≤ ∑' q, u ((rmulEquiv (P D n) (GF D n) γ').symm q) := Summable.tsum_le_tsum hle hsF hsu
      _ = ∑' q, u q := Equiv.tsum_eq _ _
  have hF : ∀ q, AEStronglyMeasurable (F q) lam := fun q => by
    have : Continuous (F q) := hcont.comp (continuous_const.mul (hnbc.mul continuous_const))
    exact this.aestronglyMeasurable
  have hchm : AEStronglyMeasurable ch lam := (continuous_chi hψ _).aestronglyMeasurable
  have hchn : ∀ b, ‖ch b‖ = 1 := fun b => hψ.2.1 _
  have hcha : ∀ a b, ch (a + b) = ch a * ch b := fun a b => chi_add_right ψ _ a b
  have hchr : ∀ l : ratHerm D n, ch l = 1 := fun l => chi_rat hψ hβr l
  let τ : ratHerm D n → Cosets (P D n) (GF D n) ≃ Cosets (P D n) (GF D n) :=
    fun l => rmulEquiv (P D n) (GF D n) ⟨nb l.1, hγ l⟩
  have hτ : ∀ (l : ratHerm D n) q b, F q ((l : hermA D n) + b) = F (τ l q) b := by
    intro l q b
    show term (P D n) (GF D n) φ (nb ((l : hermA D n) + b) * g) q =
      term (P D n) (GF D n) φ (nb b * g) (rmulEquiv (P D n) (GF D n) ⟨nb l.1, hγ l⟩ q)
    rw [nb_add hnb, mul_assoc]
    exact term_mul_left hLI (⟨nb l.1, hγ l⟩ : GF D n) (nb b * g) q
  have hτc : ∀ (l : ratHerm D n) q, cosetCell (τ l q) = cosetCell q := by
    intro l q
    obtain ⟨x, hx⟩ := mem_ratMx.1 (AddSubgroup.mem_comap.1 l.2)
    refine GlobalTheory.T.coset_cell_invariant_unipotent q _ x ?_
    show mat (nb l.1) = _
    rw [hnb l.1]
    exact congrArg (fun m => blk4 1 m 0 1) hx.symm
  obtain ⟨e, he, hfib, hval⟩ := GlobalTheory.T.big_cell_cosets_hermitian_param hw hnb
  have he0 : ∀ (l : ratHerm D n) b, F (e l) b = F0 ((l : hermA D n) + b) := by
    intro l b
    show term (P D n) (GF D n) φ (nb b * g) (e l) = φ (w * nb ((l : hermA D n) + b) * g)
    rw [hval _ hLI l (nb b * g), nb_add hnb]
    simp only [mul_assoc]
  have hsmall : ∀ y, y ≠ (⊥ : Submodule D.host.E (Fin n → D.host.E)) →
      ∃ ν, ch ν ≠ 1 ∧ ∀ q, cosetCell q = y → ∀ b, F q (ν + b) = F q b := by
    intro y hy
    obtain ⟨ν0, hν, hsm⟩ := GlobalTheory.T.nondegenerate_character_cell_factorization hψ β hβ y hy
    refine ⟨ν0, by rw [hch]; exact hν, fun q hq b => ?_⟩
    obtain ⟨p, hp, a, ha, hd, hpe⟩ :=
      hsm ((q.out : GF D n) : G D n) (nb ν0) q.out.2 (ratOf q.out) (mat_ratOf q.out) hq (hnb ν0)
    show φ (((q.out : GF D n) : G D n) * (nb (ν0 + b) * g)) =
      φ (((q.out : GF D n) : G D n) * (nb b * g))
    rw [nb_add hnb, mul_assoc, ← mul_assoc ((q.out : GF D n) : G D n), hpe, mul_assoc]
    exact sec_det_one hsz hp ha hd _
  exact (GlobalTheory.T.fundamental_domain_fourier_unfolding lam (ratHerm D n) 𝓖 hD hD1 cosetCell ⊥ F F0 ch hF hchm hchn hcha hchr
    (∑' q, u q) hbound τ hτ hτc e he hfib he0 hsmall).1

end Unfolding

theorem integrable_npow_height {D : D7} {n : ℕ} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    {H : G D n → ℝ≥0} (hH : IsHeight H) {nb : hermA D n → G D n} {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)}
    (hCD : CoefData nb lam 𝓖) {w : G D n} (hw : mat w = blk4 0 1 (-1) 0) (β : HermE D n) (hβ : β.1.det ≠ 0)
    {s : ℂ} (hs : (n : ℝ) / 2 < s.re) (g : G D n) :
    Integrable (fun b : hermA D n => npow (H (w * nb b * g)) (s + (n : ℂ) / 2)) lam := by
  exact integrable_bigCell_spherical hψ hH hCD hw β hβ hs g

end PositivityTheory.PfSWUS.HandIAdd

end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.HandIAdd

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.IwaAd

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G} [μ.IsMulLeftInvariant]
  {X : Type*} [Countable X]

theorem integrable_descend_tsum (a : G → X → ℂ) (ha : ∀ x, Measurable fun g => a g x)
    (hA : LeftInv Γ fun g => ∑' x, ‖a g x‖ₑ) (hL : LeftInv Γ fun g => ∑' x, a g x)
    (hfin : ∫⁻ q, descend Γ (fun g => ∑' x, ‖a g x‖ₑ) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ < ⊤) :
    Integrable (descend Γ fun g => ∑' x, a g x) (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) ∧
      ∀ᵐ q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ, Summable (a q.out) := by
  set A : G → ℝ≥0∞ := fun g => ∑' x, ‖a g x‖ₑ with hAdef
  have hAm : Measurable A := Measurable.ennreal_tsum fun x => (ha x).enorm
  have hAq : Measurable (descend Γ A) := measurable_from_quotient.2 (by
    rw [show descend Γ A ∘ Quotient.mk'' = A from hA.lift_descend]
    exact hAm)
  have hae : ∀ᵐ q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ, descend Γ A q < ⊤ := ae_lt_top hAq hfin.ne
  have haeG : ∀ᵐ g ∂μ, A g < ⊤ := by
    filter_upwards [ae_quotMeasure_iff.1 hae] with g hg
    rwa [hA.descend_mk] at hg
  have hBm : AEStronglyMeasurable (fun g => ∑' x, a g x) μ := by
    refine aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset X))
      (f := fun s g => ∑ x ∈ s, a g x) (fun s => ?_) ?_
    · exact (Finset.measurable_sum s fun x _ => ha x).aestronglyMeasurable
    · filter_upwards [haeG] with g hg
      exact (GlobalTheory.CompanionTheory.ThetaOrbit.summable_of_tsum_enorm_lt_top hg).hasSum
  have hGm : AEStronglyMeasurable (descend Γ fun g => ∑' x, a g x) (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := by
    rw [aestronglyMeasurable_quotMeasure_iff_lift, hL.lift_descend]
    exact hBm
  refine ⟨⟨hGm, ?_⟩, ?_⟩
  · refine (lintegral_mono fun q => ?_).trans_lt hfin
    show ‖∑' x, a q.out x‖ₑ ≤ ∑' x, ‖a q.out x‖ₑ
    exact enorm_tsum_le_tsum_enorm
  · filter_upwards [hae] with q hq
    exact GlobalTheory.CompanionTheory.ThetaOrbit.summable_of_tsum_enorm_lt_top hq

theorem average_descend_finset_sum {N : ℕ} (a : Fin N → G → X → ℂ) (ha : ∀ j x, Measurable fun g => a j g x)
    (hA : ∀ j, LeftInv Γ fun g => ∑' x, ‖a j g x‖ₑ) (hL : ∀ j, LeftInv Γ fun g => ∑' x, a j g x)
    (hfin : ∀ j, ∫⁻ q, descend Γ (fun g => ∑' x, ‖a j g x‖ₑ) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ < ⊤) :
    ⨍ q, descend Γ (fun g => ∑' x, ∑ j, a j g x) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ =
      ∑ j, ⨍ q, descend Γ (fun g => ∑' x, a j g x) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ := by
  have key := fun j => integrable_descend_tsum (μ := μ) (a j) (ha j) (hA j) (hL j) (hfin j)
  have hae : ∀ᵐ q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ, ∀ j, Summable (a j q.out) :=
    ae_all_iff.2 fun j => (key j).2
  have hcongr : (descend Γ fun g => ∑' x, ∑ j, a j g x) =ᵐ[GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ]
      fun q => ∑ j, descend Γ (fun g => ∑' x, a j g x) q := by
    filter_upwards [hae] with q hq
    show ∑' x, ∑ j, a j q.out x = ∑ j, ∑' x, a j q.out x
    exact Summable.tsum_finsetSum fun j _ => hq j
  simp_rw [average_eq]
  rw [integral_congr_ae hcongr, integral_finsetSum _ fun j _ => (key j).1, Finset.smul_sum]

end Abstract

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem ifrB_finset_sum {V : HSp D} {ν : Measure (GA D V)} (hν : ν.IsHaarMeasure) {r : ℕ} (β : HermE D r)
    {N : ℕ} (φs : Fin N → Mx D V.rank r → ℂ) (hc : ∀ j, Continuous (φs j))
    (habs : ∀ j, GlobalTheory.SiegelFormula.absThetaInt V ν (φs j) < ⊤) :
    IfrB V ν (∑ j, φs j) β = ∑ j, IfrB V ν (φs j) β := by
  have : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := hν
  haveI := GlobalTheory.ThetaTransformMeas.countable_field D.host.E
  haveI : Countable (Matrix (Fin V.rank) (Fin r) D.host.E) :=
    inferInstanceAs (Countable (Fin V.rank → Fin r → D.host.E))
  have hrank : ∀ (δ : GL (Fin V.rank) D.host.E) (ξ : Matrix (Fin V.rank) (Fin r) D.host.E),
      (δ.1 * ξ).rank = ξ.rank := fun δ ξ =>
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 δ.isUnit)
  have hfin : ∀ j, ∫⁻ q, descend (GQ V) (fun g => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
      ‖φs j (GlobalTheory.SiegelFormula.invPt V g x.1)‖ₑ) q ∂autMeasure V ν < ⊤ := fun j => by
    refine (lintegral_mono fun q => ?_).trans_lt (habs j)
    exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
      (fun ξ => ‖φs j (GlobalTheory.SiegelFormula.invPt V q.out ξ)‖ₑ)
  have key := average_descend_finset_sum (Γ := GQ V) (μ := ν)
    (X := {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1})
    (fun j h x => φs j (GlobalTheory.SiegelFormula.invPt V h x.1))
    (fun j x => ((hc j).comp (GlobalTheory.AbsThetaSemi.continuous_invPt V x.1)).measurable)
    (fun j => GlobalTheory.CompanionTheory.SplitGram.leftInv_subtypeSum V (fun y => ‖φs j y‖ₑ)
      (fun x : Matrix (Fin V.rank) (Fin r) D.host.E => x.rank = r ∧ gramQ V x = β.1)
      (fun δ hδ ξ h => ⟨(hrank δ ξ).trans h.1, (GlobalTheory.CompanionTheory.SplitGram.gramQ_mul V hδ ξ).trans h.2⟩))
    (fun j => GlobalTheory.CompanionTheory.SplitGram.leftInv_subtypeSum V (φs j)
      (fun x : Matrix (Fin V.rank) (Fin r) D.host.E => x.rank = r ∧ gramQ V x = β.1)
      (fun δ hδ ξ h => ⟨(hrank δ ξ).trans h.1, (GlobalTheory.CompanionTheory.SplitGram.gramQ_mul V hδ ξ).trans h.2⟩))
    hfin
  have e : IfrB V ν (∑ j, φs j) β = ⨍ q, descend (GQ V) (fun g =>
      ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
        ∑ j, φs j (GlobalTheory.SiegelFormula.invPt V g x.1)) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) ν := by
    unfold IfrB
    simp only [Finset.sum_apply]
    rfl
  rw [e]
  exact key

theorem hasTemperateGrowth_evalPoly {m n : ℕ} (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    (fun z : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly p (fun τ => Matrix.of (z τ))).HasTemperateGrowth := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    convert Function.HasTemperateGrowth.const (E := D.what₂.Tau → Fin m → Fin n → ℂ) c using 1
    funext z
    simp [evalPoly]
  | add p q hp hq =>
    convert hp.add hq using 1
    funext z
    simp only [evalPoly, map_add, Pi.add_apply]
  | mul_X p k hp =>
    have hcoord : (fun z : D.what₂.Tau → Fin m → Fin n → ℂ => z k.1 k.2.1 k.2.2.1).HasTemperateGrowth :=
      ((ContinuousLinearMap.proj (R := ℝ) k.2.2.1).comp ((ContinuousLinearMap.proj (R := ℝ) k.2.1).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) k.1))).hasTemperateGrowth
    have hk : (fun z : D.what₂.Tau → Fin m → Fin n → ℂ =>
        if k.2.2.2 then conj (z k.1 k.2.1 k.2.2.1) else z k.1 k.2.1 k.2.2.1).HasTemperateGrowth := by
      split_ifs
      · exact (Complex.conjCLE.toContinuousLinearMap.comp ((ContinuousLinearMap.proj (R := ℝ) k.2.2.1).comp
          ((ContinuousLinearMap.proj (R := ℝ) k.2.1).comp
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) k.1)))).hasTemperateGrowth
      · exact hcoord
    have e : (fun z : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly (p * MvPolynomial.X k) (fun τ => Matrix.of (z τ))) =
        fun z => evalPoly p (fun τ => Matrix.of (z τ)) *
          (if k.2.2.2 then conj (z k.1 k.2.1 k.2.2.1) else z k.1 k.2.1 k.2.2.1) := by
      funext z
      simp only [evalPoly, map_mul, MvPolynomial.eval_X]
      rfl
    rw [e]
    exact hp.mul hk

theorem mem_schwartzA_of_isMonoFock {n : ℕ} {θ : InfFam D} {V : HSp D} {l : D.what₂.Tau → ℝ}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} (hl : ∀ τ, l τ ≠ 0)
    (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ)) {φ : Mx D V.rank n → ℂ} (h : IsMonoFock θ V l s φ) :
    φ ∈ schwartzA θ V.rank n := by
  obtain ⟨e, c, g, d, bs, gv, hpure, rfl⟩ := h
  obtain ⟨f, hf⟩ := GlobalTheory.GaussSchwartz.exists_schwartz_gauss D n V l hl s hs
  have hg := mem_SB_of_isPureFin bs g gv hpure
  have h1 : (fun x : Mx D V.rank n => gauss V l s (fun τ => compAt θ τ x) * g (fun i j => finPart D (x i j))) ∈
      schwartzA θ V.rank n := by
    refine Submodule.subset_span ⟨f, g, hg, ?_⟩
    funext x
    rw [hf]
    rfl
  have h2 := GlobalTheory.CompanionTheory.WSum.mul_mem_schwartzA D θ V.rank n _ (hasTemperateGrowth_evalPoly (MvPolynomial.monomial e c)) _ h1
  convert h2 using 1
  funext x
  rw [← mul_assoc]
  rfl

theorem mem_schwartzA_mul_right {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle}
    {θ : InfFam D} {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hω : IsWeilSch ψ χ θ V μ ω) (a : GL (Fin n) (AE D)) {φ : Mx D V.rank n → ℂ} (hφ : φ ∈ schwartzA θ V.rank n) :
    (fun x : Mx D V.rank n => φ (HMul.hMul x a.1)) ∈ schwartzA θ V.rank n := by
  obtain ⟨g, hg⟩ := GlobalTheory.StdUnn.Model.exists_levi (D := D) a
  set c : ℂ := (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
    npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) / 2) with hcdef
  have hc : c ≠ 0 := mul_ne_zero (Circle.coe_ne_zero _) (GlobalTheory.Doubling.npow_ne_zero (GlobalTheory.CompanionTheory.IwaAd.absA_pos _) _)
  have heq : (fun x : Mx D V.rank n => φ (HMul.hMul x a.1)) = c⁻¹ • (ω g ⟨φ, hφ⟩).1 := by
    funext x
    rw [Pi.smul_apply, hω.levi g a hg ⟨φ, hφ⟩ x, smul_eq_mul, ← hcdef, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [heq]
  exact (schwartzA θ V.rank n).smul_mem _ (ω g ⟨φ, hφ⟩).2

theorem ifrBAdd_of_weilThetaConvergence (hW : GlobalTheory.Published.WeilThetaConvergence) : IfrBAdd := by
  intro D n V ψ χ θ μ ω H l s ν Φ hS hR β _hβ a N φs hφs
  have hl : ∀ τ, l τ ≠ 0 := GlobalTheory.ResAniso.VacSchwartz.realPar_ne_zero D θ hS.hθ ψ hS.hψ l hS.hl
  have hmem : ∀ j, (fun x : Mx D V.rank n => φs j (HMul.hMul x a.1)) ∈ schwartzA θ V.rank n := fun j =>
    mem_schwartzA_mul_right hS.hω a (mem_schwartzA_of_isMonoFock hl hS.hs (hφs j))
  have hn : 1 ≤ n := by obtain ⟨h1, h2, -⟩ := hR; omega
  refine Eq.trans (congrArg (fun f => IfrB V ν f β) ?_) (ifrB_finset_sum hS.hν β _
    (fun j => (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hS.hθ _ _ _ (hmem j)).1)
    (fun j => hW D n V hn (Or.inr hR.2.2) θ hS.hθ ν hS.hν ⟨_, hmem j⟩))
  funext x
  simp only [Finset.sum_apply]
  exact map_sum (Pi.evalAddMonoidHom (fun _ : Mx D V.rank n => ℂ) _) φs Finset.univ

set_option maxHeartbeats 1000000 in

theorem jt_finset_sum {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {θ : InfFam D}
    (hθ : IsInfFam θ) {μ : Measure (Mx D V.rank n)} {𝓕 : Set (Mx D V.rank n)} (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕)
    {N : ℕ} (φs : Fin N → Mx D V.rank n → ℂ) (hmem : ∀ j, φs j ∈ schwartzA θ V.rank n) (b : hermA D n) :
    Jt ψ V μ (∑ j, φs j) b = ∑ j, Jt ψ V μ (φs j) b := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D V.rank n
  haveI : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hphase : Continuous fun y : Mx D V.rank n =>
      ψ (halfTr (Matrix.trace (HMul.hMul b.1 (GlobalTheory.StdUnn.inner V y y) : Mx D n n))) :=
    hψ.1.comp (GlobalTheory.CompanionTheory.BigCellJ.continuous_halfTr.comp
      ((continuous_const.matrix_mul (GlobalTheory.CompanionTheory.BigCellJ.continuous_inner_self V n)).matrix_trace))
  have hint : ∀ j, Integrable (fun y => φs j y *
      ψ (halfTr (Matrix.trace (HMul.hMul b.1 (GlobalTheory.StdUnn.inner V y y) : Mx D n n)))) μ := fun j => by
    have hi := GlobalTheory.CompanionTheory.BigCellJ.integrable_schwartzA hθ hμ (hmem j)
    refine hi.norm.mono' (hi.aestronglyMeasurable.mul hphase.aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun y => by rw [norm_mul, hψ.2.1, mul_one]
  unfold Jt
  rw [← integral_finsetSum _ fun j _ => hint j]
  congr 1
  funext y
  rw [Finset.sum_apply, Finset.sum_mul]

theorem norm_jt_le {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    (μ : Measure (Mx D V.rank n)) (φ : Mx D V.rank n → ℂ) (b : hermA D n) :
    ‖Jt ψ V μ φ b‖ ≤ ∫ y, ‖φ y‖ ∂μ := by
  unfold Jt
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext y
  rw [norm_mul, hψ.2.1, mul_one]

theorem continuous_char_neg {n : ℕ} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (T : Mx D n n) :
    Continuous fun b : hermA D n => ψ (-halfTr (Matrix.trace (HMul.hMul T b.1 : Mx D n n))) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact hψ.1.comp ((GlobalTheory.CompanionTheory.BigCellJ.continuous_halfTr.comp
    (continuous_const.matrix_mul continuous_subtype_val).matrix_trace).neg)

set_option maxHeartbeats 1000000 in

theorem whitT_finset_sum {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {θ : InfFam D}
    (hθ : IsInfFam θ) {μ : Measure (Mx D V.rank n)} {𝓕 : Set (Mx D V.rank n)} (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕)
    (lam : Measure (hermA D n)) (nb : hermA D n → G D n) (w : G D n) (H : G D n → ℝ≥0) (T : Mx D n n) (g : G D n)
    (z : ℂ) (hint : Integrable (fun b : hermA D n => npow (H (w * nb b * g)) (z - s0 V n)) lam)
    {N : ℕ} (φs : Fin N → Mx D V.rank n → ℂ) (hmem : ∀ j, φs j ∈ schwartzA θ V.rank n) :
    whitT ψ V μ lam nb w H (∑ j, φs j) T g z = ∑ j, whitT ψ V μ lam nb w H (φs j) T g z := by
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D n n
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : SecondCountableTopology (hermA D n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
  have hchar := continuous_char_neg hψ T
  have hterm : ∀ j, Integrable (fun b : hermA D n => npow (H (w * nb b * g)) (z - s0 V n) * Jt ψ V μ (φs j) b *
      ψ (-halfTr (Matrix.trace (HMul.hMul T b.1 : Mx D n n)))) lam := fun j => by
    have hJc := GlobalTheory.CompanionTheory.BigCellJ.jt_continuous D n V ψ θ μ (φs j) hψ hθ ⟨𝓕, hμ⟩ (hmem j)
    refine (hint.norm.mul_const (∫ y, ‖φs j y‖ ∂μ)).mono' ?_ ?_
    · exact (hint.aestronglyMeasurable.mul hJc.aestronglyMeasurable).mul hchar.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun b => ?_
      rw [norm_mul, norm_mul, hψ.2.1, mul_one]
      exact mul_le_mul_of_nonneg_left (norm_jt_le hψ μ (φs j) b) (norm_nonneg _)
  unfold whitT
  rw [← integral_finsetSum _ fun j _ => hterm j]
  congr 1
  funext b
  rw [jt_finset_sum hψ hθ hμ φs hmem b, Finset.mul_sum, Finset.sum_mul]

theorem whitTAdd : WhitTAdd := by
  intro D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hCD w hw β hβ a g N φs hφs
  have hl : ∀ τ, l τ ≠ 0 := GlobalTheory.ResAniso.VacSchwartz.realPar_ne_zero D θ hS.hθ ψ hS.hψ l hS.hl
  have hmem : ∀ j, φs j ∈ schwartzA θ V.rank n := fun j => mem_schwartzA_of_isMonoFock hl hS.hs (hφs j)
  obtain ⟨𝓕, hμ⟩ := hS.hμ
  refine ⟨((V.rank : ℝ) + n) / 2, fun z hz => ?_⟩
  have hre : (z - s0 V n - (n : ℂ) / 2).re = z.re - (V.rank : ℝ) / 2 := by
    have e : z - s0 V n - (n : ℂ) / 2 = z - (((V.rank : ℝ) / 2 : ℝ) : ℂ) := by
      unfold s0; push_cast; ring
    rw [e, Complex.sub_re, Complex.ofReal_re]
  have hs' : (n : ℝ) / 2 < (z - s0 V n - (n : ℂ) / 2).re := by rw [hre]; linarith
  have hint0 := integrable_npow_height hS.hψ hS.hH hCD hw β hβ hs' g
  have hexp : z - s0 V n - (n : ℂ) / 2 + (n : ℂ) / 2 = z - s0 V n := by ring
  rw [hexp] at hint0
  exact whitT_finset_sum hS.hψ hS.hθ hμ lam nb w H _ g z hint0 φs hmem

end PositivityTheory.PfSWUS.HandIAdd

end
end
