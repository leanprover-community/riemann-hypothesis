import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.AbsGlob
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.AvgFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.OfLinearEquiv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveFinal
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.DiracInequalityKTypes
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.MultGOfMultFor
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.MultiplicityFormulaHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignOne
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvF
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleUnitaryIrreducibleRep
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleOfLinearReductive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaOfLinearReductive
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsIsSph
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KFiniteVectorsSmooth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactUnitaryFiniteInvariantSubspaceStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.ThetaFixedGlobalCharacter
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SkewExp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.LocAct
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DiracW
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.LefData
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.HomSurj
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.HarmDom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarmonicOfNormBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RangeStable
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.LowType
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.MultiFac
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.OnePlace
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.OpForm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalisedCuspFormL2Bounded
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieActionSkewAdjointL2
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisRepresentationAdmitted
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsThetaInvolution
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRightHaarMeasure
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.HasInfCharGLIff
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.UnitaryCurves.StarMulOfPlaces
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.ContOfRightInv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.FiniteTypes.FintypeHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.RlHecke
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.SumRefine
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.RlSimple

section
noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace UpperTheory.V.Z.GSp4Splitting

variable {n : ℕ}

private theorem cont_tr (E : PositivityTheory.RgBcC.KMod n) (T : E.V →L[ℂ] E.V) :
    Continuous fun κ : Un n =>
      LinearMap.trace ℂ E.V ((E.ρ κ * T : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) := by
  let L : (E.V →L[ℂ] E.V) →ₗ[ℂ] ℂ :=
    (LinearMap.trace ℂ E.V).comp (ContinuousLinearMap.coeLM ℂ)
  have hL : Continuous L := L.continuous_of_finiteDimensional
  exact hL.comp (E.cont.mul continuous_const)

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

private theorem integrable_coef [CompactSpace (Un n)] [MeasurableSpace (Un n)] [BorelSpace (Un n)]
    (ν : Measure (Un n)) [IsFiniteMeasure ν] (σ : Un n →* (V →ₗ[ℂ] V)) (hσ : IsK σ)
    {f : Un n → ℂ} (hf : Continuous f) (v w : V) :
    Integrable (fun κ => f κ * ⟪w, σ κ v⟫_ℂ) ν :=
  (hf.mul (hσ.cont v w)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem exists_avg [CompactSpace (Un n)] [MeasurableSpace (Un n)] [BorelSpace (Un n)]
    (ν : Measure (Un n)) [IsFiniteMeasure ν] (σ : Un n →* (V →ₗ[ℂ] V)) (hσ : IsK σ)
    {f : Un n → ℂ} (hf : Continuous f) (v : V) :
    ∃ p : V, ∀ w : V, ⟪w, p⟫_ℂ = ∫ κ, f κ * ⟪w, σ κ v⟫_ℂ ∂ν := by
  obtain ⟨S, hfd, hv, hS⟩ := hσ.fin v
  have hmem : ∀ κ, σ κ v ∈ S := fun κ => hS κ v hv
  let b := stdOrthonormalBasis ℂ S
  have hexp : ∀ κ, σ κ v = ∑ i, ⟪((b i : S) : V), σ κ v⟫_ℂ • ((b i : S) : V) := by
    intro κ
    have h := b.sum_repr' (⟨σ κ v, hmem κ⟩ : S)
    have h' := congrArg (Subtype.val) h
    simpa [Submodule.coe_sum, Submodule.coe_inner] using h'.symm
  refine ⟨∑ i, (∫ κ, f κ * ⟪((b i : S) : V), σ κ v⟫_ℂ ∂ν) • ((b i : S) : V), fun w => ?_⟩
  have hint : ∀ κ, f κ * ⟪w, σ κ v⟫_ℂ =
      ∑ i, (f κ * ⟪((b i : S) : V), σ κ v⟫_ℂ) * ⟪w, ((b i : S) : V)⟫_ℂ := by
    intro κ
    conv_lhs => rw [hexp κ]
    rw [inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_right]
    ring
  simp_rw [hint]
  rw [integral_finset_sum _ fun i _ => (integrable_coef ν σ hσ hf v _).mul_const _, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, integral_mul_const]

theorem avgEx : AvgEx := by
  intro n _ _ ν _ V _ _ σ hσ E T
  haveI : CompactSpace (Un n) := GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
  have hf := cont_tr E T
  choose p hp using fun v : V => exists_avg ν σ hσ hf v
  have hI := fun v w : V => integrable_coef ν σ hσ hf v w
  refine ⟨{ toFun := p, map_add' := ?_, map_smul' := ?_ }, fun v w => hp v w⟩
  · intro x y
    refine ext_inner_left ℂ fun w => ?_
    rw [inner_add_right, hp, hp, hp, ← integral_add (hI x w) (hI y w)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
    simp only [map_add, inner_add_right, mul_add]
  · intro c x
    refine ext_inner_left ℂ fun w => ?_
    rw [RingHom.id_apply, inner_smul_right, hp, hp, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
    simp only [map_smul, inner_smul_right]
    ring

end UpperTheory.V.Z.GSp4Splitting
end
end

section
open PositivityTheory.RgBcC.RealD

theorem UpperTheory.V.Z.GSp4Splitting.coreG : CoreG := coreG_of countG_holds (multG_of_multFor multiplicity_formula_holds) GlobalTheory.CompanionTheory.SignLine.signOne
end

section
noncomputable section

open MeasureTheory Matrix
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.V.Z.GSp4Splitting

section Abs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

private def cos (U : Subgroup G) (a : G) : Set G := {y | a⁻¹ * y ∈ U}

private theorem cos_self (U : Subgroup G) (a : G) : a ∈ cos U a := by
  simp [cos, U.one_mem]

private theorem isOpen_cos {U : Subgroup G} (hU : IsOpen (U : Set G)) (a : G) : IsOpen (cos U a) :=
  hU.preimage (continuous_const.mul continuous_id)

private theorem exists_reps {U : Subgroup G} (hU : IsOpen (U : Set G)) {C : Set G} (hC : IsCompact C) :
    ∃ s : Finset G, (∀ a ∈ s, ∀ b ∈ s, ∀ y, y ∈ cos U a → y ∈ cos U b → a = b) ∧
      C ⊆ ⋃ a ∈ s, cos U a := by
  classical
  obtain ⟨t, -, ht⟩ := hC.elim_nhds_subcover (fun g => cos U g)
    (fun g _ => (isOpen_cos hU g).mem_nhds (cos_self U g))
  refine ⟨(t.image (fun g => (QuotientGroup.mk g : G ⧸ U))).image Quotient.out, ?_, ?_⟩
  · intro a ha b hb y hya hyb
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hb
    have hab : (Quotient.out q)⁻¹ * Quotient.out q' ∈ U := by
      have := U.mul_mem hya (U.inv_mem hyb)
      simpa [mul_assoc] using this
    have : (QuotientGroup.mk (Quotient.out q) : G ⧸ U) = QuotientGroup.mk (Quotient.out q') :=
      QuotientGroup.eq.2 hab
    have e : q = q' := by
      simpa [QuotientGroup.out_eq'] using this
    rw [e]
  · intro y hy
    obtain ⟨g, hg, hyg⟩ := Set.mem_iUnion₂.1 (ht hy)
    have hr : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk g : G ⧸ U)) : G ⧸ U) = QuotientGroup.mk g :=
      QuotientGroup.out_eq' _
    have hgr : (Quotient.out (QuotientGroup.mk g : G ⧸ U))⁻¹ * g ∈ U := QuotientGroup.eq.1 hr
    refine Set.mem_iUnion₂.2 ⟨Quotient.out (QuotientGroup.mk g : G ⧸ U),
      Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hg), ?_⟩
    have := U.mul_mem hgr hyg
    simpa [cos, mul_assoc] using this

private theorem integral_eq_sum (μ : Measure G) [μ.IsMulLeftInvariant] {U : Subgroup G} (hU : IsOpen (U : Set G))
    (hfin : μ (U : Set G) ≠ ⊤) {h : G → ℂ} (hc : HasCompactSupport h) (hinv : ∀ g, ∀ k ∈ U, h (g * k) = h g) :
    ∃ s : Finset G, ∀ f : G → ℂ, (∀ g, ∀ k ∈ U, f (g * k) = f g) →
      ∫ y, h y * f y ∂μ = ∑ a ∈ s, (h a * (μ.real (U : Set G) : ℂ)) * f a := by
  classical
  obtain ⟨s, hdis, hcov⟩ := exists_reps hU hc.isCompact
  refine ⟨s, fun f hf => ?_⟩
  have hmeas : ∀ a, μ (cos U a) = μ (U : Set G) := fun a => measure_preimage_mul μ a⁻¹ (U : Set G)
  have hval : ∀ a y, y ∈ cos U a → h y * f y = h a * f a := by
    intro a y hy
    have e : y = a * (a⁻¹ * y) := by group
    rw [e, hinv a _ hy, hf a _ hy]
  have hsum : (fun y => h y * f y) = fun y => ∑ a ∈ s, (cos U a).indicator (fun _ => h a * f a) y := by
    funext y
    by_cases hy : ∃ a ∈ s, y ∈ cos U a
    · obtain ⟨a, ha, hya⟩ := hy
      rw [Finset.sum_eq_single a, Set.indicator_of_mem hya, hval a y hya]
      · intro b hb hba
        exact Set.indicator_of_notMem (fun hyb => hba (hdis b hb a ha y hyb hya)) _
      · exact fun h' => (h' ha).elim
    · have hy0 : h y = 0 := by
        refine image_eq_zero_of_notMem_tsupport fun hmem => hy ?_
        obtain ⟨a, ha, hya⟩ := Set.mem_iUnion₂.1 (hcov hmem)
        exact ⟨a, ha, hya⟩
      rw [hy0, zero_mul]
      exact (Finset.sum_eq_zero fun a ha => Set.indicator_of_notMem (fun hya => hy ⟨a, ha, hya⟩) _).symm
  rw [hsum, integral_finset_sum]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_indicator_const _ (isOpen_cos hU a).measurableSet]
    simp only [Measure.real, hmeas a, Complex.real_smul]
    ring
  · intro a _
    refine (integrable_indicator_iff (isOpen_cos hU a).measurableSet).2 ?_
    exact integrableOn_const (by rw [hmeas a]; exact hfin)

end Abs

theorem heckeMem : HeckeMem := by
  intro E _ _ _ n π K hKo hKc _ _ μf _ h hh ψ
  let St : Subgroup (GL (Fin n) (Af E)) :=
    { carrier := {k | finRep E n k ψ.1 = ψ.1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  have hSt : IsOpen (St : Set (GL (Fin n) (Af E))) := (π.cusp ψ.1 ψ.2).1.level
  have hU : IsOpen ((K ⊓ St : Subgroup _) : Set (GL (Fin n) (Af E))) := hKo.inter hSt
  have hfin : μf ((K ⊓ St : Subgroup _) : Set (GL (Fin n) (Af E))) ≠ ⊤ :=
    ((measure_mono Set.inter_subset_left).trans_lt hKc.measure_lt_top).ne
  obtain ⟨s, hs⟩ := integral_eq_sum μf hU hfin hh.1 (fun g k hk => by
    simpa using hh.2 1 K.one_mem k hk.1 g)
  let c : GL (Fin n) (Af E) → ℂ := fun a => h a * (μf.real ((K ⊓ St : Subgroup _) : Set (GL (Fin n) (Af E))) : ℂ)
  have hmem : ∑ g ∈ s, c g • finRep E n g ψ.1 ∈ π.V :=
    Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (π.stable (.fin g) ψ.1 ψ.2)
  have hop : (∑ g ∈ s, c g • finRep E n g ψ.1 : Sm E n).1 = heckeOp μf h ψ.1.1 := by
    funext x
    have hinv := hs (fun g => ψ.1.1 (x * finGL E n g)) (fun g k hk => by
      have e := congrArg (fun φ : Sm E n => φ.1 (x * finGL E n g)) (show finRep E n k ψ.1 = ψ.1 from hk.2)
      have e' : ψ.1.1 (x * finGL E n g * finGL E n k) = ψ.1.1 (x * finGL E n g) := e
      simpa [mul_assoc] using e')
    rw [heckeOp, hinv]
    simp [c, Submodule.coe_sum, Finset.sum_apply]
    rfl
  refine ⟨s, c, ⟨_, hmem⟩, rfl, hop, fun k hk => ?_⟩
  refine Subtype.ext (funext fun x => ?_)
  change (∑ g ∈ s, c g • finRep E n g ψ.1 : Sm E n).1 (x * finGL E n k) = (∑ g ∈ s, c g • finRep E n g ψ.1 : Sm E n).1 x
  rw [hop]
  have e := integral_mul_left_eq_self (μ := μf) (fun g => h g * ψ.1.1 (x * finGL E n g)) k
  simp only [heckeOp]
  rw [← e]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  have e2 : h (k * g) = h g := by simpa using hh.2 k hk 1 K.one_mem g
  simp [e2, map_mul, mul_assoc]

end UpperTheory.V.Z.GSp4Splitting
end
end

section
open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

noncomputable section

namespace UpperTheory.V.Z.GSp4Splitting.LieStabilizer

open Matrix

private theorem flow {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
    (D : S →L[ℝ] S) (c : ℝ → S) (hc : ∀ t, HasDerivAt c (D (c t)) t) :
    c 1 = NormedSpace.exp D (c 0) := by
  have hψ : ∀ t : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp ((1 - u) • D) (c u)) 0 t := by
    intro t
    have he := (hasDerivAt_exp_smul_const (𝕂 := ℝ) D (1 - t)).comp_const_sub 1 t
    have h := he.clm_apply (hc t)
    convert h using 1
    simp [ContinuousLinearMap.mul_apply]
  have hconst := is_const_of_deriv_eq_zero
    (fun u => (hψ u).differentiableAt) (fun u => (hψ u).deriv) 1 0
  simpa using hconst

private theorem exp_mem {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
    (D : S →L[ℝ] S) (M : Submodule ℝ S) (hM : IsClosed (M : Set S)) (hD : ∀ y ∈ M, D y ∈ M)
    {x : S} (hx : x ∈ M) : NormedSpace.exp D x ∈ M := by
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) D
  have hs2 := (ContinuousLinearMap.apply ℝ S x).hasSum hs
  have hpow : ∀ m : ℕ, (D ^ m) x ∈ M := by
    intro m
    induction m with
    | zero => simpa using hx
    | succ m ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply]
      exact hD _ ih
  refine hM.mem_of_tendsto hs2 (Filter.Eventually.of_forall fun s => ?_)
  refine M.sum_mem fun m _ => ?_
  simpa using M.smul_mem _ (hpow m)

private theorem lift {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {S : Submodule ℂ V}
    {c : ℝ → S} {d : S} {t : ℝ} (h : HasDerivAt (fun s => (c s : V)) (d : V) t) : HasDerivAt c d t := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at h ⊢
  exact (Asymptotics.isLittleO_norm_left).1 h.norm_left

variable {n : ℕ}

private def curve (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (t : ℝ) : Un n :=
  ⟨NormedSpace.exp ((t : ℂ) • X), (UpperTheory.RealTr.skewExp n).1 _ (by
    rw [conjTranspose_smul, hX]; simp)⟩

private theorem curve_add (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s t : ℝ) :
    curve X hX (s + t) = curve X hX s * curve X hX t := by
  apply Subtype.ext
  show NormedSpace.exp (((s + t : ℝ) : ℂ) • X) = NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X)
  have hc : Commute ((s : ℂ) • X) ((t : ℂ) • X) := ((Commute.refl X).smul_left _).smul_right _
  rw [← Matrix.exp_add_of_commute _ _ hc, Complex.ofReal_add, add_smul]

private theorem curve_zero (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) : curve X hX 0 = 1 := by
  apply Subtype.ext
  show NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1
  simp

end UpperTheory.V.Z.GSp4Splitting.LieStabilizer

open UpperTheory.V.Z.GSp4Splitting.LieStabilizer in
theorem UpperTheory.V.Z.GSp4Splitting.lieStab :
    LieStab := by
  intro n V _ _ σ Kf hder N hN k x hx
  obtain ⟨X, hX, hXk⟩ := (UpperTheory.RealTr.skewExp n).2 k
  obtain ⟨S, hfd, hxS, hσS, hKS, hd⟩ := hder.2 x
  haveI : FiniteDimensional ℂ S := hfd
  haveI : CompleteSpace S := FiniteDimensional.complete ℂ S

  let L : Module.End ℂ V := ∑ a, ∑ b, X a b • Kf a b
  have hLapp : ∀ w, L w = ∑ a, ∑ b, X a b • Kf a b w := by
    intro w
    simp [L, LinearMap.sum_apply]
  have hLS : ∀ w ∈ S, L w ∈ S := by
    intro w hw
    rw [hLapp]
    exact S.sum_mem fun a _ => S.sum_mem fun b _ => S.smul_mem _ (hKS a b w hw)
  have hLN : ∀ w ∈ N, L w ∈ N := by
    intro w hw
    rw [hLapp]
    exact N.sum_mem fun a _ => N.sum_mem fun b _ => N.smul_mem _ (hN a b w hw)
  let Dc : S →L[ℂ] S := LinearMap.toContinuousLinearMap (L.restrict hLS)
  let D : S →L[ℝ] S := Dc.restrictScalars ℝ
  have hDapp : ∀ w : S, ((D w : S) : V) = L w := fun w => rfl
  let γ := curve X hX
  let c : ℝ → S := fun t => ⟨σ (γ t) x, hσS _ _ hxS⟩
  have hc : ∀ t, HasDerivAt c (D (c t)) t := by
    intro t
    apply lift
    have h0 : HasDerivAt (fun s : ℝ => σ (γ s) (c t : V)) (L (c t : V)) (t - t) := by
      rw [sub_self, hLapp]
      exact hd X γ (fun _ => rfl) _ (c t).2
    have h1 := h0.comp_sub_const t t
    convert h1 using 1
    funext s
    have : γ s = γ (s - t) * γ t := by
      rw [← curve_add, sub_add_cancel]
    show σ (γ s) x = σ (γ (s - t)) (σ (γ t) x)
    rw [this, map_mul, Module.End.mul_apply]
    exact hDapp _
  have h1 := flow D c hc
  let M : Submodule ℂ S := N.comap S.subtype
  have hMc : IsClosed (M : Set S) := Submodule.closed_of_finiteDimensional M
  have hc0 : c 0 ∈ M.restrictScalars ℝ := by
    show σ (γ 0) x ∈ N
    have : γ 0 = 1 := curve_zero X hX
    rw [this, map_one]
    exact hx
  have h2 := exp_mem D (M.restrictScalars ℝ) hMc (fun y hy => hLN _ hy) hc0
  rw [← h1] at h2
  have hk : γ 1 = k := by
    apply Subtype.ext
    show NormedSpace.exp (((1 : ℝ) : ℂ) • X) = k.1
    simpa using hXk
  have h3 : σ (γ 1) x ∈ N := h2
  rwa [hk] at h3
end
end

section
open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

noncomputable section

namespace UpperTheory.V.Z.GSp4Splitting.LowRankIsomorphism

open Finset UpperTheory.RealTr GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

variable {n : ℕ}

private theorem part_sum (c : Fin n → Fin n → ℕ) (Q : Fin n → ℝ)
    (hQ : ∀ x, Q x = ∑ a, ∑ b, (c a b : ℝ) * ((if x = a then 1 else 0) - (if x = b then 1 else 0)))
    (S : Finset (Fin n)) :
    ∑ x ∈ S, Q x = ∑ a, ∑ b, (c a b : ℝ) * ((if a ∈ S then 1 else 0) - (if b ∈ S then 1 else 0)) := by
  simp only [hQ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']

private theorem domLE_of {ν m : Fin n → ℝ} (h : inCone (fun a => (a : ℕ)) (m - ν)) : DomLE ν m := by
  obtain ⟨c, hc, hQ⟩ := h
  refine ⟨fun k => ?_, ?_⟩
  · rw [← sub_nonneg, ← Finset.sum_sub_distrib]
    have hs := part_sum c (m - ν) hQ (univ.filter fun a : Fin n => (a : ℕ) < k)
    simp only [Pi.sub_apply] at hs
    rw [hs]
    refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
    by_cases h0 : c a b = 0
    · simp [h0]
    have hab : (a : ℕ) < b := hc a b h0
    refine mul_nonneg (Nat.cast_nonneg _) ?_
    simp only [mem_filter, mem_univ, true_and]
    split_ifs with h1 h2 h2
    · simp
    · simp
    · omega
    · simp
  · have hs := part_sum c (m - ν) hQ univ
    simp only [Pi.sub_apply, mem_univ, if_true, sub_self, mul_zero, Finset.sum_const_zero,
      Finset.sum_sub_distrib] at hs
    linarith

private theorem int_of (lam : Fin n → ℤ) {ν : Fin n → ℝ} (h : inCone (fun a => (a : ℕ)) (m0 lam - ν)) :
    ∃ z : Fin n → ℤ, ν = wtR z := by
  obtain ⟨c, -, hQ⟩ := h
  refine ⟨fun x => m0Z lam x - ∑ a, ∑ b, (c a b : ℤ) * ((if x = a then 1 else 0) - (if x = b then 1 else 0)), ?_⟩
  funext x
  have hx := hQ x
  simp only [Pi.sub_apply, m0] at hx
  simp only [wtR, m0Z]
  push_cast
  linarith

private theorem harm_of (lam : Fin n → ℤ) (hl : Antitone lam) {ν : Fin n → ℝ} (hν : Antitone ν)
    (h : inCone (fun a => (a : ℕ)) (m0 lam - ν)) (hd : LSq lam ≤ spinSq ν) : ν ∈ harmSet lam := by
  have hle := domLE_of h
  obtain ⟨z, rfl⟩ := int_of lam h
  have hz : Antitone z := fun a b hab => by
    have := hν hab
    simpa [wtR] using this
  rw [harmSet_eq]
  refine Finset.mem_image_of_mem _ (GlobalTheory.T.harmonic_of_norm_bound lam hl z hz hle
    (Tuple.sort fun a => -(wtR z - rhoV n) a) (((rearr n).2.1 (wtR z - rhoV n)).1) ?_)
  refine le_of_eq_of_le ?_ hd
  unfold LSq nsq m0 rhoV
  exact Finset.sum_congr rfl fun a _ => by ring

end UpperTheory.V.Z.GSp4Splitting.LowRankIsomorphism

open UpperTheory.RealTr UpperTheory.V.Z.GSp4Splitting.LowRankIsomorphism in
theorem UpperTheory.V.Z.GSp4Splitting.lowIso2 :
    LowIso := by
  intro n lam hl E T hT V _ _ E1 E2 σ A hc ⟨ν, hne, hcone⟩
  have hK : UF (kF E1 E2) := ⟨GlobalTheory.CompanionTheory.RealCount.KHw.glRel_kF hc.pair, hc.pair.unitK⟩
  have hL : LocF (kF E1 E2) := fun x => by
    obtain ⟨S, h1, h2, -, h3, -⟩ := hc.der.2 x
    exact ⟨S, h1, h2, h3⟩
  have hneK : hw (kF E1 E2) ν ≠ ⊥ := hne
  obtain ⟨-, -, hρ, -, hdom, -⟩ := rearr n
  have hD : Dom ν := (irrCh n V (kF E1 E2) hK hL ν hneK).1
  have hanti : Antitone ν := (hdom ν hD).1
  have hH : ν ∈ harmSet lam :=
    harm_of lam hl hanti hcone (diracW n lam V E1 E2 hc.pair hL hc.ch1 hc.ch2 ν hne)
  obtain ⟨E', e, T', σ', F, χ, s, he, -, hF, hder, -, -, -, hb⟩ := lefData n lam hl E T hT
  have hneF : hw F ν ≠ ⊥ := by
    intro h0
    have ht := (hb ν fun a b hab => add_lt_add_of_le_of_lt (hanti hab.le) (hρ hab)).1
    rw [← (harmDom n lam hl ν hH).2, aux₃ n ν hD, h0, trOn_bot, mul_one] at ht
    exact pow_ne_zero n two_ne_zero ht.symm
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hneF
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hneK
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ
    (show (⟨x, hx⟩ : hw F ν) ≠ 0 from fun h => hx0 (congrArg Subtype.val h))
  obtain ⟨t, ht, htφ, -⟩ := homSurj n E'.V V F (kF E1 E2) hF hK hL ν (f.smulRight (⟨y, hy⟩ : hw (kF E1 E2) ν))
  have htx : t x = y := by
    have := htφ ⟨x, hx⟩
    simpa [hf] using this
  have hg := ((derAt n V σ (kF E1 E2) hc.der).2 E'.V σ' F hder t).2 ht
  have hu : t ∘ₗ e.toLinearMap ∈ invA σ E := fun k ξ => by
    show t (e (ξ ∘L E.ρ k⁻¹)) = σ k (t (e ξ))
    rw [he, hg]
  refine (Submodule.ne_bot_iff _).2 ⟨y, ?_, hy0⟩
  refine Submodule.mem_iSup_of_mem ⟨_, hu⟩ ⟨e.symm x, ?_⟩
  show t (e (e.symm x)) = y
  rw [e.apply_symm_apply, htx]
end
end

section
open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.GKCoh MeasureTheory GlobalTheory.CompanionTheory.TwY.ThInv
open PositivityTheory.Rg.BcB (thetaA)

private theorem exists_class (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : CuspSub E n)
    (hπ : GlobalTheory.DiscSpec.IsNormalised π) :
    ∃ B : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ, (∀ φ ψ, starRingEnd ℂ (B φ ψ) = B ψ φ) ∧ (∀ φ, 0 ≤ (B φ φ).re) ∧
      (∀ φ, φ ≠ 0 → 0 < (B φ φ).re) ∧ (∀ (X : Lie E n) φ ψ, B (lieOp π X φ) ψ + B φ (lieOp π X ψ) = 0) ∧
      ∀ (g : GA E n) (φ ψ φ' ψ' : π.V), (∀ x, φ'.1.1 x = φ.1.1 (x * g)) → (∀ x, ψ'.1.1 x = ψ.1.1 (x * g)) →
        B φ' ψ' = B φ ψ := by
  obtain ⟨μ, hμ, hμ'⟩ := GlobalTheory.CompanionTheory.AdelicHaar.exists_haar_rightInvariant E n
  have hl := GlobalTheory.CompanionTheory.CuspForms.memL2_and_bounded_of_normalised GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL E n μ π hπ
  have hm : ∀ φ ∈ π.V, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E n) μ φ.1 := fun φ hφ => (hl φ hφ).1
  have inj : Function.Injective (toL2ₗ μ π.V hm) :=
    toL2ₗ_injective hm fun ψ hψ => ContAut.continuous_of_isOpen_stab E n ψ (π.cusp ψ hψ).1.level
  have sq : ∀ φ : π.V, (inner ℂ (toL2ₗ μ π.V hm φ) (toL2ₗ μ π.V hm φ)).re = ‖toL2ₗ μ π.V hm φ‖ ^ 2 := fun φ =>
    inner_self_eq_norm_sq (𝕜 := ℂ) _
  refine ⟨((innerₛₗ ℂ).comp (toL2ₗ μ π.V hm)).compl₂ (toL2ₗ μ π.V hm), fun φ ψ =>
    inner_conj_symm (𝕜 := ℂ) (toL2ₗ μ π.V hm ψ) (toL2ₗ μ π.V hm φ), fun φ => ?_,
    fun φ hφ => ?_, fun X φ ψ => ?_, fun g φ ψ φ' ψ' h h' => ?_⟩
  · exact (sq φ).symm ▸ sq_nonneg _
  · exact (sq φ).symm ▸ pow_pos (norm_pos_iff.2 fun e => hφ (inj (e.trans (map_zero _).symm))) 2
  · have e := GlobalTheory.CompanionTheory.PeterssonSkew.lie_skew_adjoint E n μ π hm (fun φ hφ => (hl φ hφ).2) X ψ φ
    exact (add_comm _ _).trans (add_eq_zero_iff_eq_neg.2 e)
  · change inner ℂ (hm _ φ'.2).toL2 (hm _ ψ'.2).toL2 = inner ℂ (hm _ φ.2).toL2 (hm _ ψ.2).toL2
    rw [GlobalTheory.AutomorphicL2Unitary.MemL2Quotient.inner_toL2_eq_theta_pairing, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient.inner_toL2_eq_theta_pairing, funext h, funext h']
    exact GlobalTheory.CompanionTheory.PeterssonSkew.pet_mul_right μ (hm _ ψ.2) (hm _ φ.2) g

theorem UpperTheory.V.Z.GSp4Splitting.petEx :
    PetEx := by
  intro E _ _ _ n _ π hθ
  obtain ⟨B, hc, h0, hp, hL, hg⟩ := exists_class E n π hθ.1
  have hv := thV_apply π hθ
  set T := thV π hθ
  have hTL : ∀ (X : Lie E n) (φ : π.V), T (lieOp π X φ) = -lieOp π (adjH X) (T φ) := fun X φ => by
    refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    have e : φ.1.1 = fun y => (T φ).1.1 (thetaA E n y) := funext fun y => by
      rw [hv, GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol]
    have e2 := lieD_theta X (T φ).1.2 (thetaA E n x)
    rw [← e, GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol] at e2
    exact (hv _ x).trans e2
  have ev : ∀ φ ψ, (B + (B.comp T).compl₂ T) φ ψ = B φ ψ + B (T φ) (T ψ) := fun _ _ => rfl
  refine ⟨B + (B.comp T).compl₂ T, fun φ ψ => ?_, fun φ hφ => ?_, fun X φ ψ => ?_, fun g φ ψ φ' ψ' h h' => ?_,
    fun φ ψ φ' ψ' h h' => ?_⟩
  · rw [ev, ev, map_add, hc, hc]
  · rw [ev, Complex.add_re]
    exact add_pos_of_pos_of_nonneg (hp φ hφ) (h0 _)
  · have e1 := hL X φ ψ
    have e2 := hL (adjH X) (T φ) (T ψ)
    rw [ev, ev, hTL, hTL, map_neg, map_neg, LinearMap.neg_apply]
    linear_combination e1 - e2
  · rw [ev, ev, hg g φ ψ φ' ψ' h h', hg (thetaA E n g) (T φ) (T ψ) (T φ') (T ψ')] <;> intro x
    · rw [hv, hv, h, map_mul, GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol]
    · rw [hv, hv, h', map_mul, GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol]
  · have k : ∀ a a' : π.V, (∀ x, a'.1.1 x = a.1.1 (thetaA E n x)) → T a = a' ∧ T a' = a := fun a a' e =>
      ⟨Subtype.ext (Subtype.ext (funext fun x => (hv a x).trans (e x).symm)),
        Subtype.ext (Subtype.ext (funext fun x => by rw [hv, e, GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol]))⟩
    rw [ev, ev, (k _ _ h).1, (k _ _ h).2, (k _ _ h').1, (k _ _ h').2, add_comm]
end

section
open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc
open scoped InnerProductSpace

namespace UpperTheory.V.Z.GSp4Splitting

section SlopeTestRemainingChoices

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {σ : Un n →* (V →ₗ[ℂ] V)} {E : KMod n}

private theorem sig_inv (k : Un n) (y : V) : σ k (σ k⁻¹ y) = y := by
  have h : σ k * σ k⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact LinearMap.congr_fun h y

private theorem inner_sig (hσ : IsK σ) (k : Un n) (c y : V) : ⟪c, σ k y⟫_ℂ = ⟪σ k⁻¹ c, y⟫_ℂ := by
  have h := hσ.iso k (σ k⁻¹ c) y
  rw [sig_inv] at h
  exact h

private theorem range_mem (t : invA σ E) (ξ : E.V →L[ℂ] ℂ) : t.1 ξ ∈ isoSp σ E :=
  (le_iSup (fun t : invA σ E => LinearMap.range t.1) t) ⟨ξ, rfl⟩

private theorem iso_le {W : Submodule ℂ V} (h : ∀ (t : invA σ E) ξ, t.1 ξ ∈ W) : isoSp σ E ≤ W := by
  refine iSup_le fun t => ?_
  rintro _ ⟨ξ, rfl⟩
  exact h t ξ

private theorem map_iso (B : V →ₗ[ℂ] V) (hB : ∀ k x, B (σ k x) = σ k (B x)) {x : V}
    (hx : x ∈ isoSp σ E) : B x ∈ isoSp σ E := by
  have h : isoSp σ E ≤ (isoSp σ E).comap B := by
    refine iso_le fun t ξ => ?_
    have ht : B.comp t.1 ∈ invA σ E := fun k ξ => by
      simp only [LinearMap.comp_apply]
      rw [t.2 k ξ, hB]
    exact range_mem ⟨_, ht⟩ ξ
  exact h hx

private theorem iso_stable (k : Un n) {x : V} (hx : x ∈ isoSp σ E) : σ k x ∈ isoSp σ E := by
  have h : isoSp σ E ≤ (isoSp σ E).comap (σ k) := by
    refine iso_le fun t ξ => ?_
    show σ k (t.1 ξ) ∈ isoSp σ E
    rw [← t.2 k ξ]
    exact range_mem t _
  exact h hx

private theorem orth_stable (hσ : IsK σ) {K : Submodule ℂ V} (hK : ∀ k, ∀ x ∈ K, σ k x ∈ K)
    (k : Un n) {y : V} (hy : y ∈ Kᗮ) : σ k y ∈ Kᗮ := by
  rw [Submodule.mem_orthogonal] at hy ⊢
  intro c hc
  rw [inner_sig hσ]
  exact hy _ (hK _ _ hc)

private theorem proj_comm (hσ : IsK σ) (K : Submodule ℂ V) [K.HasOrthogonalProjection]
    (hK : ∀ k, ∀ x ∈ K, σ k x ∈ K) (k : Un n) (x : V) :
    K.starProjection (σ k x) = σ k (K.starProjection x) := by
  refine Submodule.eq_starProjection_of_mem_orthogonal (hK _ _ (K.starProjection_apply_mem x)) ?_
  rw [← map_sub]
  exact orth_stable hσ hK k (K.sub_starProjection_mem_orthogonal x)

private theorem core (hσ : IsK σ) (S : Submodule ℂ V) [FiniteDimensional ℂ S]
    (hS : ∀ k, ∀ x ∈ S, σ k x ∈ S) {x : V} (hx : x ∈ S) :
    ∃ u ∈ S ⊓ isoSp σ E, x - u ∈ (isoSp σ E)ᗮ := by
  let D : Submodule ℂ V := S ⊓ isoSp σ E
  haveI : FiniteDimensional ℂ D := Submodule.finiteDimensional_inf_left S _
  haveI : CompleteSpace D := FiniteDimensional.complete ℂ D
  let C : Submodule ℂ V := S ⊓ Dᗮ
  haveI : FiniteDimensional ℂ C := Submodule.finiteDimensional_inf_left S _
  haveI : CompleteSpace C := FiniteDimensional.complete ℂ C
  have hD : ∀ k, ∀ x ∈ D, σ k x ∈ D := fun k x hx => ⟨hS k x hx.1, iso_stable k hx.2⟩
  have hC : ∀ k, ∀ x ∈ C, σ k x ∈ C := fun k x hx => ⟨hS k x hx.1, orth_stable hσ hD k hx.2⟩
  have hu : D.starProjection x ∈ D := D.starProjection_apply_mem x
  refine ⟨D.starProjection x, hu, ?_⟩
  have hc : x - D.starProjection x ∈ C := ⟨S.sub_mem hx hu.1, D.sub_starProjection_mem_orthogonal x⟩
  have hIC : isoSp σ E ≤ Cᗮ := by
    intro y hy
    have h1 : C.starProjection y ∈ isoSp σ E :=
      map_iso (C.starProjection : V →ₗ[ℂ] V) (fun k z => proj_comm hσ C hC k z) hy
    have h2 : C.starProjection y ∈ C := C.starProjection_apply_mem y
    have h3 : C.starProjection y ∈ D := ⟨h2.1, h1⟩
    have h0 : C.starProjection y = 0 := by
      have h4 : C.starProjection y ∈ D ⊓ Dᗮ := ⟨h3, h2.2⟩
      rw [D.inf_orthogonal_eq_bot] at h4
      exact (Submodule.mem_bot ℂ).1 h4
    exact (Submodule.starProjection_apply_eq_zero_iff C).1 h0
  rw [Submodule.mem_orthogonal]
  intro y hy
  have h := (Submodule.mem_orthogonal _ _).1 (hIC hy) _ hc
  rw [← inner_conj_symm, h, map_zero]

end SlopeTestRemainingChoices

end UpperTheory.V.Z.GSp4Splitting

theorem UpperTheory.V.Z.GSp4Splitting.projEx :
    ProjEx := by
  intro n V _ _ σ hσ E
  haveI : (isoSp σ E).HasOrthogonalProjection := ⟨fun v => by
    obtain ⟨S, hfd, hx, hS⟩ := hσ.fin v
    haveI := hfd
    obtain ⟨u, hu, hv⟩ := core (E := E) hσ S hS hx
    exact ⟨u, hu.2, hv⟩⟩
  have hIs : ∀ k, ∀ x ∈ isoSp σ E, σ k x ∈ isoSp σ E := fun k x hx => iso_stable k hx
  refine ⟨((isoSp σ E).starProjection : V →ₗ[ℂ] V), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    exact Submodule.inner_starProjection_left_eq_right _ x y
  · intro x
    exact (isoSp σ E).starProjection_apply_mem x
  · intro x hx
    exact (Submodule.starProjection_eq_self_iff).2 hx
  · intro k
    ext x
    exact proj_comm hσ _ hIs k x
  · rintro B ⟨B', hadj, hcomm⟩
    have hB : ∀ x ∈ isoSp σ E, B x ∈ isoSp σ E := fun x hx =>
      map_iso B (fun k z => LinearMap.congr_fun (hcomm k).1 z) hx
    have hB' : ∀ x ∈ isoSp σ E, B' x ∈ isoSp σ E := fun x hx =>
      map_iso B' (fun k z => LinearMap.congr_fun (hcomm k).2 z) hx
    ext x
    show (isoSp σ E).starProjection (B x) = B ((isoSp σ E).starProjection x)
    refine Submodule.eq_starProjection_of_mem_orthogonal (hB _ ((isoSp σ E).starProjection_apply_mem x)) ?_
    rw [← map_sub, Submodule.mem_orthogonal]
    intro c hc
    have h := (Submodule.mem_orthogonal _ _).1 ((isoSp σ E).sub_starProjection_mem_orthogonal x) (B' c) (hB' c hc)
    rw [← inner_conj_symm, hadj, ← inner_conj_symm, h, map_zero, map_zero]
  · intro N hN x hx
    obtain ⟨S, hfd, hxS, hS⟩ := hσ.fin x
    haveI := hfd
    haveI : FiniteDimensional ℂ (S ⊓ N : Submodule ℂ V) := Submodule.finiteDimensional_inf_left S N
    obtain ⟨u, hu, hv⟩ := core (E := E) hσ (S ⊓ N) (fun k y hy => ⟨hS k y hy.1, hN k y hy.2⟩) ⟨hxS, hx⟩
    have he : (isoSp σ E).starProjection x = u := Submodule.eq_starProjection_of_mem_orthogonal hu.2 hv
    show (isoSp σ E).starProjection x ∈ N
    rw [he]
    exact hu.1.2
end

section
open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.V.Z.GSp4Splitting

open NumberField Finset

private theorem map_epow {n : ℕ} {U W : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [AddCommGroup W] [Module ℂ W] (j : U →ₗ[ℂ] W) (M : Fin n → Fin n → Module.End ℂ U)
    (N : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b u, j (M a b u) = N a b (j u)) (m : ℕ) :
    ∀ a b u, j (PositivityTheory.RgBcC.RealD.epow M m a b u) = Formalism.REAL.epow N m a b (j u) := by
  induction m with
  | zero =>
    intro a b u
    by_cases hab : a = b <;> simp [PositivityTheory.RgBcC.RealD.epow, Formalism.REAL.epow, hab]
  | succ m ih =>
    intro a b u
    rw [PositivityTheory.RgBcC.Bridge.epow_succ']
    simp only [PositivityTheory.RgBcC.RealD.epow, LinearMap.sum_apply, map_sum, Module.End.mul_apply, h, ih]

private theorem map_gelA {n : ℕ} {U W : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [AddCommGroup W] [Module ℂ W] (j : U →ₗ[ℂ] W) (M : Fin n → Fin n → Module.End ℂ U)
    (N : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b u, j (M a b u) = N a b (j u)) (m : ℕ) (u : U) :
    j (gelA M m u) = Formalism.REAL.etr N m (j u) := by
  simp only [gelA, Formalism.REAL.etr, LinearMap.sum_apply, map_sum, map_epow j M N h m]

end UpperTheory.V.Z.GSp4Splitting

theorem UpperTheory.V.Z.GSp4Splitting.rlChar :
    RlChar := by
  intro E _ _ _ n _ π _ K _ _ _ _ _ μf _ D w lam hch
  have hin : Function.Injective ((π.V.subtype).comp D.i) :=
    Subtype.val_injective.comp D.inj
  have h1 := (PositivityTheory.RgBcC.Bridge.hasInfCharGL_iff π.V _ _).1 hch.1
  have h2 := (PositivityTheory.RgBcC.Bridge.hasInfCharGL_iff π.V _ _).1 hch.2
  constructor
  · intro m x
    apply hin
    have e := map_gelA ((π.V.subtype).comp D.i) (D.E1 w) (PositivityTheory.RgBcC.Bridge.eopW w true)
      (fun a b u => D.hE1 w a b u) m x
    rw [e, map_smul]
    simpa [PositivityTheory.RgBcC.Bridge.eopW] using h1 _ (D.i x).2 m
  · intro m x
    apply hin
    have e := map_gelA ((π.V.subtype).comp D.i) (barF (D.E2 w)) (PositivityTheory.RgBcC.Bridge.eopW w false)
      (fun a b u => by
        have := D.hE2 w b a u
        simp only [barF, LinearMap.neg_apply, map_neg, LinearMap.comp_apply, Submodule.subtype_apply,
          Submodule.coe_neg, this, neg_neg]) m x
    rw [e, map_smul]
    simpa [PositivityTheory.RgBcC.Bridge.eopW] using h2 _ (D.i x).2 m
end

section
noncomputable section

open NumberField Matrix MeasureTheory Finset
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GKCoh GlobalTheory.WigAlg
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.Desc
open scoped Classical

namespace UpperTheory.V.Z.GSp4Splitting

section Sum

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

private theorem exists_sum (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) {S : Set G} (hS : IsCompact S) :
    ∃ (T : Finset (G ⧸ K)) (r : G ⧸ K → G) (c : G ⧸ K → ℂ), ∀ F : G → ℂ, (∀ g, ∀ k ∈ K, F (g * k) = F g) →
      (∀ g, g ∉ S → F g = 0) → ∫ g, F g ∂μ = ∑ x ∈ T, c x * F (r x) :=
  _root_.UpperTheory.Reformulated.B.Qg3.exists_sum μ K hKo hKc hS

end Sum

section Ops

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

omit [NumberField E] [IsTotallyComplex E] in
private theorem atW_val (w v : InfinitePlace E) (X : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    atW w X a b v = (if v = w then X else 1) a b := by
  simp only [atW]
  split_ifs <;> rfl

omit [NumberField E] [IsTotallyComplex E] in
private theorem of_atW_mul (w w' v : InfinitePlace E) (X Y : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    ((Matrix.of (atW w X) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (atW w' Y)) a b v =
      ((if v = w then X else 1) * (if v = w' then Y else 1)) a b := by
  simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply, atW_val]

omit [NumberField E] [IsTotallyComplex E] in
private theorem of_atW_inv (w : InfinitePlace E) {X Y : Matrix (Fin n) (Fin n) ℂ} (h : X * Y = 1) :
    (Matrix.of (atW w X) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (atW w Y) = 1 := by
  ext a b v
  rw [of_atW_mul]
  by_cases hv : v = w
  · simp only [if_pos hv, h]
    show _ = (1 : Matrix (Fin n) (Fin n) (Cinf E)) a b v
    simp only [Matrix.one_apply]
    split_ifs <;> rfl
  · simp only [if_neg hv, mul_one]
    show _ = (1 : Matrix (Fin n) (Fin n) (Cinf E)) a b v
    simp only [Matrix.one_apply]
    split_ifs <;> rfl

private def yAt (w : InfinitePlace E) (k : Un n) : GL (Fin n) (Cinf E) where
  val := Matrix.of (atW w k.1)
  inv := Matrix.of (atW w (star k.1))
  val_inv := of_atW_inv w (Unitary.mul_star_self_of_mem k.2)
  inv_val := of_atW_inv w (Unitary.star_mul_self_of_mem k.2)

omit [NumberField E] [IsTotallyComplex E] in
private theorem yAt_comm {w w' : InfinitePlace E} (h : w ≠ w') (k k' : Un n) : yAt w k * yAt w' k' = yAt w' k' * yAt w k := by
  apply Units.ext
  ext a b v
  show ((Matrix.of (atW w k.1) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (atW w' k'.1)) a b v =
    ((Matrix.of (atW w' k'.1) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (atW w k.1)) a b v
  rw [of_atW_mul, of_atW_mul]
  by_cases h1 : v = w
  · have h2 : v ≠ w' := h1 ▸ h
    simp [h1, h]
  · simp [h1]

omit [NumberField E] [IsTotallyComplex E] in
private theorem coord_atW {τ : E →+* ℂ} {w : InfinitePlace E} (h : InfinitePlace.mk τ ≠ w) (X : Matrix (Fin n) (Fin n) ℂ)
    (a b : Fin n) : coord τ (atW w X a b) = (1 : Matrix (Fin n) (Fin n) ℂ) a b := by
  rw [PositivityTheory.Rg.Cz.J.coord_eq, atW_val, if_neg h, Matrix.one_apply]
  split_ifs <;> simp

private theorem commute_rt_Eop {τ : E →+* ℂ} {w : InfinitePlace E} (h : InfinitePlace.mk τ ≠ w) (k : Un n) (a b : Fin n) :
    Commute (Eop τ a b) (rt E n (infGL E n (yAt w k))) := by
  have e := GlobalTheory.CapAdInv.rt_Eop (yAt w k) τ a b
  have c1 : ∀ p q, coord τ ((yAt w k).val p q) = (1 : Matrix (Fin n) (Fin n) ℂ) p q := coord_atW h k.1
  have c2 : ∀ p q, coord τ (((yAt w k)⁻¹ : GL (Fin n) (Cinf E)).val p q) = (1 : Matrix (Fin n) (Fin n) ℂ) p q :=
    coord_atW h (star k.1)
  simp only [c1, c2, Matrix.one_apply, ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e
  exact e.symm

private theorem commute_Eop_fin (τ : E →+* ℂ) (a b : Fin n) (g : GL (Fin n) (Af E)) :
    Commute (Eop τ a b) (finRep E n g) := by
  have hl : ∀ x, Commute (lieS E n a b x) (finRep E n g) := fun x => by
    rw [lieS_apply]
    exact lie_rt_fin _ g
  have e : Eop τ a b = (1 / 2 : ℂ) • (lieS E n a b (atEmb τ 1) - Complex.I • lieS E n a b (atEmb τ Complex.I)) := by
    rw [lieS_atEmb_one, lieS_atEmb_I, smul_smul, Complex.I_mul_I]
    module
  rw [e]
  exact ((hl _).sub_left ((hl _).smul_left _)).smul_left _

private theorem commute_rt_fin (y : GL (Fin n) (Cinf E)) (g : GL (Fin n) (Af E)) :
    Commute (rt E n (infGL E n y)) (finRep E n g) := by
  show rt E n (infGL E n y) * rt E n (finGL E n g) = rt E n (finGL E n g) * rt E n (infGL E n y)
  rw [← map_mul, ← map_mul, infGL_comm]

private theorem exists_op [MeasurableSpace (GL (Fin n) (Af E))] [BorelSpace (GL (Fin n) (Af E))]
    (μf : Measure (GL (Fin n) (Af E))) [μf.IsHaarMeasure] (K : Subgroup (GL (Fin n) (Af E)))
    (hKo : IsOpen (K : Set (GL (Fin n) (Af E)))) (hKc : IsCompact (K : Set (GL (Fin n) (Af E))))
    {h : GL (Fin n) (Af E) → ℂ} (hh : IsHeckeF K h) :
    ∃ A : Module.End ℂ (Sm E n), (∀ B : Module.End ℂ (Sm E n), (∀ g, Commute B (finRep E n g)) → Commute A B) ∧
      ∀ ψ : Sm E n, (∀ k ∈ K, finRep E n k ψ = ψ) → heckeOp μf h ψ.1 = (A ψ).1 := by
  obtain ⟨T, r, c, H⟩ := exists_sum μf K hKo hKc hh.1
  refine ⟨∑ x ∈ T, (c x * h (r x)) • finRep E n (r x), fun B hB => ?_, fun ψ hψ => ?_⟩
  · exact Commute.sum_left _ _ _ fun x _ => ((hB _).symm).smul_left _
  · funext x
    have e := H (fun g => h g * ψ.1 (x * finGL E n g)) (fun g k hk => ?_) (fun g hg => ?_)
    · refine e.trans ?_
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [mul_assoc]
      rfl
    · have e1 : h (g * k) = h g := by simpa using hh.2 1 K.one_mem k hk g
      have e2 : ψ.1 (x * finGL E n g * finGL E n k) = ψ.1 (x * finGL E n g) :=
        congrArg (fun φ : Sm E n => φ.1 (x * finGL E n g)) (hψ k hk)
      simp only [e1, map_mul, ← mul_assoc, e2]
    · simp [image_eq_zero_of_notMem_tsupport hg]

end Ops

theorem rlComm : RlComm := by
  intro E _ _ _ n hn π hθ K hKo hKc hKθ _ _ μf _ D
  let ι : D.U →ₗ[ℂ] Sm E n := π.V.subtype ∘ₗ D.i
  have hinj : Function.Injective ι := π.V.injective_subtype.comp D.inj
  have lift : ∀ (A B : Module.End ℂ D.U) (A' B' : Module.End ℂ (Sm E n)), (∀ u, ι (A u) = A' (ι u)) →
      (∀ u, ι (B u) = B' (ι u)) → Commute A' B' → Commute A B := fun A B A' B' hA hB hc =>
    LinearMap.ext fun u => hinj <| by
      have := LinearMap.congr_fun hc.eq (ι u)
      simp only [Module.End.mul_apply] at this ⊢
      rw [hA, hB, hB, hA, this]
  have h1 : ∀ w a b u, ι (D.E1 w a b u) = Eop w.embedding a b (ι u) := fun w a b u => D.hE1 w a b u
  have h2 : ∀ w a b u, ι (D.E2 w a b u) = (-Eop (ComplexEmbedding.conjugate w.embedding) b a) (ι u) :=
    fun w a b u => D.hE2 w a b u
  have h3 : ∀ w k u, ι (D.σ w k u) = rt E n (infGL E n (yAt w k)) (ι u) := fun w k u =>
    Subtype.ext <| funext fun g => (D.hσ w k u g).trans (chart_val _ g (yAt w k))
  have h4 : ∀ h : {h : GL (Fin n) (Af E) → ℂ // IsHeckeF K h}, ∃ A : Module.End ℂ (Sm E n),
      (∀ B : Module.End ℂ (Sm E n), (∀ g, Commute B (finRep E n g)) → Commute A B) ∧ ∀ u, ι (D.R h u) = A (ι u) := fun h => by
    obtain ⟨A, hA, hA'⟩ := exists_op μf K hKo hKc h.2
    exact ⟨A, hA, fun u => Subtype.ext ((D.hR h u).trans (hA' _ ((D.rng (D.i u)).1 ⟨u, rfl⟩)))⟩
  have mk1 : ∀ w : InfinitePlace E, InfinitePlace.mk w.embedding = w := InfinitePlace.mk_embedding
  have mk2 : ∀ w : InfinitePlace E, InfinitePlace.mk (ComplexEmbedding.conjugate w.embedding) = w := fun w => by
    rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  have ne : ∀ {τ τ' : E →+* ℂ}, InfinitePlace.mk τ ≠ InfinitePlace.mk τ' → τ ≠ τ' := fun h e => h (e ▸ rfl)
  refine ⟨fun i j hij a b => ⟨fun c d => ⟨?_, ?_, ?_⟩, fun k => ⟨?_, ?_⟩⟩, fun i j hij k k' => ?_, fun h i => ⟨fun a b => ⟨?_, ?_⟩, fun k => ?_⟩⟩
  · exact lift _ _ _ _ (h1 i a b) (h1 j c d) (Eop_comm (ne (by rwa [mk1, mk1])) a b c d)
  · exact lift _ _ _ _ (h1 i a b) (h2 j c d) (Commute.neg_right (Eop_comm (ne (by rwa [mk1, mk2])) a b d c))
  · exact lift _ _ _ _ (h2 i a b) (h2 j c d) (Commute.neg_left (Commute.neg_right (Eop_comm (ne (by rwa [mk2, mk2])) b a d c)))
  · exact lift _ _ _ _ (h1 i a b) (h3 j k) (commute_rt_Eop (by rwa [mk1]) k a b)
  · exact lift _ _ _ _ (h2 i a b) (h3 j k) (Commute.neg_left (commute_rt_Eop (by rwa [mk2]) k b a))
  · refine (lift _ _ _ _ (h3 i k) (h3 j k') ?_).eq
    show rt E n (infGL E n (yAt i k)) * rt E n (infGL E n (yAt j k')) = rt E n (infGL E n (yAt j k')) * rt E n (infGL E n (yAt i k))
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, yAt_comm hij]
  · obtain ⟨A, hA, hA'⟩ := h4 h
    exact lift _ _ _ _ hA' (h1 i a b) (hA _ fun g => commute_Eop_fin _ a b g)
  · obtain ⟨A, hA, hA'⟩ := h4 h
    exact lift _ _ _ _ hA' (h2 i a b) (hA _ fun g => Commute.neg_left (commute_Eop_fin _ b a g))
  · obtain ⟨A, hA, hA'⟩ := h4 h
    exact lift _ _ _ _ hA' (h3 i k) (hA _ fun g => commute_rt_fin _ g)

end UpperTheory.V.Z.GSp4Splitting
end
end

section
noncomputable section

open NumberField GlobalTheory.CuspRep PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.Desc
open scoped Classical

namespace UpperTheory.V.Z.GSp4Splitting.RealLieFiniteness

private theorem exists_detect {U : Type} (C : Submodule ℂ (U → ℂ)) [FiniteDimensional ℂ C] :
    ∃ s : Finset U, ∀ f ∈ C, (∀ a ∈ s, f a = 0) → f = 0 := by
  let ev : U → Module.Dual ℂ C := fun a => (LinearMap.proj a).comp C.subtype
  have hfg : (Submodule.span ℂ (ev '' Set.univ)).FG := IsNoetherian.noetherian _
  obtain ⟨t, ht, e⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  obtain ⟨s, -, rfl⟩ := Finset.subset_set_image_iff.1 ht
  refine ⟨s, fun f hf h0 => funext fun a => ?_⟩
  have hle : Submodule.span ℂ (ev '' Set.univ) ≤ LinearMap.ker (Module.Dual.eval ℂ C ⟨f, hf⟩) := by
    rw [e, Submodule.span_le]
    intro l hl
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hl)
    exact h0 b hb
  exact hle (Submodule.subset_span ⟨a, trivial, rfl⟩)

private theorem eq_zero_of_grid {ι U : Type} [Fintype ι] (C : ι → Submodule ℂ (U → ℂ)) (s : ι → Finset U)
    (hs : ∀ i, ∀ f ∈ C i, (∀ a ∈ s i, f a = 0) → f = 0) (F : (ι → U) → ℂ)
    (hF : ∀ i k, (fun a => F (Function.update k i a)) ∈ C i) (h0 : ∀ k, (∀ i, k i ∈ s i) → F k = 0) (k : ι → U) :
    F k = 0 := by
  have key : ∀ (T : Finset ι) (k : ι → U), (∀ i, i ∉ T → k i ∈ s i) → F k = 0 := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun k hk => h0 k fun i => hk i (Finset.notMem_empty i)
    | insert i T _ ih =>
      intro k hk
      have h := hs i _ (hF i k) fun a ha => ih _ fun j hj => by
        by_cases e : j = i
        · subst e
          simpa using ha
        · rw [Function.update_of_ne e]
          exact hk j (by simp [e, hj])
      simpa using congrFun h (k i)
  exact key Finset.univ k fun i hi => absurd (Finset.mem_univ i) hi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private def glue (k : InfinitePlace E → Un n) : Kinf E n :=
  ⟨Matrix.of fun i j v => (k v).1 i j, Matrix.mem_unitaryGroup_iff'.2 <| by
    ext i j v
    have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 (k v).2) i) j
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at h
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply,
      Pi.star_apply, h]
    split_ifs <;> rfl⟩

private theorem glue_mul (k k' : InfinitePlace E → Un n) : glue (k * k') = glue k * glue k' := by
  apply Subtype.ext
  ext i j v
  show ((k v).1 * (k' v).1) i j = ((glue k).1 * (glue k').1) i j v
  simp only [glue, Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply]

private theorem glue_surj (x : Kinf E n) : ∃ k, glue k = x := by
  refine ⟨fun v => ⟨Matrix.of fun i j => x.1 i j v, Matrix.mem_unitaryGroup_iff'.2 ?_⟩, rfl⟩
  ext i j
  have h := congrFun (congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 x.2) i) j) v
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, Finset.sum_apply, Pi.mul_apply, Pi.star_apply] at h
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, Matrix.of_apply, h]
  split_ifs <;> rfl

private theorem along_glue (w : InfinitePlace E) (a : Un n) (φ : GA E n → ℂ) (g : GA E n) :
    along w g φ a.1 = φ (g * infGL E n (Unitary.toUnits (glue (Function.update 1 w a)))) := by
  rw [← chart_val φ g]
  show chart φ g _ = chart φ g _
  congr 1
  funext i j v
  show atW w a.1 i j v = ((Function.update (1 : InfinitePlace E → Un n) w a) v).1 i j
  by_cases e : v = w
  · subst e
    simp [atW]
  · simp [atW, e]

private def box (C : InfinitePlace E → Submodule ℂ (Un n → ℂ)) : Submodule ℂ (Kinf E n → ℂ) where
  carrier := {f | ∀ w x, (fun a => f (x * glue (Function.update 1 w a))) ∈ C w}
  add_mem' hf hg w x := (C w).add_mem (hf w x) (hg w x)
  zero_mem' w _ := (C w).zero_mem
  smul_mem' c _ hf w x := (C w).smul_mem c (hf w x)

private theorem box_fin (C : InfinitePlace E → Submodule ℂ (Un n → ℂ)) [∀ w, FiniteDimensional ℂ (C w)] :
    FiniteDimensional ℂ (box C) := by
  choose s hs using fun w => exists_detect (C w)
  let L : box C →ₗ[ℂ] ((∀ w, s w) → ℂ) := (LinearMap.funLeft ℂ ℂ fun k => glue fun w => (k w).1).comp (box C).subtype
  refine FiniteDimensional.of_injective L ((injective_iff_map_eq_zero L).2 fun f hf => Subtype.ext (funext fun x => ?_))
  obtain ⟨k, rfl⟩ := glue_surj x
  refine eq_zero_of_grid C s hs (fun k => f.1 (glue k)) (fun w k => ?_) (fun k hk => congrFun hf fun w => ⟨k w, hk w⟩) k
  convert f.2 w (glue (Function.update k w 1)) using 3 with a
  rw [← glue_mul]
  congr 1
  funext v
  by_cases e : v = w
  · subst e
    simp
  · simp [e]

private def coef (M : KMod n) : Module.Dual ℂ (M.V →L[ℂ] M.V) →ₗ[ℂ] (Un n → ℂ) where
  toFun l a := l (M.ρ a⁻¹)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem iso_coef {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (σ : Un n →* (V →ₗ[ℂ] V)) (M : KMod n)
    (l : V →ₗ[ℂ] ℂ) {u : V} (hu : u ∈ isoSp σ M) : (fun a => l (σ a u)) ∈ LinearMap.range (coef M) := by
  let L : V →ₗ[ℂ] (Un n → ℂ) := LinearMap.pi fun a => l.comp (σ a)
  have hle : isoSp σ M ≤ (LinearMap.range (coef M)).comap L := by
    refine iSup_le fun t => ?_
    rintro _ ⟨ξ, rfl⟩
    refine ⟨l.comp (t.1.comp (ContinuousLinearMap.compL ℂ M.V M.V ℂ ξ).toLinearMap), funext fun a => ?_⟩
    exact congrArg l (t.2 a ξ)
  exact hle hu

private theorem cap_scalar (π : CuspSub E n) (τ : E →+* ℂ) (z : ℂ) : ∃ c : ℂ, ∀ φ ∈ π.V, cap τ z φ = c • φ := by
  refine π.exists_scalar (Algebra.subset_adjoin ⟨τ, z, rfl⟩) ?_
  rintro (k | k | X)
  exacts [commute_cap_finRep τ z k, GlobalTheory.CapAdInv.cap_commute_rt_infGL E n τ z _, commute_cap_lie τ z X]

end UpperTheory.V.Z.GSp4Splitting.RealLieFiniteness

open UpperTheory.V.Z.GSp4Splitting UpperTheory.V.Z.GSp4Splitting.RealLieFiniteness PositivityTheory.Rg.BcB.E.E3.fintype in
theorem UpperTheory.V.Z.GSp4Splitting.rlFin :
    RlFin := by
  intro E _ _ _ n _ π _ K hK _ _ _ _ μf _ D M
  choose c hc using cap_scalar π
  let W := box fun w => LinearMap.range (coef (M w))
  haveI : FiniteDimensional ℂ W := box_fin _
  haveI := wl_fin W
  haveI := PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E n K hK _ (sig W) (sig_cont W) c
  let j : D.U →ₗ[ℂ] Sm E n := π.V.subtype ∘ₗ D.i
  have hj : Function.Injective j := π.V.injective_subtype.comp D.inj
  have hm : ∀ u ∈ (⨅ w, isoSp (D.σ w) (M w) : Submodule ℂ D.U),
      j u ∈ Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms K (sig W) c) := fun u hu => by
    refine Submodule.subset_span ⟨(π.cusp _ (D.i u).2).1, (D.rng _).1 ⟨u, rfl⟩, coeff_mem W _ fun g w x => ?_,
      fun τ z => hc τ z _ (D.i u).2⟩
    convert iso_coef (D.σ w) (M w)
      ((LinearMap.proj (g * infGL E n (Unitary.toUnits x))).comp ((Sm E n).subtype.comp j))
      ((Submodule.mem_iInf _).1 hu w) using 2 with a
    refine Eq.trans ?_ ((D.hσ w a u _).trans (along_glue w a _ _)).symm
    simp only [map_mul, mul_assoc]
    rfl
  exact FiniteDimensional.of_injective (j.restrict hm) fun a b e =>
    Subtype.ext (hj (congrArg (fun y : Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms K (sig W) c) => y.1) e))
end
end

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL GlobalTheory.UnitaryBC
open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.Desc
open scoped InnerProductSpace ComplexConjugate

namespace UpperTheory.V.Z.GSp4Splitting

private theorem adj_of_skew {M : Type} [AddCommGroup M] [Module ℂ M] (H : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)
    (A B : Module.End ℂ M)
    (h : ∀ (z : ℂ) (φ ψ : M), H ((z • A + star z • B) φ) ψ + H φ ((z • A + star z • B) ψ) = 0)
    (φ ψ : M) : H (A φ) ψ = - H φ (B ψ) := by
  have h1 := h 1 φ ψ
  have hI := h Complex.I φ ψ
  simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smulₛₗ, one_smul, star_one,
    Complex.star_def, Complex.conj_I, map_neg, neg_smul, map_one, RingHom.id_apply, smul_eq_mul,
    Complex.conj_conj, LinearMap.neg_apply] at h1 hI
  linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * hI +
    ((H (A φ) ψ + H φ (B ψ) - H (B φ) ψ - H φ (A ψ)) / 2) * Complex.I_sq

private theorem lie_single {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} (π : CuspSub E n)
    (τ : E →+* ℂ) (a b : Fin n) (z : ℂ) :
    lieOp π (fun i j => atEmb τ (Matrix.single a b z i j)) =
      z • cx τ (lieOp π) a b + star z • cx (PositivityTheory.Rg.Cz.barE E τ) (lieOp π) a b := by
  rw [PositivityTheory.Rg.Cz.GK.lieOp_atEmb, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro j _ hj
    simp [Matrix.single_apply, hj.symm]
  · simp
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    simp [Matrix.single_apply, hi.symm]
  · simp

private theorem cx_val {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} (π : CuspSub E n)
    (τ : E →+* ℂ) (a b : Fin n) (ψ : π.V) : (cx τ (lieOp π) a b ψ).1 = Eop τ a b ψ.1 := by
  rw [← GlobalTheory.WigCap.res_Eop]
  rfl

private theorem emb_ne {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (w : InfinitePlace E) :
    w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
  intro h
  have hc : w.IsComplex := IsTotallyComplex.isComplex w
  exact (InfinitePlace.isComplex_iff.1 hc) (ComplexEmbedding.isReal_iff.2 h.symm)

private theorem gl_pull {U M : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (J : U →ₗ[ℂ] M) (hJ : Function.Injective J) (e : Fin n → Fin n → Module.End ℂ U)
    (F : Fin n → Fin n → Module.End ℂ M) (hF : GlRel F) (h : ∀ a b u, J (e a b u) = F a b (J u)) : GlRel e := by
  intro a b c d
  refine LinearMap.ext fun u => hJ ?_
  have key := LinearMap.congr_fun (hF a b c d) (J u)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at key ⊢
  rw [map_sub, map_sub, h, h, h, h, key]
  split_ifs <;> simp [h]

private theorem gl_neg_swap {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (F : Fin n → Fin n → Module.End ℂ M) (hF : GlRel F) : GlRel (fun a b => -F b a) := by
  intro a b c d
  have key := hF b a d c
  simp only [neg_mul_neg]
  rw [key]
  by_cases h1 : b = c <;> by_cases h2 : d = a
  · subst h1; subst h2; simp; abel
  · have h2' : ¬ a = d := fun h => h2 h.symm
    subst h1
    simp [h2, h2']
  · subst h2
    have h1' : ¬ c = b := fun h => h1 h.symm
    simp [h1, h1']
  · have h2' : ¬ a = d := fun h => h2 h.symm
    have h1' : ¬ c = b := fun h => h1 h.symm
    simp [h1, h1', h2, h2']

end UpperTheory.V.Z.GSp4Splitting

theorem UpperTheory.V.Z.GSp4Splitting.rlPair :
    RlPair := by
  intro E _ _ _ n hn π hθ K hKo hKc hKθ _ _ μf _ D w
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := emb_ne w
  let A : Fin n → Fin n → Module.End ℂ π.V := cx w.embedding (lieOp π)
  let B : Fin n → Fin n → Module.End ℂ π.V := cx (PositivityTheory.Rg.Cz.barE E w.embedding) (lieOp π)
  have v1 : ∀ a b u, (D.i (D.E1 w a b u)).1 = Eop w.embedding a b (D.i u).1 := fun a b u => D.hE1 w a b u
  have v2 : ∀ a b u, (D.i (D.E2 w a b u)).1 = -Eop (ComplexEmbedding.conjugate w.embedding) b a (D.i u).1 :=
    fun a b u => D.hE2 w a b u
  have iE1 : ∀ a b u, D.i (D.E1 w a b u) = A a b (D.i u) := fun a b u =>
    Subtype.ext ((v1 a b u).trans (cx_val π _ a b _).symm)
  have iE2 : ∀ a b u, D.i (D.E2 w a b u) = -B b a (D.i u) := fun a b u =>
    Subtype.ext ((v2 a b u).trans (congrArg Neg.neg (cx_val π _ b a _).symm))
  have adjA : ∀ a b φ ψ, D.H (A a b φ) ψ = -D.H φ (B a b ψ) := fun a b =>
    adj_of_skew D.H _ _ fun z φ ψ => by
      rw [← lie_single]
      exact D.pet.2.2.1 _ φ ψ
  have adjB : ∀ a b φ ψ, D.H (B a b φ) ψ = -D.H φ (A a b ψ) := fun a b φ ψ => by
    have h := congrArg (starRingEnd ℂ) (adjA a b ψ φ)
    rw [map_neg, D.pet.1, D.pet.1] at h
    rw [h, neg_neg]
  have hJ : Function.Injective (π.V.subtype ∘ₗ D.i) := π.V.injective_subtype.comp D.inj
  refine { gl1 := ?_, gl2 := ?_, comm := ?_, unitK := ?_, unitP := ?_ }
  · exact gl_pull _ hJ _ _ (glRel_Eop w.embedding) v1
  · exact gl_pull _ hJ _ _ (gl_neg_swap _ (glRel_Eop (ComplexEmbedding.conjugate w.embedding))) v2
  · intro a b c d
    refine LinearMap.ext fun u => D.inj (Subtype.ext ?_)
    change (D.i (D.E1 w a b (D.E2 w c d u))).1 = (D.i (D.E2 w c d (D.E1 w a b u))).1
    rw [v1, v2, v2, v1, map_neg]
    exact congrArg Neg.neg (LinearMap.congr_fun (Eop_comm hne a b d c) (D.i u).1)
  · intro a b x y
    simp only [kF, LinearMap.add_apply]
    rw [D.inner_eq, D.inner_eq]
    simp only [map_add, iE1, iE2, map_neg, LinearMap.add_apply, LinearMap.neg_apply, adjA, adjB]
    ring
  · intro a b x y
    simp only [pF, LinearMap.sub_apply]
    rw [D.inner_eq, D.inner_eq]
    simp only [map_sub, iE1, iE2, map_neg, LinearMap.sub_apply, LinearMap.neg_apply, adjA, adjB]
    ring
end

section
open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

noncomputable section

open NumberField GlobalTheory.CuspRep PositivityTheory.Rg.BcB GlobalTheory.CompanionTheory.TwY GlobalTheory.CompanionTheory.TwY.ThInv
open scoped InnerProductSpace ComplexConjugate

namespace UpperTheory.V.Z.GSp4Splitting

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem along_unitary (w : InfinitePlace E) (g : GA E n) (φ : GA E n → ℂ) (k : Un n) :
    Bridge.along w g φ k.1 = φ (g * kAt w k) := by
  classical
  have e : Bridge.atW (E := E) w k.1 = toL (locInf w (Unitary.toUnits k)).val := by
    funext i j v
    rw [Bridge.atW]
    exact (locInf_apply w (Unitary.toUnits k) i j v).symm
  rw [Bridge.along, e, chart_val]
  rfl

private theorem eop_theta (w : InfinitePlace E) (a b : Fin n) {φ φ' : Sm E n}
    (h : ∀ x, φ'.1 x = φ.1 (thetaA E n x)) (x : GA E n) :
    (Bridge.eopW w true a b φ).1 (thetaA E n x) = -(Bridge.eopW w false b a φ').1 x := by
  have e : φ'.1 = fun x => φ.1 (thetaA E n x) := funext h
  have e1 : ∀ (f : Sm E n) (y : GA E n), (Bridge.eopW w true a b f).1 y =
      (1 / 2 : ℂ) * (lieD (sg w a b 1) f.1 y - Complex.I * lieD (sg w a b Complex.I) f.1 y) := fun f y => by
    simp only [Bridge.eopW, if_true]
    exact Eop_apply _ a b f y
  have e2 : ∀ (f : Sm E n) (y : GA E n), (Bridge.eopW w false b a f).1 y =
      (1 / 2 : ℂ) * (lieD (sg w b a 1) f.1 y - Complex.I * lieD (sg w b a (-Complex.I)) f.1 y) := fun f y => by
    simp only [Bridge.eopW, Bool.false_eq_true, if_false]
    rw [Eop_apply, atEmb_conjugate, atEmb_conjugate]
    simp [sg]
  rw [e1, e2, e]
  simp only [lieD_theta _ φ.2, adjH_sg, map_one, map_neg, Complex.conj_I, neg_neg]
  ring

end

theorem rlTheta : RlTheta := by
  intro E _ _ _ n _ π _ K _ _ _ _ _ μf _ D
  have hext : ∀ x y : D.U, (∀ g, (D.i x).1.1 g = (D.i y).1.1 g) → x = y := fun x y h =>
    D.inj (Subtype.ext (Subtype.ext (funext h)))
  refine ⟨LinearMap.ext fun u => hext _ _ fun g => ?_, fun x y => ?_, fun w =>
    ⟨fun k => LinearMap.ext fun u => hext _ _ fun g => ?_, fun a b => LinearMap.ext fun u => hext _ _ fun g => ?_⟩⟩
  · change (D.i (D.Θ (D.Θ u))).1.1 g = (D.i u).1.1 g
    rw [D.hΘ, D.hΘ, GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol]
  · rw [D.inner_eq, D.inner_eq]
    exact D.pet.2.2.2.2 _ _ _ _ (D.hΘ x) (D.hΘ y)
  · change (D.i (D.Θ (D.σ w k u))).1.1 g = (D.i (D.σ w k (D.Θ u))).1.1 g
    rw [D.hΘ, D.hσ, D.hσ, along_unitary, along_unitary, D.hΘ, map_mul, thetaA_kAt]
  · change (D.i (D.Θ (D.E1 w a b u))).1.1 g = (D.i (D.E2 w a b (D.Θ u))).1.1 g
    rw [D.hΘ, D.hE1, D.hE2]
    exact eop_theta w a b (D.hΘ u) g

end UpperTheory.V.Z.GSp4Splitting
end
end

section
namespace UpperTheory.V.Z.GSp4Splitting

theorem global_haarAverage_trace_identity : PositivityTheory.Rg.BcB.Desc.ThetaFixedGlobalCharacter :=
  exists_global_hecke_theta_lift avgEx (absGlob multiFac lieStab projEx avgFacts (onePlace coreG lieStab projEx avgFacts (avgTr avgFacts))) lowIso2 heckeMem
    (rlEx petEx heckeMem) rlPair rlChar rlK rlTheta rlComm (rlHecke heckeMem) (rlSimple heckeMem lieStab rlK) rlFin
    (rlLow heckeMem lowType) (opForm heckeMem rlComm locAct)

end UpperTheory.V.Z.GSp4Splitting
end
