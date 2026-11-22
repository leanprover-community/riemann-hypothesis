module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesSummableOnCovolumeDomain
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilObjectsInhabited
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocallyConstantSplitOm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalComponentsNontrivialAdelicCharacter
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenAddSubgroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalComponentsNontrivialAdelicCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsThetaStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRealPlaceSymplecticFormPositiveComplexStru
public import Formalism.LocalToGlobal.IndefiniteReal.DatumLemmas

@[expose] public section

section
section
open MeasureTheory
open scoped ContDiff

noncomputable section
namespace PositivityTheory.Member.ZakTransform.Z

section Param

variable {P T : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T] [MeasurableSpace T] [BorelSpace T]

end Param

section Torus

variable {V T : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T] [MeasurableSpace T] [BorelSpace T]
  (Γ : AddSubgroup T) [Countable Γ] (μ : Measure T) [μ.IsAddHaarMeasure] {𝓕 : Set T}
  (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) {S : Set T} (hS : IsCompact S) (hν : ∀ᵐ t ∂(μ.restrict 𝓕), t ∈ S)
  [IsFiniteMeasure (μ.restrict 𝓕)]

include h𝓕 hS hν

end Torus

section Cube

variable {ι : Type} [Fintype ι]

end Cube

end PositivityTheory.Member.ZakTransform.Z
end
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ContDiff

noncomputable section
namespace PositivityTheory.Member.ZakTransform.Z

open NumberField.mixedEmbedding GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable (F : Type) [Field F] [NumberField F]

def re : mixedSpace F →+ AF F where
  toFun x := pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x) 0
  map_zero' := Prod.ext (map_zero _) rfl
  map_add' x y := Prod.ext (map_add _ x y) (add_zero _).symm

def fi : Af F →+ AF F where
  toFun x := pairA F 0 x
  map_zero' := rfl
  map_add' _ _ := Prod.ext (add_zero _).symm rfl

variable {F}

theorem re_mul_fi (x : mixedSpace F) (y : Af F) : re F x * fi F y = 0 := Prod.ext (mul_zero _) (zero_mul _)
theorem evI_re (x : mixedSpace F) : evI F (re F x) = x := RingEquiv.apply_symm_apply _ x
theorem re_add_fi (x : AF F) : re F (evI F x) + fi F x.2 = x :=
  Prod.ext ((add_zero _).trans (RingEquiv.symm_apply_apply _ _)) (zero_add _)

theorem psi_re {ψ : AddChar (AF F) ℂ} (hstd : IsStd ψ) (x : mixedSpace F) :
    ψ (re F x) = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedSpace F) x : ℝ)) := by
  rw [hstd.2.2 (re F x), evI_re]
  intro u hu
  rw [smul_eq_mul, ← re_add_fi u, hu, map_zero, zero_add, mul_comm, re_mul_fi]

theorem trace_emb (a : F) : Algebra.trace ℝ (mixedSpace F) (mixedEmbedding F a) = (Algebra.trace ℚ F a : ℚ) := by
  classical
  rw [Algebra.trace_eq_matrix_trace (latticeBasis F), Algebra.trace_eq_matrix_trace (integralBasis F), Matrix.trace,
    Matrix.trace, Rat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    latticeBasis_apply, ← map_mul, latticeBasis_repr_apply]

variable {κ : Type} [Fintype κ]

end PositivityTheory.Member.ZakTransform.Z
end
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ContDiff

noncomputable section
namespace PositivityTheory.Member.ZakTransform.Z

open NumberField.mixedEmbedding GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section Coord

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

end Coord

end PositivityTheory.Member.ZakTransform.Z

namespace PositivityTheory.Member.ZakTransform

end PositivityTheory.Member.ZakTransform
end
end
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace PositivityTheory.Member.ZakTransform

section LocA
open Filter Topology

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ψ : AddChar k ℂ} {κ : Type} [Fintype κ]

variable [Invertible (2 : k)]

end LocA

section LocB
open Filter Topology

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ψ : AddChar k ℂ} {κ : Type} [Fintype κ] [Invertible (2 : k)]

end LocB

section LocC
open Filter Topology GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil hiding SB

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end LocC

section LocD
open Filter Topology GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil hiding SB

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end LocD

end PositivityTheory.Member.ZakTransform
end
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace PositivityTheory.Member.ZakTransform

namespace S
section Real
open Complex
open scoped Real ContDiff

end Real
end S

end PositivityTheory.Member.ZakTransform
end
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (pure tens SInf evI At Rest Acts piW)
open GlobalTheory.EmbChart (atPlace atPlace_mul_right evFin_atPlace)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace PositivityTheory.Member.ZakTransform

section Tens
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def stdF (κ : Type) (u : HeightOneSpectrum (𝓞 F)) : (κ → Fv F u) → ℂ :=
  Set.indicator {x | ∀ i, x i ∈ u.adicCompletionIntegers F} 1

def Good (φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ) : Prop :=
  (∀ u, φ u ∈ SB (κ → Fv F u)) ∧ ∀ᶠ u in cofinite, φ u = stdF κ u

def pf (φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ) (y : κ → Af F) : ℂ :=
  ∏ᶠ u, φ u fun i => evalV F u (y i)

theorem ev_int (y : κ → Af F) : ∀ᶠ u in cofinite, ∀ i, evalV F u (y i) ∈ u.adicCompletionIntegers F :=
  eventually_all.2 fun i => (y i).2

theorem cont_evalV (u : HeightOneSpectrum (𝓞 F)) : Continuous (evalV F u) :=
  (continuous_apply u).comp RestrictedProduct.continuous_coe

theorem isOpen_intAf : IsOpen {a : Af F | ∀ v, evalV F v a ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem
    (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _)

theorem isOpen_intV (u : HeightOneSpectrum (𝓞 F)) : IsOpen {x : κ → Fv F u | ∀ i, x i ∈ u.adicCompletionIntegers F} := by
  simp only [Set.setOf_forall]
  exact isOpen_iInter_of_finite fun i => (Valued.isOpen_valuationSubring _).preimage (continuous_apply i)

theorem isCompact_intV (u : HeightOneSpectrum (𝓞 F)) :
    IsCompact {x : κ → Fv F u | ∀ i, x i ∈ u.adicCompletionIntegers F} := by
  have h : IsCompact (u.adicCompletionIntegers F : Set (Fv F u)) := isCompact_iff_compactSpace.2
    (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F u)
  simpa [Set.pi] using isCompact_univ_pi fun _ : κ => h

def intV (κ : Type) [Fintype κ] (u : HeightOneSpectrum (𝓞 F)) : OpenAddSubgroup (κ → Fv F u) where
  carrier := {x | ∀ i, x i ∈ u.adicCompletionIntegers F}
  add_mem' h h' i := add_mem (h i) (h' i)
  zero_mem' _ := zero_mem _
  neg_mem' h i := neg_mem (h i)
  isOpen' := isOpen_intV u

theorem stdF_mem (u : HeightOneSpectrum (𝓞 F)) : stdF κ u ∈ SB (κ → Fv F u) :=
  GlobalTheory.WeilM.HaarUniq.indicator_mem (intV κ u) (isCompact_intV u)

theorem good_std : Good (stdF (F := F) κ) := ⟨stdF_mem, .of_forall fun _ => rfl⟩

theorem isCompact_box (C : ∀ u : HeightOneSpectrum (𝓞 F), Set (Fv F u)) (hC : ∀ u, IsCompact (C u))
    (h : ∀ᶠ u in cofinite, C u ⊆ u.adicCompletionIntegers F) : IsCompact {a : Af F | ∀ u, evalV F u a ∈ C u} := by
  let S : Set (HeightOneSpectrum (𝓞 F)) := {u | C u ⊆ u.adicCompletionIntegers F}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.2 h
  let P := RestrictedProduct (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F)
      (fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F))) (𝓟 S)
  have h1 : IsCompact {x : P | ∀ u, x u ∈ C u} := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isCompact_iff]
    convert isCompact_univ_pi hC
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ u -
      exact hy u
    · intro hx
      exact ⟨⟨x, fun u hu => hu (hx u trivial)⟩, fun u => hx u trivial, rfl⟩
  have h2 := h1.image (RestrictedProduct.continuous_inclusion hS)
  have e : {a : Af F | ∀ u, evalV F u a ∈ C u} = RestrictedProduct.inclusion _ _ hS '' {x : P | ∀ u, x u ∈ C u} := by
    ext a
    constructor
    · intro ha
      exact ⟨⟨a.1, fun u hu => hu (ha u)⟩, ha, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  rw [e]
  exact h2

theorem pf_eq_prod {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ} (S : Finset (HeightOneSpectrum (𝓞 F)))
    (y : κ → Af F) (h : ∀ u ∉ S, φ u = stdF κ u ∧ ∀ i, evalV F u (y i) ∈ u.adicCompletionIntegers F) :
    pf φ y = ∏ u ∈ S, φ u fun i => evalV F u (y i) := by
  refine finprod_eq_prod_of_mulSupport_subset _ fun u hu => ?_
  by_contra hn
  apply hu
  simp only
  rw [(h u hn).1, stdF, Set.indicator_of_mem (by exact (h u hn).2)]
  rfl

theorem exists_fin {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ} (hφ : ∀ᶠ u in cofinite, φ u = stdF κ u)
    (y : κ → Af F) : ∃ S : Finset (HeightOneSpectrum (𝓞 F)),
      ∀ u ∉ S, φ u = stdF κ u ∧ ∀ i, evalV F u (y i) ∈ u.adicCompletionIntegers F :=
  ⟨(hφ.and (ev_int y)).toFinset, fun u hu => by
    by_contra hn
    exact hu (Set.Finite.mem_toFinset _ |>.2 hn)⟩

theorem pf_mem {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ} (hφ : Good φ) : pf φ ∈ SB (κ → Af F) := by
  have hc : ∀ u, Continuous fun (y : κ → Af F) i => evalV F u (y i) := fun u =>
    continuous_pi fun i => (cont_evalV u).comp (continuous_apply i)
  constructor
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨S, hS⟩ := exists_fin hφ.2 x
    have h1 : ∀ᶠ y in 𝓝 x, ∀ i v, evalV F v (y i - x i) ∈ v.adicCompletionIntegers F :=
      eventually_all.2 fun i => (isOpen_intAf.preimage (f := fun y : κ → Af F => y i - x i) (by fun_prop)).mem_nhds
        (by intro v; simp)
    have h2 : ∀ᶠ y in 𝓝 x, ∀ u ∈ S, φ u (fun i => evalV F u (y i)) = φ u fun i => evalV F u (x i) :=
      (eventually_all_finset S).2 fun u _ => ((hφ.1 u).1.comp_continuous (hc u)).eventually_eq x
    filter_upwards [h1, h2] with y h1 h2
    rw [pf_eq_prod S x hS, pf_eq_prod S y fun u hu => ⟨(hS u hu).1, fun i => ?_⟩]
    · exact Finset.prod_congr rfl h2
    · have := add_mem (h1 i u) ((hS u hu).2 i)
      rwa [map_sub, sub_add_cancel] at this
  · have hK : ∀ i : κ, IsCompact {a : Af F | ∀ u, evalV F u a ∈ (fun x => x i) '' tsupport (φ u)} := fun i =>
      isCompact_box _ (fun u => (hφ.1 u).2.isCompact.image (continuous_apply i)) (by
        filter_upwards [hφ.2] with u hu
        rintro _ ⟨x, hx, rfl⟩
        rw [hu] at hx
        exact closure_minimal Set.support_indicator_subset (isCompact_intV u).isClosed hx i)
    refine HasCompactSupport.intro (isCompact_univ_pi hK) fun y hy => ?_
    by_contra h0
    refine hy fun i _ u => ⟨fun i => evalV F u (y i), subset_tsupport _ (fun h => h0 ?_), rfl⟩
    obtain ⟨S, hS⟩ := exists_fin hφ.2 y
    classical
    rw [pf_eq_prod (insert u S) y fun v hv => hS v fun h => hv (Finset.mem_insert_of_mem h)]
    exact Finset.prod_eq_zero (Finset.mem_insert_self _ _) h

theorem pure_mem (f : SInf F κ) {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ} (hφ : Good φ) :
    pure f φ ∈ schA F κ := Submodule.subset_span ⟨f, pf φ, pf_mem hφ, rfl⟩

def box (K : ∀ u : HeightOneSpectrum (𝓞 F), OpenAddSubgroup (κ → Fv F u)) (h : ∀ᶠ u in cofinite, K u = intV κ u)
    (h' : ∀ u, K u ≤ intV κ u) : OpenAddSubgroup (κ → Af F) where
  carrier := {y | ∀ u, (fun i => evalV F u (y i)) ∈ K u}
  add_mem' {a b} ha hb u := by
    have := add_mem (ha u) (hb u)
    simp only [Pi.add_apply, map_add (f := _)]
    exact this
  zero_mem' u := by
    simp only [Pi.zero_apply, map_zero]
    exact zero_mem (K u)
  neg_mem' {a} ha u := by
    have := neg_mem (ha u)
    simp only [Pi.neg_apply, map_neg]
    exact this
  isOpen' := by
    have e : {y : κ → Af F | ∀ u, (fun i => evalV F u (y i)) ∈ K u} =
        (⋂ i, {y | ∀ v, evalV F v (y i) ∈ v.adicCompletionIntegers F}) ∩
          ⋂ u ∈ {u | ¬ K u = intV κ u}, {y | (fun i => evalV F u (y i)) ∈ K u} := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
      refine ⟨fun H => ⟨fun i v => h' v (H v) i, fun u _ => H u⟩, fun H u => ?_⟩
      by_cases hu : K u = intV κ u
      · rw [hu]; exact fun i => H.1 i u
      · exact H.2 u hu
    rw [e]
    exact (isOpen_iInter_of_finite fun i => isOpen_intAf.preimage (continuous_apply i)).inter
      (Set.Finite.isOpen_biInter h fun u _ => (K u).isOpen.preimage
        (continuous_pi fun i => (cont_evalV u).comp (continuous_apply i)))

theorem exists_box {W : Set (κ → Af F)} (hW : W ∈ 𝓝 0) : ∃ K h h', ((box (F := F) (κ := κ) K h h' : OpenAddSubgroup (κ → Af F)) : Set (κ → Af F)) ⊆ W := by
  classical
  let j : (∀ u : HeightOneSpectrum (𝓞 F), intV κ u) → κ → Af F := fun x i =>
    RestrictedProduct.structureMap (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F)
      (fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F))) cofinite fun u => ⟨(x u).1 i, (x u).2 i⟩
  have hj : Continuous j := continuous_pi fun i => RestrictedProduct.isEmbedding_structureMap.continuous.comp
    (continuous_pi fun u => Continuous.subtype_mk (f := fun x : ∀ u, intV κ u => (x u).1 i) ((continuous_apply i).comp
      ((continuous_subtype_val (p := fun x => x ∈ intV κ u)).comp (continuous_apply (A := fun u => intV κ u) u))) _)
  have h0 : j ⁻¹' W ∈ 𝓝 0 := hj.continuousAt.preimage_mem_nhds (by convert hW; rfl)
  rw [nhds_pi, Filter.mem_pi] at h0
  obtain ⟨I, hI, t, ht, hs⟩ := h0
  have : ∀ u, ∃ K : OpenAddSubgroup (κ → Fv F u), ∀ x : intV κ u, x.1 ∈ K → x ∈ t u := fun u => by
    have := ht u
    rw [nhds_subtype, mem_comap] at this
    obtain ⟨s, hs, hst⟩ := this
    obtain ⟨K, hK⟩ := (nonarch_pi (Fv F u) κ).is_nonarchimedean s hs
    exact ⟨K, fun x hx => hst (hK hx)⟩
  choose K hK using this
  refine ⟨fun u => if u ∈ I then K u ⊓ intV κ u else intV κ u, ?_, fun u => ?_, fun y hy => ?_⟩
  · filter_upwards [hI.compl_mem_cofinite] with u hu using if_neg hu
  · simp only
    split_ifs
    · exact inf_le_right
    · exact le_rfl
  · have h1 : ∀ u, (fun i => evalV F u (y i)) ∈ intV κ u := fun u => by
      have := hy u
      simp only at this
      split_ifs at this
      · exact this.2
      · exact this
    refine hs (a := fun u => ⟨_, h1 u⟩) fun u hu => hK u _ ?_
    have := hy u
    simp only [if_pos hu] at this
    exact this.1

theorem mem_span_pf {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) :
    g ∈ Submodule.span ℂ {h | ∃ φ, Good φ ∧ h = pf φ} := by
  haveI : NonarchimedeanAddGroup (κ → Af F) := ⟨fun W hW => by
    obtain ⟨K, h, h', hs⟩ := exists_box hW
    exact ⟨_, hs⟩⟩
  obtain ⟨K₀, hK₀⟩ := GlobalTheory.WeilM.HaarUniq.exists_invariant hg
  obtain ⟨K, h, h', hs⟩ := exists_box K₀.mem_nhds_zero
  obtain ⟨S, hS⟩ := GlobalTheory.WeilM.HaarUniq.exists_decomp (box K h h') hg.2 fun k hk => hK₀ k (hs hk)
  rw [hS]
  refine Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  generalize q.out = a
  have hG : Good fun u x => Set.indicator (K u : Set (κ → Fv F u)) (fun _ => (1 : ℂ)) (x + -fun i => evalV F u (a i)) := by
    constructor
    · intro u
      have := GlobalTheory.WeilM.HaarUniq.indicator_mem (K u) ((isCompact_intV u).of_isClosed_subset (K u).isClosed (h' u))
      exact ⟨this.1.comp_continuous (continuous_add_const _), this.2.comp_homeomorph (Homeomorph.addRight _)⟩
    · filter_upwards [h, ev_int a] with u hu ha
      funext x
      rw [hu]
      have ha' : (-fun i => evalV F u (a i)) ∈ intV κ u := neg_mem (show _ ∈ intV κ u from ha)
      by_cases hx : x ∈ intV κ u
      · rw [Set.indicator_of_mem (add_mem hx ha'), stdF, Set.indicator_of_mem (by exact hx)]; rfl
      · rw [Set.indicator_of_notMem (by rwa [SetLike.mem_coe, add_mem_cancel_right ha']), stdF,
          Set.indicator_of_notMem (by exact hx)]
  refine ⟨_, hG, funext fun y => ?_⟩
  have e : ∀ u, ((fun i => evalV F u (y i)) + -fun i => evalV F u (a i)) = fun i => evalV F u ((y + -a) i) := fun u => by
    funext i; simp
  by_cases hy : y + -a ∈ box K h h'
  · rw [Set.indicator_of_mem (by exact hy), pf, eq_comm]
    refine finprod_eq_one_of_forall_eq_one fun u => ?_
    rw [e, Set.indicator_of_mem (by exact hy u)]
  · rw [Set.indicator_of_notMem (by exact hy)]
    obtain ⟨u, hu⟩ := not_forall.1 hy
    obtain ⟨S, hS⟩ := exists_fin hG.2 y
    classical
    rw [pf_eq_prod (insert u S) y fun v hv => hS v fun h => hv (Finset.mem_insert_of_mem h), eq_comm]
    refine Finset.prod_eq_zero (Finset.mem_insert_self _ _) ?_
    rw [e, Set.indicator_of_notMem (by exact hu)]

theorem pureA_add (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g h : (κ → Af F) → ℂ) :
    pureA F f (g + h) = pureA F f g + pureA F f h := funext fun _ => mul_add _ _ _

theorem pureA_smul (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (c : ℂ) (g : (κ → Af F) → ℂ) :
    pureA F f (c • g) = c • pureA F f g := funext fun _ => mul_left_comm _ _ _

theorem pureA_zero (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) : pureA F f (0 : (κ → Af F) → ℂ) = 0 :=
  funext fun _ => mul_zero _

theorem schA_le : schA F κ ≤ Submodule.span ℂ {Φ | ∃ f φ, Good φ ∧ Φ = pure f φ} := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, g, hg, rfl⟩
  have := mem_span_pf hg
  clear hg
  induction this using Submodule.span_induction with
  | mem x hx => obtain ⟨φ, hφ, rfl⟩ := hx; exact Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  | zero => rw [pureA_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [pureA_add]; exact add_mem hx hy
  | smul a x _ hx => rw [pureA_smul]; exact Submodule.smul_mem _ _ hx

end Tens

section Lift
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : HeightOneSpectrum (𝓞 F))

def off (a : AF F) : AF F := a - atPlace v (evFin F v a)

theorem ev_off (a : AF F) : evFin F v (off v a) = 0 := by simp [off, evFin_atPlace]

theorem off_add (a b : AF F) : off v (a + b) = off v a + off v b := by simp only [off, map_add]; ring

theorem off_mul (a b : AF F) : off v (a * b) = a * off v b := by
  rw [off, off, mul_sub, mul_comm a (atPlace v _), atPlace_mul_right, map_mul, mul_comm (evFin F v a)]

theorem off_off (a : AF F) : off v (off v a) = off v a := by rw [off, ev_off, map_zero, sub_zero]

theorem at_mul_off (t : Fv F v) (a : AF F) : atPlace v t * off v a = 0 := by
  rw [atPlace_mul_right, ev_off, mul_zero, map_zero]

theorem off_add_at (a : AF F) : off v a + atPlace v (evFin F v a) = a := sub_add_cancel _ _

theorem off_dot (x y : κ → AF F) : off v (x ⬝ᵥ y) = x ⬝ᵥ fun i => off v (y i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [off, dotProduct, map_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => off_mul v _ _

theorem ev_dot (x y : κ → AF F) : evFin F v (x ⬝ᵥ y) = (fun i => evFin F v (x i)) ⬝ᵥ fun i => evFin F v (y i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, map_sum, map_mul]

def Indep (r : (κ → AF F) → ℂ) : Prop := ∀ x (t : κ → Fv F v), r (x + fun i => atPlace v (t i)) = r x

def liftG {X Y : Type} (a : X → Y → X) (p : X → Y) (S : Module.End ℂ (Y → ℂ)) : Module.End ℂ (X → ℂ) where
  toFun Ψ x := S (fun t => Ψ (a x t)) (p x)
  map_add' Ψ Ψ' := funext fun x => congrFun (map_add S (fun t => Ψ (a x t)) (fun t => Ψ' (a x t))) _
  map_smul' c Ψ := funext fun x => congrFun (map_smul S c (fun t => Ψ (a x t))) _

def lift (S : Module.End ℂ ((κ → Fv F v) → ℂ)) : Module.End ℂ ((κ → AF F) → ℂ) :=
  liftG (fun x t i => off v (x i) + atPlace v (t i)) (fun x i => evFin F v (x i)) S

theorem lift_apply (S : Module.End ℂ ((κ → Fv F v) → ℂ)) (Ψ : (κ → AF F) → ℂ) (x : κ → AF F) : lift v S Ψ x =
    S (fun t => Ψ fun i => off v (x i) + atPlace v (t i)) fun i => evFin F v (x i) := rfl

variable {v}

theorem Indep.off {r : (κ → AF F) → ℂ} (h : Indep v r) (x : κ → AF F) : r (fun i => off v (x i)) = r x := by
  rw [← h _ fun i => evFin F v (x i)]
  congr 1
  funext i
  exact off_add_at v _

theorem lift_tens (S : Module.End ℂ ((κ → Fv F v) → ℂ)) (φ : (κ → Fv F v) → ℂ) {r : (κ → AF F) → ℂ} (h : Indep v r) :
    lift v S (tens (evFin F v) φ r) = tens (evFin F v) (S φ) r := by
  funext x
  have e : (fun t => tens (evFin F v) φ r fun i => off v (x i) + atPlace v (t i)) = r x • φ := by
    funext t
    have := h (fun i => off v (x i)) t
    rw [h.off] at this
    simp only [tens, map_add (f := _), ev_off, evFin_atPlace, zero_add, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm]
    exact congrArg (· * φ t) this
  rw [lift_apply, e, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  rfl

open Classical in
theorem pure_update (f : SInf F κ) {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ}
    (hφ : ∀ᶠ u in cofinite, φ u = stdF κ u) (φ' : (κ → Fv F v) → ℂ) :
    pure f (Function.update φ v φ') = tens (evFin F v) φ' (pure f (Function.update φ v 1)) := by
  funext x
  obtain ⟨S, hS⟩ := exists_fin hφ fun i => sndA F (x i)
  have key : ∀ φ'' : (κ → Fv F v) → ℂ, pf (Function.update φ v φ'') (fun i => sndA F (x i)) =
      φ'' (fun i => evFin F v (x i)) * ∏ u ∈ S.erase v, φ u fun i => evFin F u (x i) := fun φ'' => by
    rw [pf_eq_prod (insert v (S.erase v)) _ fun u hu => ?_, Finset.prod_insert (Finset.notMem_erase _ _),
      Function.update_self]
    · congr 1
      refine Finset.prod_congr rfl fun u hu => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hu)]
      rfl
    · have h1 : u ≠ v := fun e => hu (e ▸ Finset.mem_insert_self _ _)
      rw [Function.update_of_ne h1]
      exact hS u fun h => hu (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨h1, h⟩))
  show f _ * pf _ (fun i => sndA F (x i)) = φ' _ * (f _ * pf _ (fun i => sndA F (x i)))
  rw [key, key, Pi.one_apply]
  ring

open Classical in
theorem indep_pure (f : SInf F κ) (φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ) :
    Indep v (pure f (Function.update φ v 1)) := by
  intro x t
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  congr 1
  · congr 1
    funext i
    show _ = evI F (x i)
    unfold evI
    congr 1
    exact add_zero _
  · refine finprod_congr fun u => ?_
    by_cases h : u = v
    · subst h; simp
    · refine congrArg _ (funext fun i => ?_)
      rw [Pi.add_apply, map_add (f := _)]
      exact add_eq_left.2 (evalV_singleFin_ne h _)

open Classical in
theorem Good.update {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ} (hφ : Good φ) {φ' : (κ → Fv F v) → ℂ}
    (h : φ' ∈ SB (κ → Fv F v)) : Good (Function.update φ v φ') := by
  refine ⟨fun u => ?_, ?_⟩
  · by_cases e : u = v
    · subst e; rwa [Function.update_self]
    · rw [Function.update_of_ne e]; exact hφ.1 u
  · filter_upwards [hφ.2, (Set.finite_singleton v).compl_mem_cofinite] with u hu e
    rwa [Function.update_of_ne e]

open Classical in
theorem lift_pure (S : Module.End ℂ ((κ → Fv F v) → ℂ)) (f : SInf F κ)
    {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ} (hφ : Good φ) :
    lift v S (pure f φ) = pure f (Function.update φ v (S (φ v))) := by
  conv_lhs => rw [← Function.update_eq_self v φ]
  rw [pure_update f hφ.2, pure_update f hφ.2 (S _), lift_tens _ _ (indep_pure f φ)]

theorem schA_ind {P : ((κ → AF F) → ℂ) → Prop} (h0 : P 0) (h1 : ∀ x y, P x → P y → P (x + y))
    (h2 : ∀ (c : ℂ) x, P x → P (c • x)) (h : ∀ f φ, Good φ → P (pure f φ)) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : P Φ := by
  have := schA_le hΦ
  clear hΦ
  induction this using Submodule.span_induction with
  | mem x hx => obtain ⟨f, φ, hφ, rfl⟩ := hx; exact h f φ hφ
  | zero => exact h0
  | add x y _ _ hx hy => exact h1 _ _ hx hy
  | smul a x _ hx => exact h2 _ _ hx

theorem lift_mem {S : Module.End ℂ ((κ → Fv F v) → ℂ)} (hS : ∀ φ ∈ SB (κ → Fv F v), S φ ∈ SB (κ → Fv F v))
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : lift v S Φ ∈ schA F κ := by
  refine schA_ind (P := fun Φ => lift v S Φ ∈ schA F κ) (by simp) (fun x y hx hy => ?_) (fun c x hx => ?_)
    (fun f φ hφ => ?_) hΦ
  · rw [map_add]; exact add_mem hx hy
  · rw [map_smul]; exact Submodule.smul_mem _ _ hx
  · rw [lift_pure S f hφ]; exact pure_mem f (hφ.update (hS _ (hφ.1 v)))

theorem lift_adm {S : Module.End ℂ ((κ → Fv F v) → ℂ)} (hS : ∀ φ ∈ SB (κ → Fv F v), S φ ∈ SB (κ → Fv F v)) :
    ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ lift v S ∈ (adeleClass F).adm κ := by
  intro l hl g hg
  have : ∃ g' ∈ SB (κ → Af F), ∀ f : SInf F κ, lift v S (pureA F f g) = pureA F f g' := by
    have := mem_span_pf hg
    clear hg
    induction this using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, hφ, rfl⟩ := hx
      exact ⟨_, pf_mem (hφ.update (hS _ (hφ.1 v))), fun f => lift_pure S f hφ⟩
    | zero => exact ⟨0, zero_mem _, fun f => by rw [pureA_zero, map_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hx⟩ := hx
      obtain ⟨b, hb, hy⟩ := hy
      exact ⟨a + b, add_mem ha hb, fun f => by rw [pureA_add, map_add (f := _), hx, hy, pureA_add]⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, hx⟩ := hx
      exact ⟨c • a, Submodule.smul_mem _ _ ha, fun f => by rw [pureA_smul, map_smul, hx, pureA_smul]⟩
  obtain ⟨g', hg', h⟩ := this
  obtain ⟨T, hT⟩ := hl g' hg'
  exact ⟨T, fun f => by rw [LinearMap.comp_apply, h, hT]⟩

theorem lift_lift {S S' : Module.End ℂ ((κ → Fv F v) → ℂ)} (hS : ∀ φ ∈ SB (κ → Fv F v), S' φ ∈ SB (κ → Fv F v))
    {S'' : Module.End ℂ ((κ → Fv F v) → ℂ)} (h : ∀ φ ∈ SB (κ → Fv F v), S (S' φ) = S'' φ)
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : lift v S (lift v S' Φ) = lift v S'' Φ := by
  classical
  refine schA_ind (P := fun Φ => lift v S (lift v S' Φ) = lift v S'' Φ) (by simp) (fun x y hx hy => ?_)
    (fun c x hx => ?_) (fun f φ hφ => ?_) hΦ
  · simp only [map_add (f := _), hx, hy]
  · simp only [map_smul, hx]
  · rw [lift_pure S' f hφ, lift_pure S f (hφ.update (hS _ (hφ.1 v))), lift_pure S'' f hφ, Function.update_self,
      Function.update_idem, h _ (hφ.1 v)]

theorem lift_one (Φ : (κ → AF F) → ℂ) : lift v 1 Φ = Φ := funext fun x => by
  rw [lift_apply]
  exact congrArg Φ (funext fun i => off_add_at v _)

variable (v) in
def psv (ψ : AddChar (AF F) ℂ) : AddChar (Fv F v) ℂ := ψ.compAddMonoidHom (atPlace v).toAddMonoidHom

theorem psv_apply (ψ : AddChar (AF F) ℂ) (t : Fv F v) : psv v ψ t = ψ (atPlace v t) := rfl

scoped instance invTwoV : Invertible (2 : Fv F v) :=
  ⟨evFin F v (⅟2), by rw [← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one],
    by rw [← map_ofNat (evFin F v) 2, ← map_mul, mul_invOf_self, map_one]⟩

variable (v) in
def evP (w : (κ → AF F) × (κ → AF F)) : (κ → Fv F v) × (κ → Fv F v) := (fun i => evFin F v (w.1 i), fun i => evFin F v (w.2 i))

variable (v) in
def offP (w : (κ → AF F) × (κ → AF F)) : (κ → AF F) × (κ → AF F) := (fun i => off v (w.1 i), fun i => off v (w.2 i))

theorem schr_tens (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F)) (φ : (κ → Fv F v) → ℂ) {r : (κ → AF F) → ℂ}
    (h : Indep v r) : schr ψ w (tens (evFin F v) φ r) =
      tens (evFin F v) (schr (psv v ψ) (evP v w) φ) (schr ψ (offP v w) r) := by
  funext x
  have e1 : r (x + w.1) = r (x + (offP v w).1) := by
    rw [← h (x + (offP v w).1) fun i => evFin F v (w.1 i)]
    congr 1
    ext i
    simp only [Pi.add_apply, offP, add_assoc, off_add_at]
  have e2 : ψ (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) =
      psv v ψ ((fun i => evFin F v (x i)) ⬝ᵥ (evP v w).2 + ⅟(2 : Fv F v) * ((evP v w).1 ⬝ᵥ (evP v w).2)) *
      ψ (x ⬝ᵥ (offP v w).2 + ⅟(2 : AF F) * ((offP v w).1 ⬝ᵥ (offP v w).2)) := by
    rw [psv_apply, ← AddChar.map_add_eq_mul, ← off_add_at v (x ⬝ᵥ w.2 + _), add_comm (off v _)]
    congr 2
    · rw [map_add (f := _), map_mul, ev_dot, ev_dot]; rfl
    · rw [off_add, off_mul, off_dot, ← off_off v (w.1 ⬝ᵥ w.2), off_dot v w.1 w.2, dotProduct_comm w.1, off_dot,
        dotProduct_comm (fun i => off v (w.2 i))]
      rfl
  simp only [schr, tens]
  rw [e1, e2]
  simp only [Pi.add_apply, map_add (f := _)]
  show _ = _ * φ (fun i => evFin F v (x i) + evFin F v (w.1 i)) * _
  ring

theorem Indep.schr (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F)) {r : (κ → AF F) → ℂ}
    (h : Indep v r) : Indep v (schr ψ (offP v w) r) := by
  intro x t
  simp only [GlobalTheory.WeilM.schr]
  rw [add_right_comm, h, add_dotProduct]
  congr 3
  refine add_eq_left.2 (Finset.sum_eq_zero fun i _ => at_mul_off v _ _)

theorem schr_add {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (w : (κ → R) × (κ → R))
    (φ φ' : (κ → R) → ℂ) : schr ψ w (φ + φ') = schr ψ w φ + schr ψ w φ' := funext fun _ => mul_add _ _ _

theorem schr_smul {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (w : (κ → R) × (κ → R))
    (c : ℂ) (φ : (κ → R) → ℂ) : schr ψ w (c • φ) = c • schr ψ w φ := funext fun _ => mul_left_comm _ _ _

theorem schr_zero {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (φ : (κ → R) → ℂ) :
    schr ψ 0 φ = φ := funext fun x => by simp [schr]

theorem lift_schr (ψ : AddChar (AF F) ℂ) {S : Module.End ℂ ((κ → Fv F v) → ℂ)} {w w' : (κ → AF F) × (κ → AF F)}
    (h : offP v w = offP v w')
    (hS : ∀ φ ∈ SB (κ → Fv F v), S (schr (psv v ψ) (evP v w) φ) = schr (psv v ψ) (evP v w') (S φ))
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : lift v S (schr ψ w Φ) = schr ψ w' (lift v S Φ) := by
  classical
  refine schA_ind (P := fun Φ => lift v S (schr ψ w Φ) = schr ψ w' (lift v S Φ)) ?_ (fun x y hx hy => ?_)
    (fun c x hx => ?_) (fun f φ hφ => ?_) hΦ
  · have : ∀ w, schr ψ w (0 : (κ → AF F) → ℂ) = 0 := fun w => funext fun _ => mul_zero _
    simp only [this, map_zero]
  · simp only [map_add (f := _), schr_add, hx, hy]
  · simp only [map_smul, schr_smul, hx]
  · have hi := indep_pure (v := v) f φ
    rw [← Function.update_eq_self v φ, pure_update f hφ.2, schr_tens ψ w _ hi, lift_tens _ _ (hi.schr ψ w),
      lift_tens _ _ hi, schr_tens ψ w' _ hi, h, hS _ (hφ.1 v)]

theorem schr_mem_SB {ψ : AddChar (Fv F v) ℂ} (hψ : Continuous ψ) (w : (κ → Fv F v) × (κ → Fv F v))
    {φ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB (κ → Fv F v)) : schr ψ w φ ∈ SB (κ → Fv F v) := by
  haveI := nonarch_field (Fv F v)
  refine ⟨IsLocallyConstant.mul ((isLocallyConstant_addChar ψ hψ).comp_continuous (by fun_prop))
    (hφ.1.comp_continuous (continuous_add_const _)), HasCompactSupport.mul_left ?_⟩
  exact hφ.2.comp_homeomorph (Homeomorph.addRight _)

end Lift

section Split
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (AE cA incM UA Spc Model Rep mat HasSig)
open GlobalTheory.EmbChart (tensAt compFin_tensAt tensAt_mul_right tensAt_tmul)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)}

theorem piW_tmul (t : E →ₐ[F] Fv F v) (a : AF F) (x : E) : piW t (a ⊗ₜ[F] x) = evFin F v a * t x := rfl

theorem piW_smul (t : E →ₐ[F] Fv F v) (a : AF F) (z : AE F E) : piW t (a • z) = evFin F v a * piW t z := by
  rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply, piW_tmul, map_one, mul_one]
  rfl

theorem piW_inc (t : E →ₐ[F] Fv F v) (x : E) : piW t (inclR (F := F) (AF F) x) = t x :=
  (piW_tmul t 1 x).trans (by rw [map_one, one_mul])

theorem piW_cA (t : E →ₐ[F] Fv F v) (z : AE F E) : piW t (cA σ z) = piW (t.comp σ) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem trace_cm (h : IsCMExt F E σ) (x : E) : algebraMap F E (Algebra.trace F E x) = x + σ x := by
  classical
  have h1 := trace_eq_sum_embeddings (K := F) (L := E) (AlgebraicClosure E) (x := x)
  let τ : E →ₐ[F] AlgebraicClosure E := IsScalarTower.toAlgHom F E _
  have h2 : (Finset.univ : Finset (E →ₐ[F] AlgebraicClosure E)) = {τ, τ.comp σ} := by
    ext τ'
    simpa using eq_or_eq_comp_conj h τ τ'
  rw [h2, Finset.sum_pair (comp_conj_ne h τ).symm] at h1
  apply (algebraMap E (AlgebraicClosure E)).injective
  rw [← IsScalarTower.algebraMap_apply, h1, map_add (f := _)]
  rfl

theorem trace_tmul {R : Type} [CommRing R] [Algebra F R] (r : R) (x : E) :
    Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] x) = r * algebraMap F R (Algebra.trace F E x) := by
  have h1 : (r ⊗ₜ[F] x : R ⊗[F] E) = r • ((1 : R) ⊗ₜ[F] x) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

theorem ev_trace (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (z : AE F E) :
    evFin F v (Algebra.trace (AF F) (AE F E) z) = piW t z + piW (t.comp σ) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, add_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]; ring
  | tmul a x =>
    rw [trace_tmul, map_mul, AlgHom.commutes, piW_tmul, piW_tmul, ← t.commutes, trace_cm h, map_add (f := _), mul_add]
    rfl

variable (v) in
def ep : AF F := atPlace v 1

theorem ep_mul (a : AF F) : ep v * a = atPlace v (evFin F v a) := by rw [ep, atPlace_mul_right, one_mul]

theorem ev_ep : evFin F v (ep v) = 1 := evFin_atPlace v 1

theorem ep_ep : ep v * ep v = ep v := by rw [ep_mul, ev_ep]; rfl

theorem off_eq (a : AF F) : off v a = (1 - ep v) * a := by rw [sub_mul, one_mul, ep_mul]; rfl

theorem ep_smul (z : AE F E) : ep v • z = tensAt E v (compFin F E v z) := by
  have := tensAt_mul_right (E := E) v 1 z
  rw [one_mul] at this
  rw [← this, Algebra.smul_def]
  rfl

theorem at_iff {M : Type} [AddCommGroup M] [Module (AF F) M] (z : M) : At (evFin F v) z ↔ ep v • z = z := by
  constructor
  · intro h
    have := h (1 - ep v) (by rw [map_sub, map_one, ev_ep, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  · intro h a ha
    rw [← h, smul_smul, mul_comm, ep_mul, ha, map_zero, zero_smul]

theorem AE_ext (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {y z : AE F E} (h0 : (1 - ep v) • y = (1 - ep v) • z)
    (h1 : piW t y = piW t z) (h2 : piW (t.comp σ) y = piW (t.comp σ) z) : y = z := by
  have : ep v • y = ep v • z := by rw [ep_smul, ep_smul, split_ext h t h1 h2]
  rw [sub_smul, sub_smul, this, one_smul, one_smul] at h0
  exact sub_left_injective h0

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

end Split

section Gen
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {v : HeightOneSpectrum (𝓞 F)}

theorem cont_at : Continuous (atPlace (F := F) v) := continuous_const.prodMk (continuous_singleFin v)

end Gen

section PartB
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (AE cA incM UA Spc Model Rep mat HasSig)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem offP_eq {κ : Type} (w : (κ → AF F) × (κ → AF F)) : offP v w = (1 - ep v) • w :=
  Prod.ext (funext fun _ => off_eq _) (funext fun _ => off_eq _)

end PartB

section PartA
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.MainNotions.StandardLattice GlobalTheory.ChiGrid GlobalTheory.FunObj
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (skewGram mulG colV adjV₁ incM boxB IsDatumB)
open Formalism.IndefR.Datum.Brg (GG GI cA_inc GG_herm GI_GG)
open scoped ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

end PartA

section Datum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.MainNotions.StandardLattice GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.StdFrames
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (boxB IsDatumB)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Datum

end PositivityTheory.Member.ZakTransform
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
