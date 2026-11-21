import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PropZStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreConnected
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateKernelAtPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverStatementHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartStatementHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectionStatementHolds
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DetCondTensorDefinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleModelsOfHtBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLocalOfKernelAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericStatementOfCanonicalExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonStatementHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistenceOfComparison
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftingOfComparison
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateStatementHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueStatementHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundStatementHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointwiseOfTateValueBound
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreConnectedOfProper
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluingOfConnectedness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationConstantOfPowerEq
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite

section
open AlgebraicGeometry CategoryTheory GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_fibre_connected : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Y : Scheme.{0}) (f : Y ⟶ Spec (.of O)), IsIntegral Y → (∀ z : Y, IsIntegrallyClosed (Y.presheaf.stalk z)) → IsProper f → Flat f → ConnectedSpace (specialFibre f) := by
  first | exact @GlobalTheory.SpecialConn.connectedSpace_specialFibre | exact GlobalTheory.SpecialConn.connectedSpace_specialFibre | (intros; apply GlobalTheory.SpecialConn.connectedSpace_specialFibre <;> assumption)
end

section
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_statement_holds : ChartSt := by
  first | exact @GlobalTheory.FlatModel.chartSt | exact GlobalTheory.FlatModel.chartSt | (intros; apply GlobalTheory.FlatModel.chartSt <;> assumption)
end

section
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projection_statement_holds : ProjSt := by
  first | exact @GlobalTheory.FlatModel.Proj.projSt | exact GlobalTheory.FlatModel.Proj.projSt | (intros; apply GlobalTheory.FlatModel.Proj.projSt <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel.LatDual

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def actZ (Dw : Datum H) : 𝓞 E →+* Module.End ℤ Dw.La := (Algebra.lsmul ℤ ℤ Dw.La).toRingHom

theorem actZ_apply (Dw : Datum H) (o : 𝓞 E) :
    actZ Dw o = (LinearMap.lsmul (𝓞 E) Dw.La o).restrictScalars ℤ :=
  LinearMap.ext fun _ => rfl

theorem finrank_eig (Dw : Datum H) [Module.Finite ℤ Dw.La] [Module.Free ℤ Dw.La] {K : Type} [Field K]
    [Algebra K ℂ] (V : ValuationSubring K) (σ : 𝓞 E →+* V) :
    Module.finrank V (EigenSplit.eigenSub (EigenSplit.baseChangeAction V (actZ Dw)) σ) = Dw.p + Dw.q := by
  have : FaithfulSMul V K := (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective V K)
  have : Module.Flat V K := EigenSplit.flat_of_valuationRing V K
  have hF := EigenSplit.finrank_eigenSub_of_flat (R := V) (R' := K) (ρ := EigenSplit.baseChangeAction V (actZ Dw))
    (ρ' := EigenSplit.baseChangeAction K (actZ Dw)) (f := EigenSplit.extendTensor ℤ V K Dw.La)
    (EigenSplit.extendTensor_equivariant V K (actZ Dw)) (EigenSplit.isBaseChange_extendTensor ℤ V K Dw.La) σ
  have hC := EigenSplit.finrank_eigenSub_of_flat (R := K) (R' := ℂ) (ρ := EigenSplit.baseChangeAction K (actZ Dw))
    (ρ' := EigenSplit.baseChangeAction ℂ (actZ Dw)) (f := EigenSplit.extendTensor ℤ K ℂ Dw.La)
    (EigenSplit.extendTensor_equivariant K ℂ (actZ Dw)) (EigenSplit.isBaseChange_extendTensor ℤ K ℂ Dw.La)
    ((algebraMap V K).comp σ)
  have hT := TensorDet.finrank_eigenSub (E := E) (k := ℂ) (O := ℤ) (M := Dw.La)
    ((algebraMap K ℂ).comp ((algebraMap V K).comp σ)) (RingHom.ext_int _ _)
  have e : TensorDet.rightAction ℂ ℤ (𝓞 E) Dw.La = EigenSplit.baseChangeAction ℂ (actZ Dw) := rfl
  rw [e, hC, hF, Dw.rank] at hT
  exact hT

end GlobalTheory.FlatModel.LatDual

namespace GlobalTheory.FlatModel.LatDual

theorem latSt : LatSt := by
  intro E _ _ _ H Dw l c W p hp hW τ
  classical
  obtain ⟨N, ⟨a⟩⟩ : ∃ k : ℕ, Nonempty (Module.Basis (Fin k) ℤ Dw.La) := by
    haveI := Dw.fin
    haveI : Module.Finite ℤ Dw.La := Module.Finite.trans (𝓞 E) Dw.La
    haveI : Module.IsTorsionFree ℤ Dw.La :=
      Function.Injective.moduleIsTorsionFree Dw.EF Dw.unimod.1 (fun r x => map_smul _ r x)
    haveI : Module.Free ℤ Dw.La := Module.free_of_finite_type_torsion_free'
    exact ⟨_, ⟨Module.finBasis ℤ Dw.La⟩⟩
  haveI : Module.Free ℤ Dw.La := Module.Free.of_basis a
  haveI : Module.Finite ℤ Dw.La := Module.Finite.of_basis a
  set σ : 𝓞 E →+* c.V W := embV c W (conjEmb τ.1) with hσ
  set K := EigenSplit.eigenSub (EigenSplit.baseChangeAction (c.V W) (actZ Dw)) σ with hK
  haveI : Module.Free (c.V W) K := EigenSplit.free_eigenSub_of_valuationRing _ _
  haveI : Module.Finite (c.V W) K := EigenSplit.finite_eigenSub_of_valuationRing _ _
  have hrk : Fintype.card (Ind Dw τ.1) = Module.finrank (c.V W) K := by
    rw [hK, finrank_eig, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin,
      GlobalTheory.ShFam.Pad.AdmExist.mult_add_mult_conj]
  let b : Module.Basis (Ind Dw τ.1) (c.V W) K := (Module.finBasis (c.V W) K).reindex (Fintype.equivFinOfCardEq hrk).symm
  obtain ⟨Q, hQ⟩ := EigenSplit.exists_isCompl_eigenSub_of_valuationRing (EigenSplit.baseChangeAction (c.V W) (actZ Dw)) σ
  let pr := Submodule.linearProjOfIsCompl K Q hQ
  let f : Ind Dw τ.1 → (c.V W ⊗[ℤ] Dw.La →ₗ[c.V W] c.V W) := fun i => (b.coord i).comp pr
  have hf : ∀ i j, f i (b j) = if i = j then 1 else 0 := by
    intro i j
    show b.coord i (pr (b j)) = _
    rw [show pr (b j) = b j from Submodule.linearProjOfIsCompl_apply_left hQ (b j), Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply]
    simp [eq_comm]
  choose y hy using fun m' : Fin N => Dw.unimod.2 (a.coord m')
  let cc : Fin N → Fin N → ℤ := fun m' m => a.repr (y m') m
  have hcc : ∀ m' k, ∑ m, cc m' m * Dw.EF (a m) (a k) = if m' = k then 1 else 0 := by
    intro m' k
    have h0 : Dw.EF (y m') (a k) = ∑ m, cc m' m * Dw.EF (a m) (a k) := by
      calc Dw.EF (y m') (a k) = Dw.EF (∑ m, a.repr (y m') m • a m) (a k) := by rw [a.sum_repr]
        _ = ∑ m, cc m' m * Dw.EF (a m) (a k) := by
          simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, cc]
    rw [← h0, hy, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    simp [eq_comm]
  let tb := Algebra.TensorProduct.basis (c.V W) a
  let T : Ind Dw τ.1 → Fin N → c.V W := fun j m => tb.repr (b j : c.V W ⊗[ℤ] Dw.La) m
  let S : Ind Dw τ.1 → Fin N → c.V W := fun i m => ∑ m', f i (1 ⊗ₜ a m') * (cc m' m : c.V W)
  have hT : ∀ j, ∑ m, T j m ⊗ₜ[ℤ] a m = (b j : c.V W ⊗[ℤ] Dw.La) := by
    intro j
    conv_rhs => rw [← tb.sum_repr (b j : c.V W ⊗[ℤ] Dw.La)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  have hS : ∀ i k, ∑ m, S i m * ((Dw.EF (a m) (a k) : ℤ) : c.V W) = f i (1 ⊗ₜ a k) := by
    intro i k
    simp only [S, Finset.sum_mul]
    rw [Finset.sum_comm]
    have e : ∀ m', ∑ m, f i (1 ⊗ₜ a m') * (cc m' m : c.V W) * ((Dw.EF (a m) (a k) : ℤ) : c.V W)
        = f i (1 ⊗ₜ a m') * (if m' = k then 1 else 0) := by
      intro m'
      have h2 := congrArg (fun z : ℤ => (z : c.V W)) (hcc m' k)
      simp only [Int.cast_sum, Int.cast_mul] at h2
      simp_rw [_root_.mul_assoc, ← Finset.mul_sum, h2]
      split_ifs <;> simp
    simp_rw [e, mul_ite, _root_.mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine ⟨N, a, T, S, ?_, ?_, ?_⟩
  · intro i o
    have hm := EigenSplit.mem_eigenSub.1 (b i).2 o
    rw [EigenSplit.baseChangeAction_apply, actZ_apply] at hm
    have e1 : ∑ m, T i m ⊗ₜ[ℤ] (o • a m)
        = ((LinearMap.lsmul (𝓞 E) Dw.La o).restrictScalars ℤ).baseChange (c.V W) (∑ m, T i m ⊗ₜ[ℤ] a m) := by
      simp [map_sum, LinearMap.baseChange_tmul]
    rw [e1, hT, hm, ← hT, Finset.smul_sum]
    simp [TensorProduct.smul_tmul', smul_eq_mul]
  · intro i j
    have e2 : ∑ m, ∑ m', S i m * T j m' * ((Dw.EF (a m) (a m') : ℤ) : c.V W) = f i (b j) := by
      rw [Finset.sum_comm]
      simp_rw [mul_comm (S i _) (T j _), _root_.mul_assoc, ← Finset.mul_sum, hS]
      rw [← hT j, map_sum]
      refine Finset.sum_congr rfl fun m' _ => ?_
      have e3 : T j m' ⊗ₜ[ℤ] a m' = T j m' • ((1 : c.V W) ⊗ₜ[ℤ] a m') := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [e3, map_smul, smul_eq_mul]
    rw [e2, hf]
  · intro x hx
    have hxK : x ∈ K := EigenSplit.mem_eigenSub.2 fun o => by
      rw [EigenSplit.baseChangeAction_apply, actZ_apply]; exact hx o
    have e' : x = ∑ i, b.repr ⟨x, hxK⟩ i • (b i : c.V W ⊗[ℤ] Dw.La) := by
      conv_lhs => rw [show x = ((⟨x, hxK⟩ : K) : c.V W ⊗[ℤ] Dw.La) from rfl, ← b.sum_repr ⟨x, hxK⟩]
      simp only [Submodule.coe_sum, Submodule.coe_smul]
    rw [e']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hT i⟩)

end GlobalTheory.FlatModel.LatDual
end
end

open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_statement_holds : LatSt := by
  atlas_forward_decl GlobalTheory.FlatModel.LatDual.latSt
end

section
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparison_statement_holds : CmpSt := by
  first | exact @GlobalTheory.FlatModel.cmpSt_holds | exact GlobalTheory.FlatModel.cmpSt_holds | (intros; apply GlobalTheory.FlatModel.cmpSt_holds <;> assumption)
end

section
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existence_of_comparison : CmpSt → ExSt := by
  first | exact @GlobalTheory.FlatModel.exSt_of_cmpSt | exact GlobalTheory.FlatModel.exSt_of_cmpSt | (intros; apply GlobalTheory.FlatModel.exSt_of_cmpSt <;> assumption)
end

section
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.value_statement_holds : ValueSt := by
  first | exact @GlobalTheory.FlatModel.valueSt | exact GlobalTheory.FlatModel.valueSt | (intros; apply GlobalTheory.FlatModel.valueSt <;> assumption)
end

section
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bound_statement_holds : BoundSt := by
  first | exact @GlobalTheory.FlatModel.boundSt | exact GlobalTheory.FlatModel.boundSt | (intros; apply GlobalTheory.FlatModel.boundSt <;> assumption)
end

section
section
open NumberField IsDedekindDomain IsLocalRing HeightOneSpectrum

namespace GlobalTheory.CompleteDVR

theorem exists_place_le {K : Type} [Field K] [NumberField K] (W : ValuationSubring K) :
    ∃ la : HeightOneSpectrum (𝓞 K), (la.valuation K).valuationSubring ≤ W := by
  have hint : ∀ a : 𝓞 K, (a : K) ∈ W := fun a => by
    have h2 : IsIntegral W (a : K) := (RingOfIntegers.isIntegral_coe a).tower_top
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := W) (K := K)).mp h2
    rw [← hy]
    exact y.2
  let g : 𝓞 K →+* W := (algebraMap (𝓞 K) K).codRestrict W hint
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal ((IsLocalRing.maximalIdeal W).comap g)
    (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal W).ne_top)
  refine ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)⟩,
    fun a ha => ?_⟩
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer _ a ha
  have hu : IsUnit (g d) := by
    by_contra hu
    exact d.2 (hle ((IsLocalRing.mem_maximalIdeal _).2 hu))
  obtain ⟨b, hb⟩ := hu.exists_right_inv
  have hb' : algebraMap (𝓞 K) K d * (b : K) = 1 := congrArg Subtype.val hb
  have : a = algebraMap (𝓞 K) K n * (b : K) := by rw [← hnd, mul_assoc, hb', mul_one]
  rw [this]
  exact W.mul_mem _ _ (hint n) b.2

theorem ne_top_of_isDiscreteValuationRing {K : Type} [Field K] (V : ValuationSubring K)
    [IsDiscreteValuationRing V] : V ≠ ⊤ := by
  intro h
  have hall : ∀ y : K, y ∈ V := fun y => h ▸ ValuationSubring.mem_top y
  apply IsDiscreteValuationRing.not_a_field V
  ext x
  simp only [Ideal.mem_bot]
  constructor
  · intro hx
    by_contra hne
    have hne' : (x : K) ≠ 0 := fun h0 => hne (Subtype.ext h0)
    apply (IsLocalRing.mem_maximalIdeal x).1 hx
    refine IsUnit.of_mul_eq_one ⟨(x : K)⁻¹, hall _⟩ (Subtype.ext ?_)
    simp [hne']
  · rintro rfl
    exact Ideal.zero_mem _

theorem exists_complete : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V],
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (φ : V →+* O),
      Function.Injective φ ∧ IsLocalHom φ := by
  intro F _ _ V _
  obtain ⟨la, hla⟩ := exists_place_le V
  have hV : (la.valuation F).valuationSubring = V :=
    ValuationSubring.eq_of_le_of_ne_top _ hla (ne_top_of_isDiscreteValuationRing V)
  subst hV
  have hc : IsAdicComplete (maximalIdeal (la.adicCompletionIntegers F)) (la.adicCompletionIntegers F) := by
    refine NormIntegers.isAdicComplete_of_fg (C := la.adicCompletion F) ⟨?_, ?_, ?_⟩
      (IsNoetherian.noetherian _) (maximalIdeal.isMaximal _).ne_top
    · exact FaithfulSMul.algebraMap_injective _ _
    · intro x
      have : ‖(x : la.adicCompletion F)‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 x.2
      exact_mod_cast this
    · intro x hx
      have : ‖x‖ ≤ 1 := by exact_mod_cast hx
      exact ⟨⟨x, Valued.toNormedField.norm_le_one_iff.1 this⟩, rfl⟩
  let φ : (la.valuation F).valuationSubring →+* la.adicCompletionIntegers F :=
    ((FinitePlace.embedding la).comp (la.valuation F).valuationSubring.subtype).codRestrict _ (fun x => by
      rw [RingHom.comp_apply, mem_adicCompletionIntegers, ValuationSubring.coe_subtype,
        FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation']
      exact (Valuation.mem_valuationSubring_iff _ _).1 x.2)
  refine ⟨la.adicCompletionIntegers F, inferInstance, inferInstance, inferInstance, hc, φ, ?_, ?_⟩
  · intro a b h
    exact Subtype.ext ((FinitePlace.embedding la).injective (congrArg Subtype.val h))
  · refine ⟨fun a ha => ?_⟩
    rw [adicCompletionIntegers.isUnit_iff_valued_eq_one] at ha
    have h1 : la.valuation F (a : F) = 1 := by
      rw [← valuedAdicCompletion_eq_valuation']
      exact ha
    exact (Valuation.valuationSubring.integers (la.valuation F)).isUnit_iff_valuation_eq_one.2 h1

end GlobalTheory.CompleteDVR
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complete_dvr_extension : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V], ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (φ : V →+* O), Function.Injective φ ∧ IsLocalHom φ := by
  atlas_forward_decl GlobalTheory.CompleteDVR.exists_complete
end

section
section
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem flat_injective_dvr {V O : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing O] [IsDomain O]
    (φ : V →+* O) (hφ : Function.Injective φ) : Flat (Spec.map (CommRingCat.ofHom φ)) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  change φ.Flat
  algebraize [φ]
  change Module.Flat V O
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
  rintro t ⟨⟨a, ha⟩, ht⟩
  have h1 : φ a * t = 0 := ht
  rcases mul_eq_zero.1 h1 with h | h
  · exact absurd (hφ (h.trans (map_zero φ).symm)) (nonZeroDivisors.ne_zero ha)
  · exact h

theorem connected_pullback_of_geomIrr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (O : Type)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (φ : V →+* O) (hφ : Function.Injective φ)
    (_hloc : IsLocalHom φ) (X : Scheme.{0}) (s : X ⟶ Spec (.of V)) (Xw : X.Opens) (hX : IsIntegral X) (hs : Flat s)
    (hg : GeomIrr s Xw) : ConnectedSpace ↑(pullback s (Spec.map (CommRingCat.ofHom φ))) := by
  set K := FractionRing O
  set φ' := Spec.map (CommRingCat.ofHom φ)
  set ι' : Spec (.of K) ⟶ Spec (.of O) := Spec.map (CommRingCat.ofHom (algebraMap O K))
  set f : V →+* K := (algebraMap O K).comp φ
  have hf : Function.Injective f := (IsFractionRing.injective O K).comp hφ
  have hfe : spMap f = ι' ≫ φ' := by
    simp only [spMap, ι', φ', f, ← Spec.map_comp]
    rfl
  haveI hWi := hg K f hf
  set Wk := pullback (Xw.ι ≫ s) (spMap f)

  let m : Wk ⟶ pullback s φ' := pullback.lift (pullback.fst _ _ ≫ Xw.ι) (pullback.snd _ _ ≫ ι') (by
    simp only [Category.assoc]
    rw [← hfe]
    exact pullback.condition)
  haveI : Flat φ' := flat_injective_dvr φ hφ
  have gfst : GeneralizingMap (pullback.fst s φ') := by
    exact Flat.generalizingMap _
  have gsnd : GeneralizingMap (pullback.snd s φ') := by
    exact Flat.generalizingMap _

  haveI : IrreducibleSpace X := inferInstance
  set η := genericPoint X
  obtain ⟨w₀⟩ := (inferInstance : Nonempty Wk)
  have hη : η ∈ Xw := by
    exact ((genericPoint_spec X).mem_open_set_iff Xw.isOpen).2
      ⟨_, trivial, (pullback.fst (Xw.ι ≫ s) (spMap f) w₀).2⟩
  have key : ∀ x : ↥(pullback s φ'), x ∈ closure (Set.range m) := by
    intro x
    obtain ⟨x₁, hx₁, hx₁s⟩ := gsnd (b := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O)) (a := x)
      ((PrimeSpectrum.le_iff_specializes _ _).1 bot_le)
    obtain ⟨x₂, hx₂, hx₂f⟩ := gfst (genericPoint_specializes (pullback.fst s φ' x₁))
    have hs₂ : pullback.snd s φ' x₂ = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) := by
      have := (hx₂.map (pullback.snd s φ').continuous)
      rw [hx₁s] at this
      exact PrimeSpectrum.ext (le_bot_iff.1 ((PrimeSpectrum.le_iff_specializes _ _).2 this))

    have hι : ι' (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) := by
      have := bot_map (X := Spec (.of O)) (IsFractionRing.injective O K) (𝟙 _)
      exact this
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd s φ') (g := ι') x₂
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) (by rw [hs₂, hι])
    obtain ⟨y, hy₁, hy₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := Xw.ι)
      (g := pullback.fst (pullback.snd s φ') ι' ≫ pullback.fst s φ') ⟨η, hη⟩ z
      (by rw [Scheme.Hom.comp_apply, hz₁, hx₂f]; rfl)
    let h : pullback Xw.ι (pullback.fst (pullback.snd s φ') ι' ≫ pullback.fst s φ') ⟶ Wk :=
      pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd _ _) (by
        simp only [Category.assoc]
        rw [pullback.condition_assoc, Category.assoc, pullback.condition, pullback.condition_assoc, hfe])
    have hm : h ≫ m = pullback.snd _ _ ≫ pullback.fst (pullback.snd s φ') ι' := by
      apply pullback.hom_ext
      · simp only [Category.assoc, m, h, pullback.lift_fst, pullback.lift_fst_assoc]
        rw [pullback.condition]
      · simp only [Category.assoc, m, h, pullback.lift_snd, pullback.lift_snd_assoc]
        rw [pullback.condition]
    have hx₂m : x₂ ∈ Set.range m := ⟨h y, by
      rw [← Scheme.Hom.comp_apply, hm, Scheme.Hom.comp_apply, hy₂, hz₁]⟩
    exact closure_mono (Set.singleton_subset_iff.2 hx₂m) (hx₂.trans hx₁).mem_closure
  have hirr : IsIrreducible (Set.range m) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ Wk).image _ m.continuous.continuousOn
  have : IrreducibleSpace ↑(pullback s φ') := by
    have hcl := hirr.closure
    rw [Set.eq_univ_of_forall key] at hcl
    exact (irreducibleSpace_def _).2 hcl
  infer_instance

end GlobalTheory.FlatModel
end

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_change_complete_connected : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (φ : V →+* O), Function.Injective φ → IsLocalHom φ → ∀ (X : Scheme.{0}) (s : X ⟶ Spec (.of V)) (Xw : X.Opens), IsIntegral X → Flat s → GeomIrr s Xw → ConnectedSpace ↑(pullback s (Spec.map (CommRingCat.ofHom φ))) := by
  atlas_forward_decl GlobalTheory.FlatModel.connected_pullback_of_geomIrr
end

section
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_fibre_connected_of_proper : GlobalTheory.Published.FormalAlgebraisation.Morphisms → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Y : Scheme.{0}) (f : Y ⟶ Spec (.of O)), IsProper f → ConnectedSpace ↑Y → ConnectedSpace ↑(GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre f) := by
  first | exact @GlobalTheory.AlgConn.connectedSpace_specialFibre_of_morphisms | exact GlobalTheory.AlgConn.connectedSpace_specialFibre_of_morphisms | (intros; apply GlobalTheory.AlgConn.connectedSpace_specialFibre_of_morphisms <;> assumption)
end

section
section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.FibSurj

open IsLocalRing

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (φ : V →+* O) [IsLocalHom φ]
  {X : Scheme.{0}} (s : X ⟶ Spec (.of V))

theorem spec_square :
    Spec.map (CommRingCat.ofHom (residue O)) ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom (ResidueField.map φ)) ≫ Spec.map (CommRingCat.ofHom (residue V)) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2

noncomputable def fibMap :
    pullback (pullback.snd s (Spec.map (CommRingCat.ofHom φ))) (Spec.map (CommRingCat.ofHom (residue O))) ⟶
      pullback s (Spec.map (CommRingCat.ofHom (residue V))) :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (ResidueField.map φ))) (by
      simp only [Category.assoc]
      rw [← spec_square, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc])

theorem fibMap_fst : fibMap φ s ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ :=
  pullback.lift_fst _ _ _

theorem fibMap_snd : fibMap φ s ≫ pullback.snd _ _ =
    pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (ResidueField.map φ)) :=
  pullback.lift_snd _ _ _

theorem fibMap_isPullback :
    IsPullback (fibMap φ s) (pullback.snd _ _) (pullback.snd _ _)
      (Spec.map (CommRingCat.ofHom (ResidueField.map φ))) := by
  have hL := IsPullback.of_hasPullback (pullback.snd s (Spec.map (CommRingCat.ofHom φ)))
    (Spec.map (CommRingCat.ofHom (residue O)))
  have hR := IsPullback.of_hasPullback s (Spec.map (CommRingCat.ofHom φ))
  have hOut := hL.paste_horiz hR
  rw [← fibMap_fst, spec_square] at hOut
  exact IsPullback.of_right hOut (fibMap_snd φ s) (IsPullback.of_hasPullback _ _)

theorem fibMap_surjective : Surjective (fibMap φ s) := by
  have hψ : Surjective (Spec.map (CommRingCat.ofHom (ResidueField.map φ))) := by
    constructor
    intro x
    obtain ⟨y⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of (ResidueField O))))
    exact ⟨y, Subsingleton.elim _ _⟩
  exact MorphismProperty.of_isPullback (fibMap_isPullback φ s).flip hψ

end

theorem fibre_connected_of_base_change :
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (φ : V →+* O), IsLocalHom φ → ∀ (X : Scheme.{0}) (s : X ⟶ Spec (.of V)), ConnectedSpace ↑(GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre (pullback.snd s (Spec.map (CommRingCat.ofHom φ)))) → ConnectedSpace ↑(GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre s) := by
  intro V _ _ _ O _ _ _ φ hφ X s hc
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre at hc ⊢
  exact (fibMap_surjective φ s).surj.connectedSpace (fibMap φ s).continuous

end GlobalTheory.FibSurj
end

open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_fibre_connected_of_base_change : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (φ : V →+* O), IsLocalHom φ → ∀ (X : Scheme.{0}) (s : X ⟶ Spec (.of V)), ConnectedSpace ↑(GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre (pullback.snd s (Spec.map (CommRingCat.ofHom φ)))) → ConnectedSpace ↑(GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre s) := by
  atlas_forward_decl GlobalTheory.FibSurj.fibre_connected_of_base_change
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem connected_of_hypotheses (hP : GlobalTheory.CovTop.Hypotheses2) : ConnSt := by
  intro F _ _ V _ X s Xw hI _ hPr hF hG
  obtain ⟨O, _, _, _, _, φ, hφi, hφl⟩ := GlobalTheory.T.exists_complete_dvr_extension F V
  have hpr : IsProper s := by
    obtain ⟨N, c, hc, rfl⟩ := hPr
    have := isProper_str (↥V) N
    infer_instance
  have hc := GlobalTheory.T.base_change_complete_connected V O φ hφi hφl X s Xw hI hF hG
  have hsp := GlobalTheory.T.special_fibre_connected_of_proper hP.q18.1 O (pullback s (Spec.map (CommRingCat.ofHom φ))) (pullback.snd _ _) inferInstance hc
  exact GlobalTheory.T.special_fibre_connected_of_base_change V O φ hφl X s hsp

end GlobalTheory.FlatModel
end
end

open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connectedness_statement_holds : GlobalTheory.CovTop.Hypotheses2 → ConnSt := by
  atlas_forward_decl GlobalTheory.FlatModel.connected_of_hypotheses
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem exists_alg_norm_eq (p : ℕ) [Fact p.Prime] (x : ℂ_[p]) (hx : x ≠ 0) :
    ∃ a : PadicAlgCl p, ‖(a : ℂ_[p])‖ = ‖x‖ := by
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  obtain ⟨a, ha⟩ := (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl p)).exists_dist_lt x hpos
  refine ⟨a, ?_⟩
  rw [dist_eq_norm] at ha
  have h1 : ‖(a : ℂ_[p])‖ ≤ max ‖x‖ ‖x - (a : ℂ_[p])‖ := by
    have := IsUltrametricDist.norm_add_le_max x (-(x - (a : ℂ_[p])))
    rwa [norm_neg, show x + -(x - (a : ℂ_[p])) = (a : ℂ_[p]) by ring] at this
  have h2 : ‖x‖ ≤ max ‖(a : ℂ_[p])‖ ‖x - (a : ℂ_[p])‖ := by
    have := IsUltrametricDist.norm_add_le_max (a : ℂ_[p]) (x - (a : ℂ_[p]))
    rwa [show (a : ℂ_[p]) + (x - (a : ℂ_[p])) = x by ring] at this
  rw [max_eq_left ha.le] at h1
  refine le_antisymm h1 ?_
  rcases le_max_iff.1 h2 with h | h
  · exact h
  · exact absurd h (not_le.2 ha)

theorem norm_unit_int (p : ℕ) [Fact p.Prime] {u : 𝓞_ℂ_[p]} (hu : IsUnit u) : ‖(u : ℂ_[p])‖ = 1 := by
  rw [← coe_valued]
  have := (PadicComplexInt.integers p).one_of_isUnit hu
  exact_mod_cast this

theorem norm_eq_unif_pow (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) (φ : O →+* 𝓞_ℂ_[p]) {n : O} (hn : n ≠ 0) :
    ∃ m : ℕ, ‖((φ n : 𝓞_ℂ_[p]) : ℂ_[p])‖ = ‖((φ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖ ^ m := by
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hn hϖ
  refine ⟨m, ?_⟩
  rw [map_mul, map_pow, Subring.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow,
    norm_unit_int p ((Units.isUnit u).map φ), _root_.one_mul]

theorem exists_frac_model (p : ℕ) [Fact p.Prime] (a : PadicAlgCl p) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (φ : O →+* 𝓞_ℂ_[p]) (n d : O),
      Function.Injective φ ∧ IsLocalHom φ ∧ d ≠ 0 ∧
        ((φ n : 𝓞_ℂ_[p]) : ℂ_[p]) = (a : ℂ_[p]) * ((φ d : 𝓞_ℂ_[p]) : ℂ_[p]) := by
  let L := IntermediateField.adjoin ℚ_[p] ({a} : Set (PadicAlgCl p))
  haveI : FiniteDimensional ℚ_[p] L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  obtain ⟨W, _, _, _, _, _, _, _, hc, hfin, -, -, -, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension ℤ_[p] ℚ_[p] L
  let φ₀ : W →+* ℂ_[p] :=
    (algebraMap (PadicAlgCl p) ℂ_[p]).comp (L.val.toRingHom.comp (algebraMap W L))
  have hcomp : (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (padicIntHom p) = φ₀.comp (algebraMap ℤ_[p] W) := by
    ext z
    have h1 := congrArg (fun g => g z) hc
    simp only [RingHom.comp_apply] at h1
    simp only [RingHom.comp_apply, φ₀, h1]
    rfl
  have hint : ∀ b : W, φ₀ b ∈ 𝓞_ℂ_[p] := by
    intro b
    haveI : Algebra.IsIntegral ℤ_[p] W := Algebra.IsIntegral.of_finite ℤ_[p] W
    have h1 : IsIntegral 𝓞_ℂ_[p] (φ₀ b) :=
      IsIntegral.map_of_comp_eq (padicIntHom p) φ₀ hcomp (Algebra.IsIntegral.isIntegral b)
    exact (PadicComplexInt.integers p).mem_of_integral h1
  let φ : W →+* 𝓞_ℂ_[p] := φ₀.codRestrict 𝓞_ℂ_[p] hint
  have hinj0 : Function.Injective φ₀ :=
    (algebraMap (PadicAlgCl p) ℂ_[p]).injective.comp
      (Subtype.val_injective.comp (IsFractionRing.injective W L))
  have hinj : Function.Injective φ := fun b c h => hinj0 (congrArg Subtype.val h)
  have hle : ∀ u : 𝓞_ℂ_[p], ‖(u : ℂ_[p])‖ ≤ 1 := fun u => by
    rw [← coe_valued]
    exact_mod_cast u.2
  have hpn : ‖((φ ((p : ℕ) : W) : 𝓞_ℂ_[p]) : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [map_natCast]
    rw [show (((p : ℕ) : 𝓞_ℂ_[p]) : ℂ_[p]) = ((p : ℕ) : ℂ_[p]) from map_natCast (algebraMap 𝓞_ℂ_[p] ℂ_[p]) p]
    rw [← coe_valued, PadicComplex.valuation_p]
    simp
  have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.2 (Fact.out : p.Prime).pos)
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have hloc : IsLocalHom φ := by
    refine ⟨fun b hb => ?_⟩
    by_contra hnb
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
    have hp0 : ((p : ℕ) : W) ≠ 0 := fun h => by
      rw [h, map_zero] at hpn
      simp only [ZeroMemClass.coe_zero, norm_zero] at hpn
      exact hpos.ne hpn
    obtain ⟨e, he⟩ := norm_eq_unif_pow p hϖ φ hp0
    have hϖ1 : ‖((φ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖ < 1 := by
      refine lt_of_le_of_ne (hle _) fun h => ?_
      rw [h, one_pow, hpn] at he
      exact hp1.ne he
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [map_zero] at hb
      exact not_isUnit_zero hb
    obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
    have hm : m ≠ 0 := by
      rintro rfl
      exact hnb (by rw [pow_zero, _root_.mul_one]; exact u.isUnit)
    have h1 := norm_unit_int p hb
    rw [map_mul, map_pow, Subring.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow,
      norm_unit_int p ((Units.isUnit u).map φ), _root_.one_mul] at h1
    have h2 : ‖((φ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖ ^ m ≤ ‖((φ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖ :=
      pow_le_of_le_one (norm_nonneg _) (hle _) hm
    linarith
  let a' : L := ⟨a, IntermediateField.mem_adjoin_simple_self ℚ_[p] a⟩
  obtain ⟨n, d, hd, hnd⟩ := IsFractionRing.div_surjective (A := W) a'
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hdL : algebraMap W L d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective W L)).2 hd0
  have e1 : algebraMap W L n = a' * algebraMap W L d := by rw [← hnd, div_mul_cancel₀ _ hdL]
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, φ, n, d, hinj, hloc, hd0, ?_⟩
  have e2 := congrArg (fun z : L => algebraMap (PadicAlgCl p) ℂ_[p] (z : PadicAlgCl p)) e1
  simp only [MulMemClass.coe_mul, map_mul] at e2
  exact e2

theorem exists_unif_norm (p : ℕ) [Fact p.Prime] (x : ℂ_[p]) (hx : x ≠ 0) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (ϖ : O) (_ : Irreducible ϖ)
      (φ : O →+* 𝓞_ℂ_[p]) (k : ℤ),
      Function.Injective φ ∧ IsLocalHom φ ∧ ‖((φ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖ ^ k = ‖x‖ := by
  obtain ⟨a, ha⟩ := exists_alg_norm_eq p x hx
  obtain ⟨O, _, _, _, _, φ, n, d, hinj, hloc, hd, hnd⟩ := exists_frac_model p a
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hne : ∀ b : O, b ≠ 0 → ((φ b : 𝓞_ℂ_[p]) : ℂ_[p]) ≠ 0 := fun b hb h =>
    hb (hinj (by rw [map_zero]; exact Subtype.ext h))
  have hxa : (a : ℂ_[p]) ≠ 0 := fun h => hx (norm_eq_zero.1 (ha ▸ (norm_eq_zero.2 h)))
  have hn : n ≠ 0 := by
    rintro rfl
    rw [map_zero, ZeroMemClass.coe_zero] at hnd
    exact mul_ne_zero hxa (hne d hd) hnd.symm
  obtain ⟨m₁, h₁⟩ := norm_eq_unif_pow p hϖ φ hn
  obtain ⟨m₂, h₂⟩ := norm_eq_unif_pow p hϖ φ hd
  have hϖ0 : ‖((φ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖ ≠ 0 := norm_ne_zero_iff.2 (hne ϖ hϖ.ne_zero)
  refine ⟨O, inferInstance, inferInstance, inferInstance, inferInstance, ϖ, hϖ, φ, (m₁ : ℤ) - m₂,
    hinj, hloc, ?_⟩
  have e := congrArg norm hnd
  rw [norm_mul, h₁, h₂, ha] at e
  rw [zpow_sub₀ hϖ0, zpow_natCast, zpow_natCast, e, mul_div_cancel_right₀ _ (pow_ne_zero _ hϖ0)]

end GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

open GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.ValConstOfPowEq in

theorem packSt : PackSt := by
  intro p _ x hx
  obtain ⟨O, _, _, _, _, ϖ, hϖ, φ, k, hinj, hloc, hk⟩ := exists_unif_norm p x hx
  obtain ⟨hI, hN, hP, hF, -, hD, ht⟩ := hyp_spec O
  let f : Spec (.of O) ⟶ Spec (.of O) := 𝟙 _
  let D := trivLB (Spec (.of O))
  let sig : (D.pull (genericι f)).Gen :=
    ⟨fun _ => res le_top (constUnit (genericStr f) (unifUnit ϖ hϖ ^ k))⟩
  have hsig : sig.IsGen := by
    intro i j
    rw [show (D.pull (genericι f)).g i j = 1 from linComb_g_one D (fun _ _ => rfl) _ _ i j, _root_.one_mul]
    exact (res_res' _ _ _).trans (res_res' _ _ _).symm
  have hg : Function.Injective ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ) :=
    (IsFractionRing.injective 𝓞_ℂ_[p] ℂ_[p]).comp hinj
  let ψ : FractionRing O →+* ℂ_[p] := IsFractionRing.lift hg
  let ybar : Spec (.of 𝓞_ℂ_[p]) ⟶ Spec (.of O) := Spec.map (CommRingCat.ofHom φ)
  have hw : (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ ybar) ≫ f =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O))) := by
    simp only [f, ybar, Category.comp_id, ← Spec.map_comp]
    congr 1
    ext a
    simp [ψ, IsFractionRing.lift_algebraMap]
  let y : Spec (.of ℂ_[p]) ⟶ genericFibre f := pullback.lift _ _ hw
  have hy : y ≫ genericι f = Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ ybar :=
    pullback.lift_fst _ _ _
  have hj₀ : ybar ⁻¹ᵁ D.U PUnit.unit = ⊤ := by simp [D, trivLB]
  have htop := top_le_generic D ybar y hy PUnit.unit hj₀
  let cc : ℂ_[p]ˣ := Units.map (Scheme.ΓSpecIso (.of ℂ_[p])).hom.hom.toMonoidHom
    (res htop (pullU y _ (sig.s (fun _ => PUnit.unit))))
  have hcc : (cc : ℂ_[p]) = (algebraMap 𝓞_ℂ_[p] ℂ_[p] (φ ϖ)) ^ k := by
    have e0 : constUnit (genericStr f) (unifUnit ϖ hϖ ^ k) = constUnit (genericStr f) (unifUnit ϖ hϖ) ^ k := by
      simp only [constUnit, map_zpow]
    have e1 : res htop (pullU y _ (sig.s (fun _ => PUnit.unit))) =
        (res (le_top : ⊤ ≤ y ⁻¹ᵁ ⊤) (pullU y ⊤ (constUnit (genericStr f) (unifUnit ϖ hϖ)))) ^ k := by
      show res htop (pullU y _ (res le_top (constUnit (genericStr f) (unifUnit ϖ hϖ ^ k)))) = _
      rw [res_pullU_res', e0, map_zpow, map_zpow]
      all_goals rfl
    show ((Units.map (Scheme.ΓSpecIso (.of ℂ_[p])).hom.hom.toMonoidHom
      (res htop (pullU y _ (sig.s (fun _ => PUnit.unit)))) : ℂ_[p]ˣ) : ℂ_[p]) = _
    rw [e1, map_zpow, Units.val_zpow_eq_zpow_val]
    congr 1
    exact eval_constUnit ϖ hϖ φ ybar (Category.comp_id _) y hy le_top
  refine ⟨O, inferInstance, inferInstance, inferInstance, inferInstance, ϖ, hϖ, Spec (.of O), f, D,
    hI, hN, hP, hF, hD, ht, sig, hsig, φ, hinj, hloc, ybar, y, chartGen D ybar PUnit.unit hj₀, cc,
    Category.comp_id _, hy, chartGen_isGen D hD ybar PUnit.unit hj₀,
    isCoord_chartGen D sig hsig ybar y hy PUnit.unit hj₀, ?_⟩
  rw [hcc, norm_zpow, ← hk]
  rfl

end GlobalTheory.FlatModel
end
end

open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.packing_statement_holds : PackSt := by
  atlas_forward_decl GlobalTheory.FlatModel.packSt
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Local

variable {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} {W : ValuationSubring ℂ}
  {Y : Model Xo' c' (c'.V W).subtype} {r : Xo'.XF c' ⟶ Xo.XF c} {ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)}
  {hle : c.F ≤ c'.F} {r₀ : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀} {x : ℝ} {Z : Comp Xo c} {τ : Psi H}
  {la : HeightOneSpectrum (𝓞 c.F)} {p : ℕ} [Fact p.Prime] {Xw : Y.X.Opens}

theorem exists_unit (hG : GenSt) (hL : Laws U x) (s : ArchSec U x Z (flatWt Dw τ)) (hc : IsCover Y r hle Z la p Xw)
    {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] {ξ : Sp R ⟶ Y.X} [IsOpenImmersion ξ] {β : c'.V W →+* R}
    (hβ : ξ ≫ Y.s = spMap β) (hξ : ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ Xw) {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ Y.t.G.left)} (he : IsTanBasis Y.t ξ e) {U₁ U₂ : Fin g → Fin g → R}
    (h₁ : EigFam Y.t ξ (β.comp (embV c' W τ.1)) e U₁) (h₂ : EigFam Y.t ξ (β.comp (embV c' W (conjEmb τ.1))) e U₂)
    (K₁ : Fin (Dw.mult τ.1) → Fin g) (K₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g) (a₁ : Fin (Dw.mult τ.1) → Fin g → R)
    (a₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → R) (ε : ℤˣ) :
    ∃ u : (Localization.Away ((p : R) * (pairDet a₁ (U₁ ∘ K₁) * pairDet a₂ (U₂ ∘ K₂))))ˣ,
      ∀ (k : Type) [Field k] [Algebra c.F k] (ψ : Localization.Away ((p : R) * (pairDet a₁ (U₁ ∘ K₁) * pairDet a₂ (U₂ ∘ K₂))) →+* k) (yy : Sp k ⟶ Xo'.XF c'),
        yy ≫ Y.j = spMap (ψ.comp (algebraMap R _)) ≫ ξ → ∃ fv : k,
          GVal Y r ν τ.1 s.sig yy (bcV Y.t (ψ.comp (algebraMap R _)) e) (fun i b => ψ (algebraMap R _ (U₁ (K₁ i) b)))
            (fun i b => ψ (algebraMap R _ (U₂ (K₂ i) b))) fv ∧
          ψ u = fv * ((ε : ℤ) : k) * ψ (algebraMap R _ (pairDet a₁ (U₁ ∘ K₁))) / ψ (algebraMap R _ (pairDet a₂ (U₂ ∘ K₂))) := by
  set q : R := (p : R) * (pairDet a₁ (U₁ ∘ K₁) * pairDet a₂ (U₂ ∘ K₂)) with hq
  have hu : IsUnit (algebraMap R (Localization.Away q) q) := IsLocalization.Away.algebraMap_isUnit q
  by_cases h0 : q = 0
  · refine ⟨1, fun k _ _ ψ _ _ => ?_⟩
    have := hu.map ψ
    rw [show algebraMap R (Localization.Away q) q = 0 from (congrArg _ h0).trans (map_zero _), map_zero] at this
    exact absurd this not_isUnit_zero
  have hle' : Submonoid.powers q ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors h0
  haveI : IsDomain (Localization.Away q) := IsLocalization.isDomain_localization hle'
  haveI : IsIntegrallyClosed (Localization.Away q) := isIntegrallyClosed_of_isLocalization _ _ hle'
  have hinj : Function.Injective (algebraMap R (Localization.Away q)) := IsLocalization.injective _ hle'
  let ρ := algebraMap R (Localization.Away q)
  have hu' : IsUnit ((p : Localization.Away q) * (ρ (pairDet a₁ (U₁ ∘ K₁)) * ρ (pairDet a₂ (U₂ ∘ K₂)))) := by
    rw [← map_natCast ρ, ← map_mul, ← map_mul]; exact hu
  have u₁ := isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right hu')
  have u₂ := isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right hu')
  have mp : ∀ {m : ℕ} (a V : Fin m → Fin g → R), ρ (pairDet a V) = pairDet (fun i b => ρ (a i b)) fun i b => ρ (V i b) :=
    fun a V => by
      rw [pairDet, pairDet, RingHom.map_det]
      congr 1
      ext i j
      simp [map_sum]
  haveI : IsOpenImmersion (spMap ρ) := IsOpenImmersion.of_isLocalization q
  obtain ⟨f, hf⟩ := hG E H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw Fact.out hc (Localization.Away q)
    (spMap ρ ≫ ξ) (ρ.comp β) inferInstance (by rw [Category.assoc, hβ, spMap_spMap]) (isUnit_of_mul_isUnit_left hu')
    (by rw [bot_map hinj]; exact hξ) g (bcV Y.t ρ e) (fun i b => ρ (U₁ (K₁ i) b)) (fun i b => ρ (a₁ i b))
    (fun i b => ρ (U₂ (K₂ i) b)) (fun i b => ρ (a₂ i b)) (isTanBasis_bc he ρ)
    (fun S _ φ => by
      rw [sp_sp, bcV_bcV]
      exact ⟨fun i => (h₁ S (φ.comp ρ)).1 (K₁ i), fun i => (h₂ S (φ.comp ρ)).1 (K₂ i)⟩)
    (mp a₁ _ ▸ u₁) (mp a₂ _ ▸ u₂)
  refine ⟨f * Units.map (Int.castRingHom _).toMonoidHom ε * u₁.unit * u₂.unit⁻¹, fun k _ _ ψ yy hy => ⟨ψ f, ?_, ?_⟩⟩
  · have := hf k ψ yy (by rw [sp_sp]; exact hy)
    rwa [bcV_bcV] at this
  · rw [eq_div_iff (u₂.map ψ).ne_zero, ← map_mul]
    change ψ (_ * (u₂.unit : Localization.Away q)) = _
    rw [← Units.val_mul, inv_mul_cancel_right]
    simp [ρ]

end Local

section Charts

variable {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} {W : ValuationSubring ℂ}
  {Y : Model Xo' c' (c'.V W).subtype} {r : Xo'.XF c' ⟶ Xo.XF c} {ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)}
  {hle : c.F ≤ c'.F} {r₀ : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀} {x : ℝ} {Z : Comp Xo c} {τ : Psi H}
  {la : HeightOneSpectrum (𝓞 c.F)} {p : ℕ} [Fact p.Prime] {Xw : Y.X.Opens} [StarRing (𝓞 E)]

variable (Y r ν) in

def kapSet (τ : E →+* ℂ) (f : Rul Xo c) (n : ℕ) {N : ℕ} (a : Fin N → Dw.La) (T S : Ind Dw τ → Fin N → c'.V W)
    (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) : Set ℂ_[p] :=
  {κ | ∃ (_ : Algebra c.F ℂ_[p]) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left)
    (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ ∧ KapSpec Y r ν τ f n a T S yb yy P π ψ κ}

theorem chartAt (hC : ChartSt) (hP : ProjSt) (hT : HTLocSt) (hG : GenSt) (hs : ∀ a : 𝓞 E, star a = H.bar a)
    (hL : Laws U x) (s : ArchSec U x Z (flatWt Dw τ)) (hc : IsCover Y r hle Z la p Xw) {n : ℕ} (hn : l'.A = p ^ n)
    {N : ℕ} (a : Fin N → Dw.La) (T S : Ind Dw τ.1 → Fin N → c'.V W)
    (hK : ∀ yb, IsTest p Xw yb → (kapSet Y r ν τ.1 s.sig n a T S yb).Nonempty) {z : Y.X}
    (hz : z ∈ closure (Xw : Set Y.X)) : ChartAt p n Xw (kapSet Y r ν τ.1 s.sig n a T S) z := by
  obtain ⟨R₀, _, _, _, ξ₀, g, e₀, hξ₀, ⟨z₀, rfl⟩, he₀⟩ := hC E H Dw l' Xo' c' W Y p Fact.out hc.2.2.1 z
  obtain ⟨_, ⟨z₁, rfl⟩, hz₁⟩ := mem_closure_iff.1 hz _ ξ₀.isOpenEmbedding.isOpen_range ⟨z₀, rfl⟩
  have hb₀ := bot_mem ξ₀ hz₁
  let β₀ : c'.V W →+* R₀ := (Spec.preimage (ξ₀ ≫ Y.s)).hom
  have hβ₀ : ξ₀ ≫ Y.s = spMap β₀ := (Spec.map_preimage _).symm
  obtain ⟨V₁, hV₁⟩ := hP E H l' c' W Y.X Y.t R₀ ξ₀ β₀ g e₀ he₀ τ.1
  obtain ⟨V₂, hV₂⟩ := hP E H l' c' W Y.X Y.t R₀ ξ₀ β₀ g e₀ he₀ (conjEmb τ.1)
  obtain ⟨f, h, hf, hh⟩ := hT E H Dw l' Xo' c' W Y p n hs hc.2.2.1 hn R₀ ξ₀ (hc.2.2.2.2.1 hb₀) g e₀ he₀ N a
    (PrimeSpectrum.asIdeal z₀) (PrimeSpectrum.isPrime z₀)
  have h0 : f ≠ 0 := by rintro rfl; exact hf (Ideal.zero_mem _)
  have hle' : Submonoid.powers f ≤ nonZeroDivisors R₀ := powers_le_nonZeroDivisors_of_noZeroDivisors h0
  haveI : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hle'
  haveI : IsIntegrallyClosed (Localization.Away f) := isIntegrallyClosed_of_isLocalization _ _ hle'
  have hinj : Function.Injective (algebraMap R₀ (Localization.Away f)) := IsLocalization.injective _ hle'
  let ρ := algebraMap R₀ (Localization.Away f)
  haveI : IsOpenImmersion (spMap ρ) := IsOpenImmersion.of_isLocalization f
  let U₁ : Fin g → Fin g → Localization.Away f := fun k b => ρ (V₁ k b)
  let U₂ : Fin g → Fin g → Localization.Away f := fun k b => ρ (V₂ k b)
  have hU₁ : EigFam Y.t (spMap ρ ≫ ξ₀) ((ρ.comp β₀).comp (embV c' W τ.1)) (bcV Y.t ρ e₀) U₁ := fun S _ φ => by
    rw [sp_sp, bcV_bcV]; exact hV₁ S (φ.comp ρ)
  have hU₂ : EigFam Y.t (spMap ρ ≫ ξ₀) ((ρ.comp β₀).comp (embV c' W (conjEmb τ.1))) (bcV Y.t ρ e₀) U₂ := fun S _ φ => by
    rw [sp_sp, bcV_bcV]; exact hV₂ S (φ.comp ρ)
  have hβ : (spMap ρ ≫ ξ₀) ≫ Y.s = spMap (ρ.comp β₀) := by rw [Category.assoc, hβ₀, spMap_spMap]
  have he := isTanBasis_bc he₀ ρ
  let J : Type := Equiv.Perm (Ind Dw τ.1) × (Fin (Dw.mult τ.1) → Fin g) × (Fin (Dw.mult (conjEmb τ.1)) → Fin g)
  choose u hu using fun j : J => exists_unit (ν := ν) hG hL s hc hβ (by rw [bot_map hinj]; exact hb₀) he hU₁ hU₂
    j.2.1 j.2.2 (covec (ρ.comp β₀) T h (j.1 ∘ Sum.inl)) (covec (ρ.comp β₀) S h (j.1 ∘ Sum.inr)) (Equiv.Perm.sign j.1)
  refine ⟨Localization.Away f, inferInstance, spMap ρ ≫ ξ₀, J, inferInstance, _, u, inferInstance, ?_, fun φ ht => ?_⟩
  · obtain ⟨z', hz'⟩ : z₀ ∈ Set.range (PrimeSpectrum.comap ρ) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]; exact hf
    exact ⟨z', (Scheme.Hom.comp_apply _ _ _).trans (congrArg ξ₀ hz')⟩
  have hA : ∀ {yy P π ψ}, PtOn Y (spMap φ ≫ spMap ρ ≫ ξ₀) yy P π ψ →
      HTApprox Y n yy P π ψ a (bcV Y.t φ (bcV Y.t ρ e₀)) fun m k => φ (h m k) := fun {yy P π ψ} hPt => by
    rw [bcV_bcV]
    exact hh φ yy P π ψ (by rw [← sp_sp]; exact hPt)
  have hφ : (spMap φ ≫ spMap ρ ≫ ξ₀) ≫ Y.s = spMap (φ.comp (ρ.comp β₀)) := by rw [Category.assoc, hβ, spMap_spMap]
  constructor
  · obtain ⟨κ, alg, yy, P, π, ψ, hPt, hκ⟩ := hK _ ht
    obtain ⟨⟨σ, K₁, K₂, hj⟩, -⟩ := hκ _ hφ g _ _ _ _ (isTanBasis_bc he φ) (hU₁ _ φ) (hU₂ _ φ) (hA hPt)
    refine ⟨(σ, K₁, K₂), ?_⟩
    rw [map_mul, map_pairDet_covec, map_pairDet_covec]
    exact hj
  · rintro ⟨σ, K₁, K₂⟩ hj ψ hψ κ ⟨alg, yy, P, π, ψ', hPt, hκ⟩
    obtain ⟨-, hv⟩ := hκ _ hφ g _ _ _ _ (isTanBasis_bc he φ) (hU₁ _ φ) (hU₂ _ φ) (hA hPt)
    rw [map_mul, map_pairDet_covec, map_pairDet_covec] at hj
    obtain ⟨fv, hfv, hu'⟩ := hu (σ, K₁, K₂) ℂ_[p] ψ yy (by rw [hψ, ← hPt.1, sp_sp])
    have hψ' : ∀ b, ψ (algebraMap _ _ b) = (φ b : ℂ_[p]) := fun b => RingHom.congr_fun hψ b
    simp only [hψ'] at hfv hu'
    rw [hψ, ← bcV_bcV] at hfv
    rw [hu', map_pairDet_covec, map_pairDet_covec]
    exact hv σ K₁ K₂ hj fv hfv

end Charts

section Top

variable {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} {W : ValuationSubring ℂ}
  {Y : Model Xo' c' (c'.V W).subtype} {r : Xo'.XF c' ⟶ Xo.XF c} {ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)}
  {hle : c.F ≤ c'.F} {r₀ : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀} {x : ℝ} {Z : Comp Xo c} {τ : Psi H}
  {la : HeightOneSpectrum (𝓞 c.F)} {p : ℕ} [Fact p.Prime] {Xw : Y.X.Opens}

theorem evR_ne_zero [StarRing (𝓞 E)] [Algebra c.F ℂ_[p]] (s : ArchSec U x Z (flatWt Dw τ)) (hc : IsCover Y r hle Z la p Xw)
    {yb yy} {P : PtP E p} {π ψ y} (ht : IsTest p Xw yb) (h : HTAt Y r ν yb yy P π ψ y) : evR Xo c s.sig y ≠ 0 := by
  have hZ : LiesOn Z y := fun z => by
    rw [h.2.2.1, Scheme.Hom.comp_apply]
    refine hc.2.2.2.2.2.2.1 _ (ht.2 ⟨z, ?_⟩)
    rw [h.1.1, Scheme.Hom.comp_apply]
  have h1 : evR Xo c s.sig y * evR Xo c s.inv y = 1 := by
    rw [← CompSplitPfB.cspB_evR_mul, s.mul_inv, evR_idem hZ h.2.1]
  exact left_ne_zero_of_mul_eq_one h1

theorem exists_norm (hCov : CoverSt) (hC : ChartSt) (hP : ProjSt) (hLat : LatSt) (hT : HTLocSt) (hG : GenSt) (hEx : ExSt)
    (hLift : LiftSt) (hPt : PtSt) (hGl : GlueSt) (hL : Laws U x) (s : ArchSec U x Z (flatWt Dw τ))
    (hp : (p : 𝓞 c.F) ∈ la.asIdeal) : ∃ ρ : ℝ, ∀ [Algebra c.F ℂ_[p]] (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ)
      (y₀ : IntFr Xo c T io), OverLa la T.V io e → algOn Z T io y₀ →
      ∀ (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] ℂ_[p]) (y : FrPt Xo c ℂ_[p]), IsHTFrameCp p y₀ k y →
        evR Xo c s.sig y ≠ 0 ∧ ‖evR Xo c s.sig y‖ = ρ := by
  letI := H.starRing
  have hs : ∀ a : 𝓞 E, star a = H.bar a := fun _ => rfl
  obtain ⟨n, hn⟩ := hPt E H Dw τ p hs
  obtain ⟨l', Xo', c', W, Y, r, ν, hle, Xw, hA, hc⟩ := hCov E H Dw l Xo c hL.pos hL.lev hL.good hL.geo Z la p n Fact.out hp
  obtain ⟨N, a, T, S, hTS⟩ := hLat E H Dw l' c' W p Fact.out hc.2.2.1 τ
  have hk : ∀ [Algebra c.F ℂ_[p]] {yb yy} {P : PtP E p} {π ψ y}, IsTest p Xw yb → HTAt Y r ν yb yy P π ψ y →
      ∃ κ ∈ kapSet Y r ν τ.1 s.sig n a T S yb, ‖κ‖ = ‖evR Xo c s.sig y‖ := fun {alg yb yy P π ψ y} ht h => by
    obtain ⟨κ, h1, h2⟩ := hn l l' Xo Xo' c c' W Y r ν hle hc.1 hA N a T S hTS s.sig yb yy P π ψ y h (evR_ne_zero s hc ht h)
    exact ⟨κ, ⟨alg, yy, P, π, ψ, h.1, h2⟩, h1⟩
  have hK : ∀ yb, IsTest p Xw yb → (kapSet Y r ν τ.1 s.sig n a T S yb).Nonempty := fun yb ht => by
    obtain ⟨alg, yy, y, P, π, ψ, h⟩ := hEx E H Dw l l' Xo Xo' c c' W Y r ν hle hL.pos hL.lev hL.good Z la p Xw hc yb ht
    obtain ⟨κ, hκ, -⟩ := hk ht h
    exact ⟨κ, hκ⟩
  obtain ⟨ρ, hρ⟩ := hGl c'.F (c'.V W) p hc.2.2.2.1 Y.X Y.s Xw Y.normal Y.proj Y.flat hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.1 n _
    hK fun z hz => chartAt hC hP hT hG hs hL s hc hA a T S hK hz
  refine ⟨ρ, fun T₀ io e y₀ ho hZ k y hy => ?_⟩
  obtain ⟨yb, yy, ht, P, π, ψ, h⟩ := hLift E H Dw l l' Xo Xo' c c' W Y r ν hle Z la p Xw hc T₀ io e y₀ ho hZ k y hy
  obtain ⟨κ, hκ, h1⟩ := hk ht h
  exact ⟨evR_ne_zero s hc ht h, h1 ▸ hρ yb ht κ hκ⟩

end Top

theorem exists_prime_mem {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ la.asIdeal ∧ ∀ q : ℕ, q.Prime → (q : 𝓞 K) ∈ la.asIdeal → q = p := by
  haveI := la.isPrime
  haveI : Finite (𝓞 K ⧸ la.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ la.ne_bot
  haveI : Nontrivial (𝓞 K ⧸ la.asIdeal) := Ideal.Quotient.nontrivial_iff.2 la.isPrime.ne_top
  have hp : (ringChar (𝓞 K ⧸ la.asIdeal)).Prime := CharP.char_prime_of_ne_zero (𝓞 K ⧸ la.asIdeal) (CharP.ringChar_ne_zero_of_finite _)
  refine ⟨_, hp, Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_natCast]; exact ringChar.Nat.cast_ringChar), fun q hq h => ?_⟩
  have := Ideal.Quotient.eq_zero_iff_mem.2 h
  rw [map_natCast, ringChar.spec] at this
  exact ((Nat.prime_dvd_prime_iff_eq hp hq).1 this).symm

open Module Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits in

theorem model_of_steps (hCov : CoverSt) (hC : ChartSt) (hP : ProjSt) (hLat : LatSt) (hT : HTLocSt) (hG : GenSt) (hEx : ExSt)
    (hLift : LiftSt) (hPt : PtSt) (hGl : GlueSt) (hPk : PackSt) :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x →
  ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)),
  ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
    (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (ϖ : O) (_ : Irreducible ϖ) (Zs : Scheme.{0})
    (f : Zs ⟶ Spec (.of O)) (D : LB Zs),
    IsIntegral Zs ∧ (∀ z : Zs, IsIntegrallyClosed (Zs.presheaf.stalk z)) ∧ IsProper f ∧ Flat f ∧ D.IsLB ∧
    (∃ t : (D.pull (reducedSpecialι f)).Gen, t.IsGen) ∧
    ∃ (sig : (D.pull (genericι f)).Gen) (κ : ℝ), sig.IsGen ∧
      ∀ w ∈ htValOn Z la, ∃ (p : ℕ) (_ : Fact p.Prime) (R : Type) (_ : CommRing R) (_ : Algebra R ℂ_[p])
        (φ : O →+* R), (Valued.v : Valuation ℂ_[p] NNReal).Integers R ∧ Function.Injective φ ∧ IsLocalHom φ ∧
        ∃ (ybar : Spec (.of R) ⟶ Zs) (y : Spec (.of ℂ_[p]) ⟶ genericFibre f) (e : (D.pull ybar).Gen)
          (cc : ℂ_[p]ˣ),
          ybar ≫ f = Spec.map (CommRingCat.ofHom φ) ∧
          y ≫ genericι f = Spec.map (CommRingCat.ofHom (algebraMap R ℂ_[p])) ≫ ybar ∧
          e.IsGen ∧ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.IsCoord f D sig ybar y e cc ∧
          w s.sig = val_vw la p (Valued.v : Valuation ℂ_[p] NNReal) (cc : ℂ_[p]) ∧
          val_vw la p (Valued.v : Valuation ℂ_[p] NNReal) (algebraMap R ℂ_[p] (φ ϖ)) = (κ : EReal) := by
  intro E _ _ _ H Dw l Xo c r U x hL Z τ s la
  obtain ⟨p, hp, hm, huniq⟩ := exists_prime_mem la
  haveI := Fact.mk hp
  obtain ⟨ρ, hρ⟩ := exists_norm hCov hC hP hLat hT hG hEx hLift hPt hGl hL s hm
  have hw : ∀ w ∈ htValOn Z la, ∃ z : ℂ_[p], z ≠ 0 ∧ ‖z‖ = ρ ∧
      w s.sig = val_vw la p (Valued.v : Valuation ℂ_[p] NNReal) z := by
    rintro w ⟨T, io, e, y₀, ho, hZ, q, hq, alg, k, y, hy, rfl⟩
    obtain rfl := huniq q hq.out (hy.mem ho)
    exact ⟨_, (hρ T io e y₀ ho hZ k y hy).1, (hρ T io e y₀ ho hZ k y hy).2, rfl⟩
  obtain ⟨z₀, hz₀, h₀⟩ : ∃ z₀ : ℂ_[p], z₀ ≠ 0 ∧ ∀ w ∈ htValOn Z la, ‖z₀‖ = ρ := by
    by_cases h : (htValOn Z la).Nonempty
    · obtain ⟨z, h1, h2, -⟩ := hw _ h.choose_spec
      exact ⟨z, h1, fun _ _ => h2⟩
    · exact ⟨1, one_ne_zero, fun w hw => absurd ⟨w, hw⟩ h⟩
  obtain ⟨O, i1, i2, i3, i4, ϖ, hϖ, Zs, f, D, a1, a2, a3, a4, a5, a6, sig, hsig, φ, hφ, hloc, ybar, y, e, cc, b1, b2, b3, b4,
    b5⟩ := hPk p z₀ hz₀
  have hne : algebraMap 𝓞_ℂ_[p] ℂ_[p] (φ ϖ) ≠ 0 := fun h =>
    hϖ.ne_zero (hφ (by rw [map_zero]; exact Subtype.ext h))
  refine ⟨O, i1, i2, i3, i4, ϖ, hϖ, Zs, f, D, a1, a2, a3, a4, a5, a6, sig, _, hsig, fun w hw' => ⟨p, inferInstance, 𝓞_ℂ_[p],
    inferInstance, inferInstance, φ, PadicComplexInt.integers p, hφ, hloc, ybar, y, e, cc, b1, b2, b3, b4, ?_,
    val_vw_of_ne la p _ hne⟩⟩
  obtain ⟨z, h1, h2, h3⟩ := hw w hw'
  rw [h3, val_vw_of_ne la p _ h1, val_vw_of_ne la p _ cc.ne_zero, coe_valued p z, coe_valued p cc, b5, h₀ w hw', h2]

open Module Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits in

theorem exists_model : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension →
  GlobalTheory.Published.PrismaticDieudonneHodge →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x →
  ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)),
  ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
    (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (ϖ : O) (_ : Irreducible ϖ) (Zs : Scheme.{0})
    (f : Zs ⟶ Spec (.of O)) (D : LB Zs),
    IsIntegral Zs ∧ (∀ z : Zs, IsIntegrallyClosed (Zs.presheaf.stalk z)) ∧ IsProper f ∧ Flat f ∧ D.IsLB ∧
    (∃ t : (D.pull (reducedSpecialι f)).Gen, t.IsGen) ∧
    ∃ (sig : (D.pull (genericι f)).Gen) (κ : ℝ), sig.IsGen ∧
      ∀ w ∈ htValOn Z la, ∃ (p : ℕ) (_ : Fact p.Prime) (R : Type) (_ : CommRing R) (_ : Algebra R ℂ_[p])
        (φ : O →+* R), (Valued.v : Valuation ℂ_[p] NNReal).Integers R ∧ Function.Injective φ ∧ IsLocalHom φ ∧
        ∃ (ybar : Spec (.of R) ⟶ Zs) (y : Spec (.of ℂ_[p]) ⟶ genericFibre f) (e : (D.pull ybar).Gen)
          (cc : ℂ_[p]ˣ),
          ybar ≫ f = Spec.map (CommRingCat.ofHom φ) ∧
          y ≫ genericι f = Spec.map (CommRingCat.ofHom (algebraMap R ℂ_[p])) ≫ ybar ∧
          e.IsGen ∧ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.IsCoord f D sig ybar y e cc ∧
          w s.sig = val_vw la p (Valued.v : Valuation ℂ_[p] NNReal) (cc : ℂ_[p]) ∧
          val_vw la p (Valued.v : Valuation ℂ_[p] NNReal) (algebraMap R ℂ_[p] (φ ϖ)) = (κ : EReal) := fun hP h₂ h₃ _ =>
  model_of_steps GlobalTheory.T.cover_statement_holds GlobalTheory.T.chart_statement_holds GlobalTheory.T.projection_statement_holds GlobalTheory.T.lattice_statement_holds (GlobalTheory.T.hodge_tate_local_of_kernel_at_point (GlobalTheory.T.hodge_tate_kernel_at_point hP)) (GlobalTheory.T.generic_statement_of_canonical_extension hP h₂ h₃)
    (GlobalTheory.T.existence_of_comparison GlobalTheory.T.comparison_statement_holds) (GlobalTheory.T.lifting_of_comparison GlobalTheory.T.comparison_statement_holds)
    (GlobalTheory.T.pointwise_of_tate_value_bound (GlobalTheory.T.hodge_tate_kernel_at_point hP) GlobalTheory.T.tate_statement_holds GlobalTheory.T.value_statement_holds GlobalTheory.T.bound_statement_holds)
    (GlobalTheory.T.gluing_of_connectedness (GlobalTheory.T.connectedness_statement_holds hP) GlobalTheory.T.prop_z_statement) GlobalTheory.T.packing_statement_holds

end GlobalTheory.FlatModel

end
end

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open AlgebraicGeometry CategoryTheory GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits ReciprocityTheory.ChartRestriction.G.Semi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_section_flat_weight : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension →
  GlobalTheory.Published.PrismaticDieudonneHodge →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x →
  ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)),
  ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
    (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (ϖ : O) (_ : Irreducible ϖ) (Zs : Scheme.{0})
    (f : Zs ⟶ Spec (.of O)) (D : LB Zs),
    IsIntegral Zs ∧ (∀ z : Zs, IsIntegrallyClosed (Zs.presheaf.stalk z)) ∧ IsProper f ∧ Flat f ∧ D.IsLB ∧
    (∃ t : (D.pull (reducedSpecialι f)).Gen, t.IsGen) ∧
    ∃ (sig : (D.pull (genericι f)).Gen) (κ : ℝ), sig.IsGen ∧
      ∀ w ∈ htValOn Z la, ∃ (p : ℕ) (_ : Fact p.Prime) (R : Type) (_ : CommRing R) (_ : Algebra R ℂ_[p])
        (φ : O →+* R), (Valued.v : Valuation ℂ_[p] NNReal).Integers R ∧ Function.Injective φ ∧ IsLocalHom φ ∧
        ∃ (ybar : Spec (.of R) ⟶ Zs) (y : Spec (.of ℂ_[p]) ⟶ genericFibre f) (e : (D.pull ybar).Gen)
          (cc : ℂ_[p]ˣ),
          ybar ≫ f = Spec.map (CommRingCat.ofHom φ) ∧
          y ≫ genericι f = Spec.map (CommRingCat.ofHom (algebraMap R ℂ_[p])) ≫ ybar ∧
          e.IsGen ∧ IsCoord f D sig ybar y e cc ∧
          w s.sig = val_vw la p (Valued.v : Valuation ℂ_[p] NNReal) (cc : ℂ_[p]) ∧
          val_vw la p (Valued.v : Valuation ℂ_[p] NNReal) (algebraMap R ℂ_[p] (φ ϖ)) = (κ : EReal) := by
  atlas_forward_decl GlobalTheory.FlatModel.exists_model
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open AlgebraicGeometry CategoryTheory GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section
namespace GlobalTheory.HTConstModel

theorem val_vw_eq_of_pow {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (p : ℕ)
    {C : Type} [Field C] (v : Valuation C NNReal) {a b : C} (ha : a ≠ 0) (hb : b ≠ 0) {M : ℕ} (hM : 1 ≤ M) {n : ℤ}
    (h : v a ^ M = v b ^ n) {κ : ℝ} (hκ : val_vw la p v b = (κ : EReal)) :
    val_vw la p v a = (((n : ℝ) / M * κ : ℝ) : EReal) := by
  rw [val_vw_of_ne la p v hb, EReal.coe_eq_coe_iff] at hκ
  rw [val_vw_of_ne la p v ha, EReal.coe_eq_coe_iff, ← hκ]
  have hva : (0 : ℝ) < v a := by simpa [pos_iff_ne_zero] using ha
  have hvb : (0 : ℝ) < v b := by simpa [pos_iff_ne_zero] using hb
  have hl : (M : ℝ) * Real.log (v a) = n * Real.log (v b) := by
    have := congrArg (fun t : NNReal => Real.log (t : ℝ)) h
    simp only [NNReal.coe_pow, NNReal.coe_zpow] at this
    rwa [Real.log_pow, Real.log_zpow] at this
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have : Real.log (v a) = n / M * Real.log (v b) := by
    field_simp
    linarith
  rw [this]
  ring

end GlobalTheory.HTConstModel

theorem GlobalTheory.FlatCore.htConst_always : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne →
    GlobalTheory.Published.DeRhamCanonicalExtension → GlobalTheory.Published.PrismaticDieudonneHodge → Always fun U x => HTConst U x := by
  intro hP h1 h2 h3 E _ _ _ H Dw l Xo c r U x hL Z τ s la
  obtain ⟨O, _, _, _, _, ϖ, hϖ, Zs, f, D, hInt, hNorm, hProp, hFlat, hLB, hT, sig, κ, hsig, hw⟩ :=
    GlobalTheory.T.archimedean_section_flat_weight hP h1 h2 h3 E H Dw l Xo c r U x hL Z τ s la
  have hconn := GlobalTheory.T.special_fibre_connected O Zs f hInt hNorm hProp hFlat
  obtain ⟨M, n, hM, -, hV⟩ :=
    GlobalTheory.T.prop_z_statement O ϖ hϖ Zs f D ⟨hInt, hNorm, hProp, hFlat, hconn, hLB, hT⟩ sig hsig
  refine ⟨(n : ℝ) / M * κ, fun w hw' => ?_⟩
  obtain ⟨p, _, R, _, _, φ, hv, hφi, hφl, ybar, y, e, cc, hyb, hy, he, hco, hval, hκ⟩ := hw w hw'
  have h := (hV R ℂ_[p] NNReal (Valued.v : Valuation ℂ_[p] NNReal) hv φ hφi hφl ybar hyb y hy).2 e cc he hco
  have hb : algebraMap R ℂ_[p] (φ ϖ) ≠ 0 := fun h0 =>
    hϖ.ne_zero (hφi ((hv.hom_inj (h0.trans (map_zero _).symm)).trans (map_zero φ).symm))
  rw [hval]
  exact GlobalTheory.HTConstModel.val_vw_eq_of_pow la p _ cc.ne_zero hb hM h hκ
end
end
