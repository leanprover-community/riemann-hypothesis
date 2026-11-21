import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatMulVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyRationalUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact

section
open MeasureTheory

namespace GlobalTheory.HaarFundDom

open scoped Pointwise

theorem exists_haar_fundDom_mass_one : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [Countable Γ] [DiscreteTopology Γ] (K : Set G), IsCompact K →
    (∀ g : G, ∃ γ : Γ, γ • g ∈ K) →
    ∃ (μ : Measure G) (𝓕 : Set G), μ.IsHaarMeasure ∧ IsFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1 := by
  intro G _ _ _ _ _ _ _ _ Γ _ _ K hK hcov
  let μ₀ : Measure G := Measure.haar
  obtain ⟨𝓕, h𝓕m, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_measurable_section Γ
  have hD : IsFundamentalDomain Γ 𝓕 μ₀ := IsFundamentalDomain.mk' h𝓕m.nullMeasurableSet h𝓕
  haveI : MeasurableMul G :=
    ⟨fun g => (continuous_const.mul continuous_id).measurable, fun g => (continuous_id.mul continuous_const).measurable⟩
  haveI : MeasurableConstSMul Γ G :=
    ⟨fun γ => (continuous_const.mul continuous_id : Continuous fun x : G => (γ : G) * x).measurable⟩
  haveI : SMulInvariantMeasure Γ G μ₀ := ⟨fun γ A _ => measure_preimage_mul μ₀ (γ : G) A⟩
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hsub : 𝓕 ⊆ ⋃ γ : Γ, γ • K ∩ 𝓕 := by
    intro x hx
    obtain ⟨γ, hγ⟩ := hcov x
    refine Set.mem_iUnion.2 ⟨γ⁻¹, Set.mem_smul_set.2 ⟨γ • x, hγ, ?_⟩, hx⟩
    simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hfin : μ₀ 𝓕 < ⊤ :=
    calc μ₀ 𝓕 ≤ μ₀ (⋃ γ : Γ, γ • K ∩ 𝓕) := measure_mono hsub
      _ ≤ ∑' γ : Γ, μ₀ (γ • K ∩ 𝓕) := measure_iUnion_le _
      _ = μ₀ K := (hD.measure_eq_tsum _).symm
      _ < ⊤ := hK.measure_lt_top
  have hne : μ₀ 𝓕 ≠ 0 := by
    intro h0
    have h1 := hD.measure_eq_tsum' Set.univ
    simp only [Set.univ_inter, measure_smul, h0, tsum_zero] at h1
    exact (Measure.measure_univ_pos.2 (NeZero.ne μ₀)).ne' h1
  refine ⟨(μ₀ 𝓕)⁻¹ • μ₀, 𝓕, ?_, hD.mono Measure.smul_absolutelyContinuous, ?_⟩
  · exact Measure.IsHaarMeasure.smul μ₀ (ENNReal.inv_ne_zero.2 hfin.ne) (ENNReal.inv_ne_top.2 hne)
  · rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hne hfin.ne]

end GlobalTheory.HaarFundDom
end

section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocompact_lattice_unit_covolume : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ g : G, ∃ γ : Γ, γ • g ∈ K) → ∃ (μ : Measure G) (𝓕 : Set G), μ.IsHaarMeasure ∧ IsFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1 := by
  first | exact @GlobalTheory.HaarFundDom.exists_haar_fundDom_mass_one | exact GlobalTheory.HaarFundDom.exists_haar_fundDom_mass_one | (intros; apply GlobalTheory.HaarFundDom.exists_haar_fundDom_mass_one <;> assumption)
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass

namespace GlobalTheory.RatUDiscreteSub

theorem discreteTopology_subgroupOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (N : Subgroup (UA σ J)),
    DiscreteTopology ((ratU σ J).subgroupOf N) := by
  intro F E _ _ _ _ _ σ n J N
  haveI := GlobalTheory.RatUDiscrete.discreteTopology_ratU F E σ n J
  let φ : (ratU σ J).subgroupOf N → ratU σ J := fun x => ⟨x.1.1, Subgroup.mem_subgroupOf.1 x.2⟩
  have h2 : Topology.IsEmbedding (fun x : (ratU σ J).subgroupOf N => ((x : N) : UA σ J)) :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have hφ : Topology.IsEmbedding φ :=
    (Topology.IsEmbedding.of_comp_iff (Topology.IsEmbedding.subtypeVal (p := fun x : UA σ J => x ∈ ratU σ J))).1 h2
  exact hφ.discreteTopology

end GlobalTheory.RatUDiscreteSub
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrete_rational_points_subgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (N : Subgroup (UA σ J)), DiscreteTopology ((ratU σ J).subgroupOf N) := by
  atlas_forward_decl GlobalTheory.RatUDiscreteSub.discreteTopology_subgroupOf
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass

noncomputable section

namespace GlobalTheory.UnipClosed

theorem isClosed_unip (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d d₁ : ℕ) (W : Spc F E d) (H' : Plane E d d₁) (hx : H'.x ≠ 0) :
    IsClosed ((unip σ W H' : Subgroup (UA σ W.J)) : Set (UA σ W.J)) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  set x : Fin d → AE F E := incV F H'.x with hxdef
  set ι : Matrix (Fin d) (Fin d₁) (AE F E) := incM F H'.ι

  set S : Set (UA σ W.J) := {u | mat u *ᵥ x = x ∧ ∀ z, ∃ a : AE F E, mat u *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x} with hS
  obtain ⟨k, hk⟩ : ∃ k, H'.x k ≠ 0 := by
    by_contra h; push_neg at h; exact hx (funext h)
  have hcu : IsUnit (x k) := by
    have : x k = inclR (F := F) (AF F) (H'.x k) := rfl
    rw [this]; exact (IsUnit.mk0 _ hk).map _
  set c : (AE F E)ˣ := hcu.unit
  have hc : (c : AE F E) = x k := hcu.unit_spec
  have hline : ∀ v w : Fin d → AE F E, (∃ a : AE F E, w = v + a • x) ↔ w = v + ((w - v) k * ↑c⁻¹) • x := by
    intro v w
    constructor
    · rintro ⟨a, rfl⟩
      congr 2
      simp only [add_sub_cancel_left, Pi.smul_apply, smul_eq_mul]
      rw [← hc, mul_assoc, Units.mul_inv, mul_one]
    · intro h; exact ⟨_, h⟩
  have hm : Continuous fun g : UA σ W.J => mat g := Units.continuous_val.comp continuous_subtype_val
  have hSc : IsClosed S := by
    have h1 : IsClosed {u : UA σ W.J | mat u *ᵥ x = x} :=
      isClosed_eq (hm.matrix_mulVec continuous_const) continuous_const
    have h2 : IsClosed {u : UA σ W.J | ∀ z, ∃ a : AE F E, mat u *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x} := by
      simp only [Set.setOf_forall]
      refine isClosed_iInter fun z => ?_
      simp_rw [hline]
      have hf : Continuous fun u : UA σ W.J => mat u *ᵥ (ι *ᵥ z) := hm.matrix_mulVec continuous_const
      have hg : Continuous fun u : UA σ W.J => ((mat u *ᵥ (ι *ᵥ z) - ι *ᵥ z) k * ↑c⁻¹) :=
        ((continuous_apply k).comp (hf.sub continuous_const)).mul continuous_const
      exact isClosed_eq hf (continuous_const.add (hg.smul (continuous_const : Continuous fun _ : UA σ W.J => x)))
    exact h1.inter h2
  have hsub : ∃ H : Subgroup (UA σ W.J), (H : Set (UA σ W.J)) = S := by
    refine ⟨{ carrier := S, one_mem' := ?_, mul_mem' := ?_, inv_mem' := ?_ }, rfl⟩
    · rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
      refine ⟨by rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, hv1, hu1], fun z => ?_⟩
      obtain ⟨a, ha⟩ := hv2 z
      obtain ⟨b, hb⟩ := hu2 z
      refine ⟨b + a, ?_⟩
      rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_add, Matrix.mulVec_smul, hb, hu1, add_smul, add_assoc]
    · exact ⟨by simp [GlobalTheory.StabHaar.mat_one], fun z => ⟨0, by simp [GlobalTheory.StabHaar.mat_one]⟩⟩
    · rintro u ⟨hu1, hu2⟩
      have e1 : mat u⁻¹ *ᵥ x = x := by
        conv_lhs => rw [← hu1]
        rw [Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mulVec]
      refine ⟨e1, fun z => ?_⟩
      obtain ⟨a, ha⟩ := hu2 z
      refine ⟨-a, ?_⟩
      have : mat u⁻¹ *ᵥ (mat u *ᵥ (ι *ᵥ z)) = ι *ᵥ z := by
        rw [Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mulVec]
      rw [ha, Matrix.mulVec_add, Matrix.mulVec_smul, e1] at this
      rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq, this]
  obtain ⟨H, hH⟩ := hsub
  have : unip σ W H' = H := by
    apply le_antisymm
    · rw [unip, Subgroup.closure_le]; exact hH.symm ▸ subset_rfl
    · intro g hg
      have : g ∈ S := hH ▸ hg
      exact Subgroup.subset_closure this
  rw [this, hH]; exact hSc

end GlobalTheory.UnipClosed
end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_radical_closed_nonzero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d d₁ : ℕ) (W : Spc F E d) (H' : Plane E d d₁), H'.x ≠ 0 → IsClosed ((unip σ W H' : Subgroup (UA σ W.J)) : Set (UA σ W.J)) := by
  first | exact @GlobalTheory.UnipClosed.isClosed_unip | exact GlobalTheory.UnipClosed.isClosed_unip | (intros; apply GlobalTheory.UnipClosed.isClosed_unip <;> assumption)
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
namespace GlobalTheory.AdeleCocompactExt

theorem exists_compact_adeleE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    ∃ K : Set (AE F E), IsCompact K ∧ ∀ a : AE F E, ∃ e : E, a - inclR (F := F) (AF F) e ∈ K := by
  intro F E _ _ _ _ _
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨K₀, hK₀, hK⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  let b := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (AF F) b
  have hφ : Continuous B.equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap B.equivFun.symm.toLinearMap
  refine ⟨B.equivFun.symm '' Set.pi Set.univ (fun _ => K₀),
    (isCompact_univ_pi fun _ => hK₀).image hφ, ?_⟩
  intro a
  choose x hx using fun k => hK (B.equivFun a k)
  refine ⟨∑ k, x k • b k, fun k => B.equivFun a k - algebraMap F (AF F) (x k), fun k _ => hx k, ?_⟩
  rw [LinearEquiv.symm_apply_eq]
  funext k
  have h1 : B.equivFun (inclR (F := F) (AF F) (∑ k, x k • b k)) k = algebraMap F (AF F) (x k) := by
    rw [Module.Basis.equivFun_apply]
    show (B.repr ((1 : AF F) ⊗ₜ[F] (∑ k, x k • b k))) k = _
    rw [Algebra.TensorProduct.basis_repr_tmul]
    simp [b, Module.Basis.repr_sum_self]
    rw [Finset.sum_eq_single k (fun j _ hj => by simp [Finsupp.single_apply, hj]) (by simp)]
    simp
  simp only [map_sub, Pi.sub_apply, h1]

end GlobalTheory.AdeleCocompactExt
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adele_quotient_compact_fundamental_set : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ K : Set (AE F E), IsCompact K ∧ ∀ a : AE F E, ∃ e : E, a - inclR (F := F) (AF F) e ∈ K := by
  first | exact @GlobalTheory.AdeleCocompactExt.exists_compact_adeleE | exact GlobalTheory.AdeleCocompactExt.exists_compact_adeleE | (intros; apply GlobalTheory.AdeleCocompactExt.exists_compact_adeleE <;> assumption)
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass

noncomputable section

namespace GlobalTheory.UnipMass.Unitary

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_invol (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [cA, hσ]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem cA_inclR (σ : E →ₐ[F] E) (a : E) : cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := by
  simp [cA, inclR]

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem bar_add (w w' : Fin n → AE F E) :
    (fun i => cA σ ((w + w') i)) = (fun i => cA σ (w i)) + fun i => cA σ (w' i) := by
  funext i; simp

theorem bar_sub (w w' : Fin n → AE F E) :
    (fun i => cA σ ((w - w') i)) = (fun i => cA σ (w i)) - fun i => cA σ (w' i) := by
  funext i; simp

theorem bar_smul (a : AE F E) (w : Fin n → AE F E) :
    (fun i => cA σ ((a • w) i)) = cA σ a • fun i => cA σ (w i) := by
  funext i; simp

theorem hA_add_left (v v' w : Fin n → AE F E) : hA σ J (v + v') w = hA σ J v w + hA σ J v' w := by
  simp [hA, add_dotProduct]

theorem hA_sub_left (v v' w : Fin n → AE F E) : hA σ J (v - v') w = hA σ J v w - hA σ J v' w := by
  simp [hA, sub_dotProduct]

theorem hA_smul_left (a : AE F E) (v w : Fin n → AE F E) : hA σ J (a • v) w = a * hA σ J v w := by
  simp [hA, smul_dotProduct]

theorem hA_add_right (v w w' : Fin n → AE F E) : hA σ J v (w + w') = hA σ J v w + hA σ J v w' := by
  simp only [hA, bar_add, Matrix.mulVec_add, dotProduct_add]

theorem hA_sub_right (v w w' : Fin n → AE F E) : hA σ J v (w - w') = hA σ J v w - hA σ J v w' := by
  simp only [hA, bar_sub, Matrix.mulVec_sub, dotProduct_sub]

theorem hA_smul_right (a : AE F E) (v w : Fin n → AE F E) : hA σ J v (a • w) = cA σ a * hA σ J v w := by
  simp only [hA, bar_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hA_swap (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = -J i j) (v w : Fin n → AE F E) :
    hA σ J w v = -cA σ (hA σ J v w) := by
  simp only [hA, dotProduct, Matrix.mulVec, map_sum, map_mul, cA_invol σ hσ, incM, Matrix.map_apply, cA_inclR, hJ,
    map_neg, Finset.mul_sum, Finset.sum_neg_distrib]
  rw [Finset.sum_comm (f := fun x x_1 => (cA σ) (v x) * (-(inclR (F := F) (AF F)) (J x_1 x) * w x_1))]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

variable {σ J}

theorem hA_nmat (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = -J i j) (x u : Fin n → AE F E) (c : AE F E)
    (hxx : hA σ J x x = 0) (hux : hA σ J u x = 0) (hc : c - cA σ c = -hA σ J u u) (v w : Fin n → AE F E) :
    hA σ J (nmat σ J x u c *ᵥ v) (nmat σ J x u c *ᵥ w) = hA σ J v w := by
  have hxu : hA σ J x u = 0 := by rw [hA_swap σ J hσ hJ u x, hux, map_zero, neg_zero]
  have hxw : hA σ J x w = -cA σ (hA σ J w x) := hA_swap σ J hσ hJ w x
  have huw : hA σ J u w = -cA σ (hA σ J w u) := hA_swap σ J hσ hJ w u
  rw [nmat_mulVec, nmat_mulVec]
  simp only [hA_sub_left, hA_sub_right, hA_smul_left, hA_smul_right, hA_add_left, hA_add_right, hxx, hux, hxu,
    hxw, huw]
  linear_combination (hA σ J v x * cA σ (hA σ J w x)) * hc

theorem entry_eq (T : Matrix (Fin n) (Fin n) (AE F E)) (i j : Fin n) :
    (Tᵀ * incM F J * T.map (cA σ)) i j = hA σ J (T *ᵥ Pi.single i 1) (T *ᵥ Pi.single j 1) := by
  have hs : ∀ m : Fin n, T *ᵥ Pi.single m 1 = fun k => T k m := fun m => by
    funext k; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hs, hs]
  simp only [hA, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem entry_J (hσ : ∀ a, σ (σ a) = a) (i j : Fin n) :
    incM F J i j = hA σ J (Pi.single i 1) (Pi.single j 1) := by
  have hb : (fun l => cA σ ((Pi.single j 1 : Fin n → AE F E) l)) = Pi.single j 1 := by
    funext l; by_cases h : l = j
    · subst h; simp
    · simp [Pi.single_apply, h]
  rw [hA, hb, single_one_dotProduct, Matrix.mulVec_single_one]
  simp

end GlobalTheory.UnipMass.Unitary

namespace GlobalTheory.UnipMass

theorem nmat_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ a, σ (σ a) = a) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ i j, σ (J j i) = -J i j) → ∀ (x u : Fin n → AE F E) (c : AE F E), hA σ J x x = 0 → hA σ J u x = 0 → c - cA σ c = -hA σ J u u → (nmat σ J x u c)ᵀ * incM F J * (nmat σ J x u c).map (cA σ) = incM F J := by
  intro F E _ _ _ _ _ σ hσ n J hJ x u c hxx hux hc
  ext i j
  rw [Unitary.entry_eq, Unitary.hA_nmat hσ hJ x u c hxx hux hc, ← Unitary.entry_J hσ]

end GlobalTheory.UnipMass
end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_matrix_preserves_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ a, σ (σ a) = a) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ i j, σ (J j i) = -J i j) → ∀ (x u : Fin n → AE F E) (c : AE F E), hA σ J x x = 0 → hA σ J u x = 0 → c - cA σ c = -hA σ J u u → (nmat σ J x u c)ᵀ * incM F J * (nmat σ J x u c).map (cA σ) = incM F J := by
  first | exact @GlobalTheory.UnipMass.nmat_unitary | exact GlobalTheory.UnipMass.nmat_unitary | (intros; apply GlobalTheory.UnipMass.nmat_unitary <;> assumption)
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass

noncomputable section
namespace GlobalTheory.UnipMass
namespace ProdFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_cA_of_invol (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [cA, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem cA_incM_apply (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    cA σ (incM F J i j) = incM F (J.map σ) i j := by
  simp [cA, incM, inclR]

theorem hA_swap (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (v w : Fin n → AE F E) : hA σ J w v = - cA σ (hA σ J v w) := by
  simp only [hA, dotProduct, Matrix.mulVec, map_sum, map_mul, cA_cA_of_invol σ hσ, cA_incM_apply]
  simp only [incM, Matrix.map_apply, hJ, map_neg]
  simp only [Finset.mul_sum, neg_mul, mul_neg, Finset.sum_neg_distrib, neg_neg]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hA_add_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v v' w : Fin n → AE F E) :
    hA σ J (v + v') w = hA σ J v w + hA σ J v' w := by
  simp only [hA, add_dotProduct]

theorem hA_sub_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v v' w : Fin n → AE F E) :
    hA σ J (v - v') w = hA σ J v w - hA σ J v' w := by
  simp only [hA, sub_dotProduct]

theorem hA_smul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : AE F E) (v w : Fin n → AE F E) :
    hA σ J (a • v) w = a * hA σ J v w := by
  simp only [hA, smul_dotProduct, smul_eq_mul]

theorem hA_add_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w w' : Fin n → AE F E) :
    hA σ J v (w + w') = hA σ J v w + hA σ J v w' := by
  have : (fun i => cA σ ((w + w') i)) = (fun i => cA σ (w i)) + fun i => cA σ (w' i) := by
    funext i; simp
  simp only [hA, this, Matrix.mulVec_add, dotProduct_add]

end ProdFormula

open ProdFormula in

theorem nmat_mul_nmat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), (∀ a, σ (σ a) = a) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ i j, σ (J j i) = -J i j) →
    ∀ (x u u' : Fin n → AE F E) (c c' : AE F E), hA σ J x x = 0 → hA σ J u x = 0 → hA σ J u' x = 0 →
    nmat σ J x u c * nmat σ J x u' c' = nmat σ J x (u + u') (c + c' - hA σ J u' u) := by
  intro F E _ _ _ _ _ σ hσ n J hJ x u u' c c' hxx hux hu'x
  have hxu : hA σ J x u = 0 := by rw [hA_swap σ hσ J hJ u x, hux, map_zero, neg_zero]
  have key : ∀ v, (nmat σ J x u c * nmat σ J x u' c') *ᵥ v =
      nmat σ J x (u + u') (c + c' - hA σ J u' u) *ᵥ v := by
    intro v
    rw [← Matrix.mulVec_mulVec, nmat_mulVec, nmat_mulVec, nmat_mulVec]
    simp only [hA_add_left, hA_sub_left, hA_smul_left, hA_add_right, hxx, hux, hu'x, hxu]
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  exact Matrix.toLin'.injective (LinearMap.ext fun v => by simpa only [Matrix.toLin'_apply] using key v)

end GlobalTheory.UnipMass
end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_matrix_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ a, σ (σ a) = a) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ i j, σ (J j i) = -J i j) → ∀ (x u u' : Fin n → AE F E) (c c' : AE F E), hA σ J x x = 0 → hA σ J u x = 0 → hA σ J u' x = 0 → nmat σ J x u c * nmat σ J x u' c' = nmat σ J x (u + u') (c + c' - hA σ J u' u) := by
  atlas_forward_decl GlobalTheory.UnipMass.nmat_mul_nmat
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
noncomputable section

namespace GlobalTheory.UnipMass.StdMat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_inclR_eq (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (AF F) e) = inclR (AF F) (σ e) := by
  simp [cA, inclR]

theorem cA_cA_eq (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (a : AE F E) : cA σ (cA σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cA, hσ]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem incM_mulVec_incV_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) E) (v : Fin n → E) :
    incM F A *ᵥ incV F v = incV F (A *ᵥ v) := by
  ext i; simp [incM, incV, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem cA_incV_eq (σ : E →ₐ[F] E) {n : ℕ} (x : Fin n → E) :
    (fun i => cA σ (incV F x i)) = incV F (fun i => σ (x i)) := by
  funext i; simp [incV, cA_inclR_eq]

theorem hA_incV_eq (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b : Fin n → E) :
    hA σ J (incV F a) (incV F b) = inclR (AF F) (form σ J a b) := by
  rw [hA, cA_incV_eq, incM_mulVec_incV_eq]
  simp [form, incV, dotProduct, map_sum, map_mul]

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem hA_add_l (v v' w : Fin n → AE F E) : hA σ J (v + v') w = hA σ J v w + hA σ J v' w := by
  simp [hA, add_dotProduct]

theorem hA_smul_l (a : AE F E) (v w : Fin n → AE F E) : hA σ J (a • v) w = a * hA σ J v w := by
  simp [hA, smul_dotProduct]

theorem hA_add_r (v w w' : Fin n → AE F E) : hA σ J v (w + w') = hA σ J v w + hA σ J v w' := by
  have : (fun i => cA σ ((w + w') i)) = (fun i => cA σ (w i)) + (fun i => cA σ (w' i)) := by
    funext i; simp
  rw [hA, this, Matrix.mulVec_add, dotProduct_add]; rfl

theorem hA_smul_r (a : AE F E) (v w : Fin n → AE F E) : hA σ J v (a • w) = cA σ a * hA σ J v w := by
  have : (fun i => cA σ ((a • w) i)) = cA σ a • (fun i => cA σ (w i)) := by
    funext i; simp
  rw [hA, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]; rfl

theorem hA_skew_eq (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = -J i j) (v w : Fin n → AE F E) :
    hA σ J w v = -cA σ (hA σ J v w) := by
  simp only [hA, dotProduct, Matrix.mulVec, incM, Matrix.map_apply, map_sum, map_mul, cA_cA_eq σ hσ, cA_inclR_eq,
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; simp only [map_neg]; ring

end GlobalTheory.UnipMass.StdMat

namespace GlobalTheory.UnipMass.StdMat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hA_mat_eq (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) (v w : Fin n → AE F E) :
    hA σ J (mat g *ᵥ v) (mat g *ᵥ w) = hA σ J v w := by
  have hg : (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J := g.2
  have hc : (fun i => cA σ ((mat g *ᵥ w) i)) = (mat g).map (cA σ) *ᵥ fun i => cA σ (w i) := by
    funext i; exact RingHom.map_mulVec (cA σ).toRingHom (mat g) w i
  rw [hA, hA, hc, ← Matrix.vecMul_transpose (mat g) v, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec]
  rw [← Matrix.mul_assoc, hg]

theorem hA_ι_incV_eq (σ : E →ₐ[F] E) {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (ι : Matrix (Fin d) (Fin d₁) E)
    (w : Fin d → E) (h : ∀ u, form σ J (ι *ᵥ u) w = 0) (z : Fin d₁ → AE F E) :
    hA σ J (incM F ι *ᵥ z) (incV F w) = 0 := by
  have hq : ιᵀ *ᵥ (J *ᵥ fun i => σ (w i)) = 0 := by
    funext k
    have := h (Pi.single k 1)
    rw [form, Matrix.mulVec_single_one] at this
    exact this
  rw [hA, cA_incV_eq, incM_mulVec_incV_eq, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
    show (incM F ι)ᵀ = incM F ιᵀ from rfl, incM_mulVec_incV_eq, hq]
  have : incV F (0 : Fin d₁ → E) = 0 := by funext i; simp [incV]
  rw [this, dotProduct_zero]

theorem incV_add_eq {n : ℕ} (a b : Fin n → E) : incV F (a + b) = incV F a + incV F b := by
  funext i; simp [incV]

theorem incV_smul_eq {n : ℕ} (s : E) (a : Fin n → E) : incV F (s • a) = inclR (F := F) (AF F) s • incV F a := by
  funext i; simp [incV]

theorem decomp_eq {d d₁ : ℕ} (x y : Fin d → E) (ι : Matrix (Fin d) (Fin d₁) E)
    (hdec : ∀ v : Fin d → E, ∃ (s t : E) (u : Fin d₁ → E), v = s • x + ι *ᵥ u + t • y) (v : Fin d → AE F E) :
    ∃ (s t : AE F E) (z : Fin d₁ → AE F E), v = s • incV F x + incM F ι *ᵥ z + t • incV F y := by
  choose s t u hu using fun i => hdec (Pi.single i 1)
  have he : ∀ i, incV F (Pi.single i (1 : E)) =
      inclR (F := F) (AF F) (s i) • incV F x + incM F ι *ᵥ incV F (u i) + inclR (F := F) (AF F) (t i) • incV F y := by
    intro i
    rw [hu i, incV_add_eq, incV_add_eq, incV_smul_eq, incV_smul_eq, incM_mulVec_incV_eq]
  have hv : v = ∑ i, v i • incV F (Pi.single i (1 : E)) := by
    funext k; simp [incV, Finset.sum_apply, Pi.single_apply]
  refine ⟨∑ i, v i * inclR (F := F) (AF F) (s i), ∑ i, v i * inclR (F := F) (AF F) (t i), ∑ i, v i • incV F (u i), ?_⟩
  calc v = ∑ i, v i • incV F (Pi.single i (1 : E)) := hv
    _ = _ := by
      simp only [he, smul_add, smul_smul, Finset.sum_add_distrib, Finset.sum_smul, Matrix.mulVec_sum, Matrix.mulVec_smul]

theorem mem_unip_std (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) (g : UA σ W.J)
    (hg : g ∈ unip σ W H') :
    mat g *ᵥ incV F H'.x = incV F H'.x ∧
      ∀ z, ∃ a : AE F E, mat g *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x := by
  unfold unip at hg
  induction hg using Subgroup.closure_induction with
  | mem u hu => exact hu
  | one => exact ⟨by simp [mat], fun z => ⟨0, by simp [mat]⟩⟩
  | mul u v _ _ hu hv =>
    have hm : mat (u * v) = mat u * mat v := rfl
    refine ⟨?_, fun z => ?_⟩
    · rw [hm, ← Matrix.mulVec_mulVec, hv.1, hu.1]
    · obtain ⟨a, ha⟩ := hv.2 z
      obtain ⟨b, hb⟩ := hu.2 z
      refine ⟨b + a, ?_⟩
      rw [hm, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_add, Matrix.mulVec_smul, hb, hu.1, add_smul]
      abel
  | inv u _ hu =>
    have h1 : mat u⁻¹ * mat u = 1 := by
      rw [show mat u⁻¹ * mat u = mat (u⁻¹ * u) from rfl, inv_mul_cancel]; rfl
    have hx : mat u⁻¹ *ᵥ incV F H'.x = incV F H'.x := by
      conv_lhs => rw [← hu.1]
      rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    refine ⟨hx, fun z => ?_⟩
    obtain ⟨a, ha⟩ := hu.2 z
    have key : mat u⁻¹ *ᵥ (incM F H'.ι *ᵥ z + a • incV F H'.x) = incM F H'.ι *ᵥ z := by
      rw [← ha, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hx] at key
    refine ⟨-a, ?_⟩
    rw [eq_sub_of_add_eq key, neg_smul, sub_eq_add_neg]

end GlobalTheory.UnipMass.StdMat

namespace GlobalTheory.UnipMass.StdMat

theorem unip_eq_nmat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ a, σ (σ a) = a) → ∀ (d d₁ : ℕ) (W : Spc F E d) (H' : Plane E d d₁), (∀ i j, σ (W.J j i) = -W.J i j) → form σ W.J H'.x H'.x = 0 → form σ W.J H'.y H'.y = 0 → form σ W.J H'.x H'.y = 1 → (∀ u, form σ W.J (H'.ι *ᵥ u) H'.x = 0 ∧ form σ W.J (H'.ι *ᵥ u) H'.y = 0) → (∀ v : Fin d → E, ∃ (s t : E) (u : Fin d₁ → E), v = s • H'.x + H'.ι *ᵥ u + t • H'.y) → ∀ g ∈ unip σ W H', ∃ (b : Fin d₁ → AE F E) (c : AE F E), c - cA σ c = -hA σ W.J (incM F H'.ι *ᵥ b) (incM F H'.ι *ᵥ b) ∧ mat g = nmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ b) c := by
  intro F E _ _ _ _ _ σ hσ d d₁ W H' hJ hxx hyy hxy horth hdec g hg
  have hXX : hA σ W.J (incV F H'.x) (incV F H'.x) = 0 := by rw [hA_incV_eq, hxx, map_zero]
  have hYY : hA σ W.J (incV F H'.y) (incV F H'.y) = 0 := by rw [hA_incV_eq, hyy, map_zero]
  have hXY : hA σ W.J (incV F H'.x) (incV F H'.y) = 1 := by rw [hA_incV_eq, hxy, map_one]
  have hYX : hA σ W.J (incV F H'.y) (incV F H'.x) = -1 := by
    rw [hA_skew_eq σ W.J hσ hJ, hXY, map_one]
  have hιX : ∀ z, hA σ W.J (incM F H'.ι *ᵥ z) (incV F H'.x) = 0 :=
    hA_ι_incV_eq σ W.J H'.ι H'.x (fun u => (horth u).1)
  have hιY : ∀ z, hA σ W.J (incM F H'.ι *ᵥ z) (incV F H'.y) = 0 :=
    hA_ι_incV_eq σ W.J H'.ι H'.y (fun u => (horth u).2)
  have hXι : ∀ z, hA σ W.J (incV F H'.x) (incM F H'.ι *ᵥ z) = 0 := fun z => by
    rw [hA_skew_eq σ W.J hσ hJ, hιX, map_zero, neg_zero]
  have hYι : ∀ z, hA σ W.J (incV F H'.y) (incM F H'.ι *ᵥ z) = 0 := fun z => by
    rw [hA_skew_eq σ W.J hσ hJ, hιY, map_zero, neg_zero]
  obtain ⟨hgX, hgι⟩ := mem_unip_std σ W H' g hg
  have inv : ∀ v w, hA σ W.J (mat g *ᵥ v) (mat g *ᵥ w) = hA σ W.J v w := hA_mat_eq σ g
  have dec := decomp_eq (F := F) H'.x H'.y H'.ι hdec
  obtain ⟨α, γ, β, hgY⟩ := dec (mat g *ᵥ incV F H'.y)
  have hγ : γ = 1 := by
    have h := inv (incV F H'.y) (incV F H'.x)
    rw [hgX, hgY] at h
    simp only [hA_add_l, hA_smul_l, hXX, hιX, hYX] at h
    linear_combination -h
  subst hγ
  have ha : ∀ z (a : AE F E), mat g *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x →
      a = -hA σ W.J (incM F H'.ι *ᵥ z) (incM F H'.ι *ᵥ β) := by
    intro z a h
    have h2 := inv (incM F H'.ι *ᵥ z) (incV F H'.y)
    rw [h, hgY] at h2
    simp only [hA_add_l, hA_add_r, hA_smul_l, hA_smul_r, hXX, hXY, hιX, hιY, hXι, mul_zero, mul_one, zero_add,
      add_zero, one_smul] at h2
    linear_combination h2
  have hα : α - cA σ α = -hA σ W.J (incM F H'.ι *ᵥ β) (incM F H'.ι *ᵥ β) := by
    have h3 := inv (incV F H'.y) (incV F H'.y)
    rw [hgY] at h3
    simp only [hA_add_l, hA_add_r, hA_smul_l, hA_smul_r, hXX, hXY, hYX, hYY, hιX, hιY, hXι, hYι, mul_zero, mul_one,
      zero_add, add_zero, one_smul, one_mul] at h3
    linear_combination h3
  refine ⟨β, α, hα, ?_⟩
  have key : ∀ v, mat g *ᵥ v = nmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ β) α *ᵥ v := by
    intro v
    obtain ⟨s, t, z, rfl⟩ := dec v
    obtain ⟨a, hz⟩ := hgι z
    have ha' := ha z a hz
    rw [nmat_mulVec]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hgX, hz, hgY, hA_add_l, hA_smul_l, hXX, hιX, hYX, hXι, hYι,
      mul_zero, zero_add, add_zero, one_smul]
    rw [ha']
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  ext i j
  have h4 := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using h4

end GlobalTheory.UnipMass.StdMat
end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_pair_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ a, σ (σ a) = a) → ∀ (d d₁ : ℕ) (W : Spc F E d) (H' : Plane E d d₁), (∀ i j, σ (W.J j i) = -W.J i j) → form σ W.J H'.x H'.x = 0 → form σ W.J H'.y H'.y = 0 → form σ W.J H'.x H'.y = 1 → (∀ u, form σ W.J (H'.ι *ᵥ u) H'.x = 0 ∧ form σ W.J (H'.ι *ᵥ u) H'.y = 0) → (∀ v : Fin d → E, ∃ (s t : E) (u : Fin d₁ → E), v = s • H'.x + H'.ι *ᵥ u + t • H'.y) → ∀ g ∈ unip σ W H', ∃ (b : Fin d₁ → AE F E) (c : AE F E), c - cA σ c = -hA σ W.J (incM F H'.ι *ᵥ b) (incM F H'.ι *ᵥ b) ∧ mat g = nmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ b) c := by
  first | exact @GlobalTheory.UnipMass.StdMat.unip_eq_nmat | exact GlobalTheory.UnipMass.StdMat.unip_eq_nmat | (intros; apply GlobalTheory.UnipMass.StdMat.unip_eq_nmat <;> assumption)
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.UnipMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_inclR (σ : E →ₐ[F] E) (a : E) : cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := by
  show Algebra.TensorProduct.map _ _ ((1 : AF F) ⊗ₜ[F] a) = (1 : AF F) ⊗ₜ[F] σ a
  simp

theorem cA_cA {σ : E →ₐ[F] E} (hσ : ∀ a, σ (σ a) = a) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => show Algebra.TensorProduct.map _ _ (Algebra.TensorProduct.map _ _ (a ⊗ₜ[F] x)) = a ⊗ₜ[F] x; simp [hσ]

theorem hA_skew {σ : E →ₐ[F] E} (hσ : ∀ a, σ (σ a) = a) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (v w : Fin n → AE F E) : cA σ (hA σ J v w) = -hA σ J w v := by
  simp only [hA, dotProduct, Matrix.mulVec, map_sum, map_mul, cA_cA hσ, incM, Matrix.map_apply, cA_inclR]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hJ y x, map_neg]
  ring

theorem hA_incV (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w : Fin n → E) :
    hA σ J (incV F v) (incV F w) = inclR (F := F) (AF F) (form σ J v w) := by
  simp only [hA, form, incV, incM, dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.map_apply, cA_inclR]

theorem incM_mulVec_incV {m n : ℕ} (A : Matrix (Fin m) (Fin n) E) (v : Fin n → E) :
    incM F A *ᵥ incV F v = incV F (A *ᵥ v) := by
  ext i
  simp only [incM, incV, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

theorem hA_add_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v v' w : Fin n → AE F E) :
    hA σ J (v + v') w = hA σ J v w + hA σ J v' w := add_dotProduct _ _ _

theorem hA_add_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w w' : Fin n → AE F E) :
    hA σ J v (w + w') = hA σ J v w + hA σ J v w' := by
  simp only [hA, Pi.add_apply, map_add]
  rw [show (fun i => cA σ (w i) + cA σ (w' i)) = (fun i => cA σ (w i)) + fun i => cA σ (w' i) from rfl,
    Matrix.mulVec_add, dotProduct_add]

theorem hA_neg_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w : Fin n → AE F E) :
    hA σ J (-v) w = -hA σ J v w := neg_dotProduct _ _

theorem hA_neg_right' (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w : Fin n → AE F E) :
    hA σ J v (-w) = -hA σ J v w := by
  simp only [hA, Pi.neg_apply, map_neg]
  rw [show (fun i => -cA σ (w i)) = -(fun i => cA σ (w i)) from rfl, Matrix.mulVec_neg, dotProduct_neg]

theorem hA_zero_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Fin n → AE F E) :
    hA σ J v 0 = 0 := by
  simp only [hA, Pi.zero_apply, map_zero]
  rw [show (fun _ : Fin n => (0 : AE F E)) = 0 from rfl, Matrix.mulVec_zero, dotProduct_zero]

theorem hA_zero_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Fin n → AE F E) :
    hA σ J 0 v = 0 := by simp [hA]

theorem nmat_rat (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x u : Fin n → E) (c : E) :
    nmat σ J (incV F x) (incV F u) (inclR (F := F) (AF F) c) =
      (1 - Matrix.vecMulVec (u + c • x) (J *ᵥ fun i => σ (x i)) - Matrix.vecMulVec x (J *ᵥ fun i => σ (u i))).map
        (inclR (F := F) (AF F)) := by
  ext i j
  simp only [nmat, incV, incM, Matrix.map_apply, Matrix.sub_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
    map_sub, map_mul, map_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, cA_inclR, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.UnipMass

namespace GlobalTheory.UnipMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem nmat_zero (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → AE F E) :
    nmat σ J x 0 0 = 1 := by
  simp only [nmat, zero_smul, add_zero, Pi.zero_apply, map_zero]
  rw [show (fun _ : Fin n => (0 : AE F E)) = 0 from rfl, Matrix.mulVec_zero]
  simp

structure Hyp (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) : Prop where
  σσ : ∀ a, σ (σ a) = a
  skew : ∀ i j, σ (W.J j i) = -W.J i j
  xx : hA σ W.J (incV F H'.x) (incV F H'.x) = 0
  ιx : ∀ z, hA σ W.J (incM F H'.ι *ᵥ z) (incV F H'.x) = 0

variable {σ : E →ₐ[F] E} {d d₁ : ℕ} {W : Spc F E d} {H' : Plane E d d₁}

theorem Hyp.xι (h : Hyp σ W H') (z : Fin d₁ → AE F E) : hA σ W.J (incV F H'.x) (incM F H'.ι *ᵥ z) = 0 := by
  have := hA_skew h.σσ h.skew (incM F H'.ι *ᵥ z) (incV F H'.x)
  rw [h.ιx z, map_zero] at this
  exact neg_eq_zero.1 this.symm

theorem mem_unip (h : Hyp σ W H') (g : UA σ W.J) (b : Fin d₁ → AE F E) (c : AE F E)
    (hg : mat g = nmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ b) c) : g ∈ unip σ W H' := by
  refine Subgroup.subset_closure ⟨?_, fun z => ⟨-hA σ W.J (incM F H'.ι *ᵥ z) (incM F H'.ι *ᵥ b), ?_⟩⟩
  · rw [hg, nmat_mulVec, h.xx, h.xι]; simp
  · rw [hg, nmat_mulVec, h.ιx]; simp [sub_eq_add_neg]

theorem nmat_mul (h : Hyp σ W H') (b b' : Fin d₁ → AE F E) (c c' : AE F E) :
    nmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ b) c * nmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ b') c' =
      nmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ (b + b')) (c + c' - hA σ W.J (incM F H'.ι *ᵥ b') (incM F H'.ι *ᵥ b)) := by
  rw [GlobalTheory.T.heisenberg_matrix_mul F E σ h.σσ d W.J h.skew _ _ _ c c' h.xx (h.ιx b) (h.ιx b'), Matrix.mulVec_add]

def elt (h : Hyp σ W H') (b : Fin d₁ → AE F E) (c : AE F E)
    (hc : c - cA σ c = -hA σ W.J (incM F H'.ι *ᵥ b) (incM F H'.ι *ᵥ b)) : unip σ W H' :=
  ⟨⟨⟨nmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ b) c,
    nmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ -b) (-c - hA σ W.J (incM F H'.ι *ᵥ b) (incM F H'.ι *ᵥ b)),
    by rw [nmat_mul h, add_neg_cancel, Matrix.mulVec_neg, hA_neg_left, show c + (-c - hA σ W.J (incM F H'.ι *ᵥ b)
        (incM F H'.ι *ᵥ b)) - -hA σ W.J (incM F H'.ι *ᵥ b) (incM F H'.ι *ᵥ b) = 0 by ring, Matrix.mulVec_zero, nmat_zero],
    by rw [nmat_mul h, neg_add_cancel, Matrix.mulVec_neg, hA_neg_right', show -c - hA σ W.J (incM F H'.ι *ᵥ b)
        (incM F H'.ι *ᵥ b) + c - -hA σ W.J (incM F H'.ι *ᵥ b) (incM F H'.ι *ᵥ b) = 0 by ring, Matrix.mulVec_zero, nmat_zero]⟩,
    GlobalTheory.T.heisenberg_matrix_preserves_form F E σ h.σσ d W.J h.skew _ _ c h.xx (h.ιx b) hc⟩,
    mem_unip h _ b c rfl⟩

theorem mat_elt (h : Hyp σ W H') (b : Fin d₁ → AE F E) (c : AE F E) (hc) :
    mat ((elt h b c hc : unip σ W H') : UA σ W.J) = nmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ b) c := rfl

theorem unip_ext {g g' : unip σ W H'} (e : mat (g : UA σ W.J) = mat (g' : UA σ W.J)) : g = g' :=
  Subtype.ext (Subtype.ext (Units.ext e))

end GlobalTheory.UnipMass

namespace GlobalTheory.UnipMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_range_of {n : ℕ} (g : GL (Fin n) (AE F E)) (M M' : Matrix (Fin n) (Fin n) E)
    (h1 : (g : Matrix (Fin n) (Fin n) (AE F E)) = M.map (inclR (F := F) (AF F)))
    (h2 : ((g⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) = M'.map (inclR (F := F) (AF F))) :
    g ∈ (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range := by
  have inj : Function.Injective fun N : Matrix (Fin n) (Fin n) E => N.map (inclR (F := F) (AF F)) :=
    Matrix.map_injective (Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F))
  have e1 : M * M' = 1 := inj (by
    simp only
    rw [Matrix.map_mul (f := inclR (F := F) (AF F)), ← h1, ← h2, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
  have e2 : M' * M = 1 := inj (by
    simp only
    rw [Matrix.map_mul (f := inclR (F := F) (AF F)), ← h1, ← h2, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])
  exact ⟨⟨M, M', e1, e2⟩, Units.ext (by simp [Matrix.GeneralLinearGroup.map, h1])⟩

def nE (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x u : Fin n → E) (c : E) : Matrix (Fin n) (Fin n) E :=
  1 - Matrix.vecMulVec (u + c • x) (J *ᵥ fun i => σ (x i)) - Matrix.vecMulVec x (J *ᵥ fun i => σ (u i))

variable {σ : E →ₐ[F] E} {d d₁ : ℕ} {W : Spc F E d} {H' : Plane E d d₁}

theorem elt_rat (h : Hyp σ W H') (b₀ : Fin d₁ → E) (c₀ : E) (hc) :
    ((elt h (incV F b₀) (inclR (F := F) (AF F) c₀) hc : unip σ W H') : UA σ W.J) ∈ ratU σ W.J := by
  refine Subgroup.mem_subgroupOf.2 (mem_range_of _ (nE σ W.J H'.x (H'.ι *ᵥ b₀) c₀)
    (nE σ W.J H'.x (H'.ι *ᵥ -b₀) (-c₀ - form σ W.J (H'.ι *ᵥ b₀) (H'.ι *ᵥ b₀))) ?_ ?_)
  · exact (congrArg (fun u => nmat σ W.J (incV F H'.x) u _) (incM_mulVec_incV _ _)).trans (nmat_rat σ W.J _ _ c₀)
  · show nmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ -incV F b₀) (-inclR (F := F) (AF F) c₀ -
      hA σ W.J (incM F H'.ι *ᵥ incV F b₀) (incM F H'.ι *ᵥ incV F b₀)) = _
    rw [show -incV F b₀ = incV F (-b₀) from funext fun i => (map_neg (inclR (F := F) (AF F)) (b₀ i)).symm, incM_mulVec_incV, incM_mulVec_incV,
      hA_incV, ← map_neg, ← map_sub]
    exact nmat_rat σ W.J _ _ _

end GlobalTheory.UnipMass

namespace GlobalTheory.UnipMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hA_incM_incV (σ : E →ₐ[F] E) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) (Fin m) E)
    (z : Fin m → AE F E) (v : Fin n → E) :
    hA σ J (incM F A *ᵥ z) (incV F v) = ∑ j, z j * inclR (F := F) (AF F) (form σ J (fun i => A i j) v) := by
  simp only [hA, form, dotProduct, Matrix.mulVec, incM, incV, Matrix.map_apply, cA_inclR, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem topUA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    IsTopologicalGroup (UA σ J) ∧ LocallyCompactSpace (UA σ J) ∧ SecondCountableTopology (UA σ J) ∧
      T2Space (UA σ J) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AE F E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (Fin n) (AE F E)) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin n) (AE F E)) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : T2Space (GL (Fin n) (AE F E)) := Units.isEmbedding_embedProduct.t2Space
  have hs : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hc : IsClosed (UG (cA σ) (incM F J) : Set (GL (Fin n) (AE F E))) := by
    have hv : Continuous fun g : GL (Fin n) (AE F E) => (g : Matrix (Fin n) (Fin n) (AE F E)) := Units.continuous_val
    exact isClosed_eq ((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul (hv.matrix_map hs))
      continuous_const
  exact ⟨inferInstance, hc.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    hc.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology,
    inferInstanceAs (T2Space (UG (cA σ) (incM F J)))⟩

theorem countable_ratU' (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (N : Subgroup (UA σ J)) :
    Countable ((ratU σ J).subgroupOf N) := by
  haveI : Countable E := Function.Injective.countable (Module.finBasis ℚ E).equivFun.injective
  haveI : Countable (GL (Fin n) E) :=
    Function.Injective.countable (f := fun (g : GL (Fin n) E) (i j : Fin n) => (g : Matrix (Fin n) (Fin n) E) i j)
      fun _ _ h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j)
  haveI := (Set.countable_range (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)))).to_subtype
  exact Function.Injective.countable
    (f := fun γ : (ratU σ J).subgroupOf N => (⟨γ.1.1.1, Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 γ.2)⟩ :
      Set.range (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)))))
    fun γ γ' h => Subtype.val_injective (Subtype.val_injective (Subtype.val_injective (congrArg Subtype.val h :)))

theorem continuous_nmat (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → AE F E) {X : Type}
    [TopologicalSpace X] {u : X → Fin n → AE F E} {c : X → AE F E} (hu : Continuous u) (hc : Continuous c) :
    Continuous fun p => nmat σ J x (u p) (c p) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hs : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  unfold nmat
  refine (continuous_const.sub ?_).sub ?_
  · exact (hu.add (hc.smul continuous_const)).matrix_vecMulVec continuous_const
  · exact continuous_const.matrix_vecMulVec
      (continuous_const.matrix_mulVec (continuous_pi fun i => hs.comp ((continuous_apply i).comp hu)))

end GlobalTheory.UnipMass

namespace GlobalTheory.UnipMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {d d₁ : ℕ} {W : Spc F E d} {H' : Plane E d d₁}

theorem cocompact (h : Hyp σ W H') (hxx : form σ W.J H'.x H'.x = 0) (hyy : form σ W.J H'.y H'.y = 0)
    (hxy : form σ W.J H'.x H'.y = 1)
    (horth : ∀ u, form σ W.J (H'.ι *ᵥ u) H'.x = 0 ∧ form σ W.J (H'.ι *ᵥ u) H'.y = 0)
    (hspan : ∀ v : Fin d → E, ∃ (s t : E) (u : Fin d₁ → E), v = s • H'.x + H'.ι *ᵥ u + t • H'.y) :
    ∃ K : Set (unip σ W H'), IsCompact K ∧
      ∀ g : unip σ W H', ∃ γ : (ratU σ W.J).subgroupOf (unip σ W H'), γ • g ∈ K := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hs : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  obtain ⟨KE, hKE, hcov⟩ := GlobalTheory.T.adele_quotient_compact_fundamental_set F E
  set ι := incM F H'.ι with hι
  set half : AE F E := inclR (F := F) (AF F) (2⁻¹ : E) with hhalf_def
  have hhalf : (2 : AE F E) * half = 1 := by
    rw [hhalf_def, ← map_ofNat (inclR (F := F) (AF F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  have hσhalf : cA σ half = half := by rw [hhalf_def, cA_inclR, map_inv₀, map_ofNat]
  have hsk : ∀ v w, cA σ (hA σ W.J v w) = -hA σ W.J w v := hA_skew h.σσ h.skew
  let cf : (Fin d₁ → AE F E) → AE F E → AE F E :=
    fun b k => half * (k + cA σ k) - half * hA σ W.J (ι *ᵥ b) (ι *ᵥ b)
  have hcf : ∀ b k, cf b k - cA σ (cf b k) = -hA σ W.J (ι *ᵥ b) (ι *ᵥ b) := by
    intro b k
    simp only [cf, map_sub, map_mul, map_add, hσhalf, cA_cA h.σσ, hsk]
    linear_combination (-hA σ W.J (ι *ᵥ b) (ι *ᵥ b)) * hhalf
  let Q : (Fin d₁ → AE F E) × AE F E → unip σ W H' := fun p => elt h p.1 (cf p.1 p.2) (hcf p.1 p.2)
  have hcfc : Continuous fun p : (Fin d₁ → AE F E) × AE F E => cf p.1 p.2 := by
    have hh : Continuous fun p : (Fin d₁ → AE F E) × AE F E => hA σ W.J (ι *ᵥ p.1) (ι *ᵥ p.1) := by
      unfold hA
      exact (continuous_const.matrix_mulVec continuous_fst).dotProduct (continuous_const.matrix_mulVec
        (continuous_pi fun i => hs.comp ((continuous_apply i).comp (continuous_const.matrix_mulVec continuous_fst))))
    exact (continuous_const.mul (continuous_snd.add (hs.comp continuous_snd))).sub (continuous_const.mul hh)
  have hQ : Continuous Q := by
    refine Continuous.subtype_mk (Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _) _
    · exact continuous_nmat σ W.J _ (continuous_const.matrix_mulVec continuous_fst) hcfc
    · have hh : Continuous fun p : (Fin d₁ → AE F E) × AE F E => hA σ W.J (ι *ᵥ p.1) (ι *ᵥ p.1) := by
        unfold hA
        exact (continuous_const.matrix_mulVec continuous_fst).dotProduct (continuous_const.matrix_mulVec
          (continuous_pi fun i => hs.comp ((continuous_apply i).comp (continuous_const.matrix_mulVec continuous_fst))))
      exact continuous_nmat σ W.J _ (continuous_const.matrix_mulVec continuous_fst.neg) (hcfc.neg.sub hh)
  refine ⟨Q '' (Set.univ.pi (fun _ => KE) ×ˢ KE), ((isCompact_univ_pi fun _ => hKE).prod hKE).image hQ, fun g => ?_⟩
  obtain ⟨b, c, hc, hg⟩ := GlobalTheory.T.hyperbolic_pair_decomposition F E σ h.σσ d d₁ W H' h.skew hxx hyy hxy horth hspan g g.2
  choose e he using fun j => hcov (b j)
  set u₀ := ι *ᵥ incV F (-e) with hu₀
  set c₁E : E := -(2⁻¹ * form σ W.J (H'.ι *ᵥ -e) (H'.ι *ᵥ -e)) with hc₁E
  have hhu₀ : hA σ W.J u₀ u₀ = inclR (F := F) (AF F) (form σ W.J (H'.ι *ᵥ -e) (H'.ι *ᵥ -e)) := by
    rw [hu₀, hι, incM_mulVec_incV, hA_incV]
  have hc₁ : inclR (F := F) (AF F) c₁E - cA σ (inclR (F := F) (AF F) c₁E) = -hA σ W.J u₀ u₀ := by
    have e1 : inclR (F := F) (AF F) c₁E = -(half * hA σ W.J u₀ u₀) := by
      rw [hhu₀, hc₁E, map_neg, map_mul, hhalf_def]
    rw [e1, map_neg, map_mul, hσhalf, hsk]
    linear_combination (-hA σ W.J u₀ u₀) * hhalf
  let γ₁ : (ratU σ W.J).subgroupOf (unip σ W H') := ⟨elt h (incV F (-e)) _ hc₁, elt_rat h _ _ hc₁⟩
  set c₂ := inclR (F := F) (AF F) c₁E + c - hA σ W.J (ι *ᵥ b) u₀ with hc₂_def
  set b' : Fin d₁ → AE F E := incV F (-e) + b with hb'_def
  have hm1 : mat ((γ₁ • g : unip σ W H') : UA σ W.J) = nmat σ W.J (incV F H'.x) (ι *ᵥ b') c₂ := by
    show nmat σ W.J (incV F H'.x) u₀ (inclR (F := F) (AF F) c₁E) * mat (g : UA σ W.J) = _
    rw [hg, hu₀, nmat_mul h]
  have hc₂ : c₂ - cA σ c₂ = -hA σ W.J (ι *ᵥ b') (ι *ᵥ b') := by
    rw [hb'_def, Matrix.mulVec_add, ← hu₀, hA_add_left, hA_add_right, hA_add_right, hc₂_def]
    simp only [map_add, map_sub]
    linear_combination hc₁ + hc + hsk (ι *ᵥ b) u₀
  set s := half * (c₂ + cA σ c₂) with hs_def
  have hσs : cA σ s = s := by rw [hs_def, map_mul, hσhalf, map_add, cA_cA h.σσ, add_comm (cA σ c₂)]
  obtain ⟨e', he'⟩ := hcov s
  set k := s - inclR (F := F) (AF F) e' with hk_def
  set e₀ : E := -(2⁻¹ * (e' + σ e')) with he₀_def
  have hσe₀ : σ e₀ = e₀ := by
    rw [he₀_def, map_neg, map_mul, map_add, h.σσ, map_inv₀, map_ofNat, add_comm (σ e')]
  have h0 : incV F (0 : Fin d₁ → E) = 0 := funext fun _ => map_zero _
  have hc₃ : inclR (F := F) (AF F) e₀ - cA σ (inclR (F := F) (AF F) e₀) =
      -hA σ W.J (ι *ᵥ incV F 0) (ι *ᵥ incV F 0) := by
    rw [cA_inclR, hσe₀, sub_self, h0, Matrix.mulVec_zero, hA_zero_left, neg_zero]
  let γ₂ : (ratU σ W.J).subgroupOf (unip σ W H') := ⟨elt h (incV F 0) _ hc₃, elt_rat h _ _ hc₃⟩
  have key : inclR (F := F) (AF F) e₀ + c₂ = cf b' k := by
    have he₀' : inclR (F := F) (AF F) e₀ =
        -(half * (inclR (F := F) (AF F) e' + inclR (F := F) (AF F) (σ e'))) := by
      rw [he₀_def, map_neg, map_mul, map_add, hhalf_def]
    have hσk : cA σ k = s - inclR (F := F) (AF F) (σ e') := by rw [hk_def, map_sub, hσs, cA_inclR]
    simp only [cf]
    linear_combination he₀' + (-half) * hk_def + (-half) * hσk + half * hc₂ -
      (c₂ * (1 + half) + half * cA σ c₂) * hhalf + (-2 * half) * hs_def
  refine ⟨γ₂ * γ₁, (b', k), ⟨fun j _ => ?_, he'⟩, ?_⟩
  · have : b' j = b j - inclR (F := F) (AF F) (e j) := by
      rw [hb'_def, Pi.add_apply, show incV F (-e) j = -inclR (F := F) (AF F) (e j) from map_neg _ _]
      ring
    show b' j ∈ KE
    rw [this]
    exact he j
  · apply unip_ext
    rw [mul_smul]
    show nmat σ W.J (incV F H'.x) (ι *ᵥ b') (cf b' k) =
      nmat σ W.J (incV F H'.x) (ι *ᵥ incV F 0) (inclR (F := F) (AF F) e₀) * mat ((γ₁ • g : unip σ W H') : UA σ W.J)
    rw [hm1, nmat_mul h, h0, zero_add, Matrix.mulVec_zero, hA_zero_right, sub_zero, key]

end GlobalTheory.UnipMass

namespace GlobalTheory.UnipMass

theorem exists_haar_unip_mass_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ X om om', IsTriple B G X om om' →
      ∃ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure ∧
        IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ ∧ μ 𝓕 = 1 := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' hT
  have hσ : ∀ a, σ (σ a) = a := cm_conj_conj hT.base.cm
  have hW := hT.geo.hW
  have hH := hC.hH'
  have hspan : ∀ v : Fin (b + 2 + a') → E, ∃ (s t : E) (u : Fin (b + a') → E),
      v = s • H'.x + H'.ι *ᵥ u + t • H'.y := by
    intro v
    have hv : v ∈ Submodule.span E (G.W.L : Set (Fin (b + 2 + a') → E)) := by
      rw [hW.lat.span_eq_top]; trivial
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨s, t, u, -, -, -, hz⟩ := hH.split z hz
      exact ⟨s, t, u, hz⟩
    | zero => exact ⟨0, 0, 0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨s, t, u, rfl⟩ := hy
      obtain ⟨s', t', u', rfl⟩ := hz
      exact ⟨s + s', t + t', u + u', by rw [Matrix.mulVec_add]; module⟩
    | smul a y _ hy =>
      obtain ⟨s, t, u, rfl⟩ := hy
      exact ⟨a * s, a * t, a • u, by rw [Matrix.mulVec_smul]; module⟩
  have horthA : ∀ z, hA σ G.W.J (incM F H'.ι *ᵥ z) (incV F H'.x) = 0 := by
    intro z
    rw [hA_incM_incV]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h1 := (hH.orth (Pi.single j 1)).1
    rw [Matrix.mulVec_single_one] at h1
    rw [show (fun i => H'.ι i j) = H'.ι.col j from rfl, h1, map_zero, mul_zero]
  have h : Hyp σ G.W H' := ⟨hσ, hW.skew, by rw [hA_incV, hH.xx, map_zero], horthA⟩
  have hx0 : H'.x ≠ 0 := fun h0 => by
    have h1 := hH.xy
    rw [h0] at h1
    simp [form] at h1
  obtain ⟨hTG, hLC, hSC, hT2⟩ := topUA σ G.W.J
  haveI := hTG
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  have hcl := GlobalTheory.T.unipotent_radical_closed_nonzero F E σ _ _ G.W H' hx0
  haveI : LocallyCompactSpace (unip σ G.W H') := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (unip σ G.W H') :=
    hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI := countable_ratU' σ G.W.J (unip σ G.W H')
  haveI := GlobalTheory.T.discrete_rational_points_subgroup F E σ _ G.W.J (unip σ G.W H')
  obtain ⟨K, hK, hcov⟩ := cocompact h hH.xx hH.yy hH.xy hH.orth hspan
  exact GlobalTheory.T.cocompact_lattice_unit_covolume _ _ K hK hcov

end GlobalTheory.UnipMass
end
end
