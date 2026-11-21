import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MapInclKMemTwCentResOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigResIterateEqSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigIterateApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySimilitudeIntegralSubgroupCommensuratedFrStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatesSeparableMatrixCompactModCentralizer
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtC
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedExtensionProductDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlPiEquivSymmContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFinitenessSeparableNormStatement

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinCmd

theorem exists_finset_mul_eq_of_relIndex {H : Type} [Group H] (K : Subgroup H) (s : H)
    (h : (K.map (MulAut.conj s).toMonoidHom).relIndex K ≠ 0) :
    ∃ S : Finset H, ∀ k ∈ K, ∃ s' ∈ S, ∃ k' ∈ K, k * s = s' * k' := by
  set L := K.map (MulAut.conj s).toMonoidHom with hL
  haveI : Finite (K ⧸ L.subgroupOf K) := by
    haveI : (L.subgroupOf K).FiniteIndex := ⟨h⟩
    exact Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (K ⧸ L.subgroupOf K) := Fintype.ofFinite _
  refine ⟨Finset.univ.image fun q : K ⧸ L.subgroupOf K => ((Quotient.out q : K) : H) * s, ?_⟩
  intro k hk
  set q : K ⧸ L.subgroupOf K := QuotientGroup.mk ⟨k, hk⟩
  have hq : (Quotient.out q)⁻¹ * (⟨k, hk⟩ : K) ∈ L.subgroupOf K := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  rw [Subgroup.mem_subgroupOf] at hq
  obtain ⟨x, hx, hxe⟩ := hq
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hxe
  refine ⟨((Quotient.out q : K) : H) * s, Finset.mem_image_of_mem _ (Finset.mem_univ _), x, hx, ?_⟩
  have : k = ((Quotient.out q : K) : H) * (s * x * s⁻¹) := by
    rw [hxe, mul_inv_cancel_left]
  rw [this]
  group

end GlobalTheory.OrbFinCmd

open GlobalTheory.OrbFinCmd in

theorem GlobalTheory.orbFin_KHT_cmd :
    ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → ∀ s : Gr G r, ∃ S : Finset (Gr G r),
      ∀ k ∈ KHT p G.m G.n r G.Fw, ∃ s' ∈ S, ∃ k' ∈ KHT p G.m G.n r G.Fw, k * s = s' * k' := by
  intro p _ G r hr s
  exact exists_finset_mul_eq_of_relIndex _ s ((GlobalTheory.T.unitarySimilitudeIntegralSubgroup_commensurated_frobenius p G r hr).1 s).1
end
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_left_coset_representatives : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → ∀ s : Gr G r, ∃ S : Finset (Gr G r), ∀ k ∈ KHT p G.m G.n r G.Fw, ∃ s' ∈ S, ∃ k' ∈ KHT p G.m G.n r G.Fw, k * s = s' * k' := by
  first | (exact @GlobalTheory.orbFin_KHT_cmd) | (exact GlobalTheory.orbFin_KHT_cmd) | (intros; apply GlobalTheory.orbFin_KHT_cmd <;> assumption)
end

section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKLoc

namespace GlobalTheory.LKLoc

theorem mem_intR_iff_norm_le_one (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ)
    (x : Kn p K r) : x ∈ intR p K r ↔ ‖x‖ ≤ 1 := by
  change (x : PadicAlgCl p) ∈ Obar p ↔ _
  exact mem_Obar_iff

theorem mem_Kint_iff_integral_entries (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ)
    (g : GL (Fin n) (Kn p K r)) :
    g ∈ Kint p K n r ↔ (∀ i j, (g : Matrix (Fin n) (Fin n) (Kn p K r)) i j ∈ intR p K r) ∧
      (∀ i j, ((g⁻¹ : GL (Fin n) (Kn p K r)) : Matrix (Fin n) (Fin n) (Kn p K r)) i j ∈ intR p K r) := by
  constructor
  · rintro ⟨A, rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · change ((A : Matrix (Fin n) (Fin n) (intR p K r)) i j : Kn p K r) ∈ intR p K r
      exact SetLike.coe_mem _
    · rw [← map_inv]
      change (((A⁻¹ : GL (Fin n) (intR p K r)) : Matrix (Fin n) (Fin n) (intR p K r)) i j : Kn p K r) ∈ intR p K r
      exact SetLike.coe_mem _
  · rintro ⟨h1, h2⟩
    let B : Matrix (Fin n) (Fin n) (intR p K r) := Matrix.of fun i j => ⟨_, h1 i j⟩
    let C : Matrix (Fin n) (Fin n) (intR p K r) := Matrix.of fun i j => ⟨_, h2 i j⟩
    have hB : B.map (intR p K r).subtype = (g : Matrix (Fin n) (Fin n) (Kn p K r)) := by
      ext i j; rfl
    have hC : C.map (intR p K r).subtype = ((g⁻¹ : GL (Fin n) (Kn p K r)) : Matrix (Fin n) (Fin n) (Kn p K r)) := by
      ext i j; rfl
    have inj : Function.Injective (fun M : Matrix (Fin n) (Fin n) (intR p K r) => M.map (intR p K r).subtype) := by
      intro M N h
      funext i j
      exact Subtype.ext (congrFun (congrFun h i) j)
    have hBC : B * C = 1 := inj (by
      simp only
      rw [Matrix.map_mul, hB, hC, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.mul_inv)
    have hCB : C * B = 1 := inj (by
      simp only
      rw [Matrix.map_mul, hB, hC, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.inv_mul)
    refine ⟨⟨B, C, hBC, hCB⟩, ?_⟩
    ext i j
    rfl

theorem isCompact_Kint (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K)
    (n r : ℕ) (hr : 0 < r) : IsCompact (Kint p K n r : Set (GL (Fin n) (Kn p K r))) := by
  haveI : FiniteDimensional ℚ_[p] (Kn p K r) := finiteDimensional_Kn p K hK hr
  haveI : ProperSpace (Kn p K r) := FiniteDimensional.proper ℚ_[p] (Kn p K r)
  set L := Kn p K r
  let Mset : Set (Matrix (Fin n) (Fin n) L) := {A | ∀ i j, A i j ∈ intR p K r}
  have hMset : Mset = Set.univ.pi (fun _ : Fin n => Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : L) 1) := by
    ext A
    show (∀ i j, A i j ∈ intR p K r) ↔ _
    constructor
    · intro h i _ j _
      show A i j ∈ Metric.closedBall (0 : L) 1
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (mem_intR_iff_norm_le_one p K r _).1 (h i j)
    · intro h i j
      have h' : A i j ∈ Metric.closedBall (0 : L) 1 := h i trivial j trivial
      rw [Metric.mem_closedBall, dist_zero_right] at h'
      exact (mem_intR_iff_norm_le_one p K r _).2 h'
  have hM : IsCompact Mset := by
    rw [hMset]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hM' : IsCompact (MulOpposite.unop ⁻¹' Mset) := by
    have : MulOpposite.unop ⁻¹' Mset = MulOpposite.op '' Mset :=
      Set.ext fun x => ⟨fun h => ⟨x.unop, h, rfl⟩, by rintro ⟨y, hy, rfl⟩; exact hy⟩
    rw [this]
    exact hM.image MulOpposite.continuous_op
  let S : Set (Matrix (Fin n) (Fin n) L × (Matrix (Fin n) (Fin n) L)ᵐᵒᵖ) :=
    (Mset ×ˢ (MulOpposite.unop ⁻¹' Mset)) ∩ {x | x.1 * x.2.unop = 1} ∩ {x | x.2.unop * x.1 = 1}
  have hS : IsCompact S := by
    have hc1 : Continuous fun x : Matrix (Fin n) (Fin n) L × (Matrix (Fin n) (Fin n) L)ᵐᵒᵖ => x.1 * x.2.unop :=
      continuous_fst.matrix_mul (MulOpposite.continuous_unop.comp continuous_snd)
    have hc2 : Continuous fun x : Matrix (Fin n) (Fin n) L × (Matrix (Fin n) (Fin n) L)ᵐᵒᵖ => x.2.unop * x.1 :=
      (MulOpposite.continuous_unop.comp continuous_snd).matrix_mul continuous_fst
    exact ((hM.prod hM').inter_right (isClosed_eq hc1 continuous_const)).inter_right
      (isClosed_eq hc2 continuous_const)
  rw [Units.isEmbedding_embedProduct.isCompact_iff]
  convert hS using 1
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨h1, h2⟩ := (mem_Kint_iff_integral_entries p K n r u).1 hu
    exact ⟨⟨⟨h1, h2⟩, u.mul_inv⟩, u.inv_mul⟩
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨⟨x.1, x.2.unop, h3, h4⟩, (mem_Kint_iff_integral_entries p K n r _).2 ⟨h1, h2⟩, ?_⟩
    rfl

end GlobalTheory.LKLoc
end

section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKLoc

namespace GlobalTheory.LKLoc

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem isOpen_intR (r : ℕ) : IsOpen ((intR p K r : Subring (Kn p K r)) : Set (Kn p K r)) := by
  have h : ((intR p K r : Subring (Kn p K r)) : Set (Kn p K r)) =
      (Subtype.val : Kn p K r → PadicAlgCl p) ⁻¹' Metric.closedBall 0 1 := by
    ext x
    simp only [intR, Subring.coe_comap, Set.mem_preimage, SetLike.mem_coe, Metric.mem_closedBall, dist_zero_right]
    exact mem_Obar_iff
  rw [h]
  exact (IsUltrametricDist.isOpen_closedBall _ one_ne_zero).preimage continuous_subtype_val

theorem mem_Kint_iff (n r : ℕ) (g : GL (Fin n) (Kn p K r)) :
    g ∈ Kint p K n r ↔ (∀ i j, (g : Matrix (Fin n) (Fin n) (Kn p K r)) i j ∈ intR p K r) ∧
      ∀ i j, ((g⁻¹ : GL (Fin n) (Kn p K r)) : Matrix (Fin n) (Fin n) (Kn p K r)) i j ∈ intR p K r := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simp [GeneralLinearGroup.map]
    · rw [← map_inv]
      simp [GeneralLinearGroup.map]
  · rintro ⟨h1, h2⟩
    let A : Matrix (Fin n) (Fin n) (intR p K r) := Matrix.of fun i j => ⟨_, h1 i j⟩
    let B : Matrix (Fin n) (Fin n) (intR p K r) := Matrix.of fun i j => ⟨_, h2 i j⟩
    have hA : A.map (intR p K r).subtype = (g : Matrix (Fin n) (Fin n) (Kn p K r)) := by
      ext i j; rfl
    have hB : B.map (intR p K r).subtype = ((g⁻¹ : GL (Fin n) (Kn p K r)) : Matrix (Fin n) (Fin n) (Kn p K r)) := by
      ext i j; rfl
    have inj : Function.Injective (fun M : Matrix (Fin n) (Fin n) (intR p K r) => M.map (intR p K r).subtype) :=
      Matrix.map_injective Subtype.val_injective
    have hAB : A * B = 1 := by
      apply inj
      simp only [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.mul_inv
    have hBA : B * A = 1 := by
      apply inj
      simp only [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.inv_mul
    refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
    ext i j
    rfl

theorem isOpen_Kint : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ),
    IsOpen (Kint p K n r : Set (GL (Fin n) (Kn p K r))) := by
  intro p _ K n r
  have hS : IsOpen {M : Matrix (Fin n) (Fin n) (Kn p K r) | ∀ i j, M i j ∈ intR p K r} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_intR p K r).preimage ((continuous_apply j).comp (continuous_apply i))
  have hS' : IsOpen {M : (Matrix (Fin n) (Fin n) (Kn p K r))ᵐᵒᵖ | ∀ i j, (MulOpposite.unop M) i j ∈ intR p K r} :=
    hS.preimage MulOpposite.continuous_unop
  have h : (Kint p K n r : Set (GL (Fin n) (Kn p K r))) = Units.embedProduct _ ⁻¹' (
      {M : Matrix (Fin n) (Fin n) (Kn p K r) | ∀ i j, M i j ∈ intR p K r} ×ˢ
      {M : (Matrix (Fin n) (Fin n) (Kn p K r))ᵐᵒᵖ | ∀ i j, (MulOpposite.unop M) i j ∈ intR p K r}) := by
    ext g
    rw [SetLike.mem_coe, mem_Kint_iff]
    rfl
  rw [h]
  exact (hS.prod hS').preimage Units.continuous_embedProduct

end GlobalTheory.LKLoc
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.OrbFinP

def FinConj {H : Type} [Group H] (U : Subgroup H) (a : H) : Prop :=
  ∀ E : Finset H, ∃ D : Finset H, ∀ x : H, (∃ e ∈ E, ∃ k ∈ U, x⁻¹ * a * x = e * k) →
    ∃ t : H, t * a = a * t ∧ ∃ d ∈ D, ∃ k ∈ U, x = t * d * k

theorem finConj_of_central {H : Type} [Group H] (U : Subgroup H) (a : H) (ha : ∀ x, x * a = a * x) :
    FinConj U a :=
  fun _ => ⟨{1}, fun x _ => ⟨x, ha x, 1, Finset.mem_singleton_self _, 1, U.one_mem, by simp⟩⟩

theorem finConj_prod {H₁ H₂ : Type} [Group H₁] [Group H₂] (U₁ : Subgroup H₁) (U₂ : Subgroup H₂) (a₁ : H₁)
    (a₂ : H₂) (h₁ : FinConj U₁ a₁) (h₂ : FinConj U₂ a₂) : FinConj (U₁.prod U₂) (a₁, a₂) := by
  intro E
  obtain ⟨D₁, hD₁⟩ := h₁ (E.image Prod.fst)
  obtain ⟨D₂, hD₂⟩ := h₂ (E.image Prod.snd)
  refine ⟨D₁ ×ˢ D₂, fun x ⟨e, he, k, hk, hx⟩ => ?_⟩
  have hk' := Subgroup.mem_prod.1 hk
  obtain ⟨t₁, ht₁, d₁, hd₁, k₁, hk₁, hx₁⟩ :=
    hD₁ x.1 ⟨e.1, Finset.mem_image_of_mem _ he, k.1, hk'.1, congrArg Prod.fst hx⟩
  obtain ⟨t₂, ht₂, d₂, hd₂, k₂, hk₂, hx₂⟩ :=
    hD₂ x.2 ⟨e.2, Finset.mem_image_of_mem _ he, k.2, hk'.2, congrArg Prod.snd hx⟩
  exact ⟨(t₁, t₂), Prod.ext ht₁ ht₂, (d₁, d₂), Finset.mem_product.2 ⟨hd₁, hd₂⟩, (k₁, k₂),
    Subgroup.mem_prod.2 ⟨hk₁, hk₂⟩, Prod.ext hx₁ hx₂⟩

theorem finConj_pi {ι : Type} [Fintype ι] {H : ι → Type} [∀ i, Group (H i)] (U : ∀ i, Subgroup (H i))
    (a : ∀ i, H i) (h : ∀ i, FinConj (U i) (a i)) : FinConj (Subgroup.pi Set.univ U) a := by
  intro E
  choose D hD using fun i => h i (E.image fun e => e i)
  refine ⟨Fintype.piFinset D, fun x ⟨e, he, k, hk, hx⟩ => ?_⟩
  choose t ht d hd k' hk' hxe using fun i =>
    hD i (x i) ⟨e i, Finset.mem_image_of_mem _ he, k i, hk i (Set.mem_univ i), congrFun hx i⟩
  exact ⟨t, funext ht, d, Fintype.mem_piFinset.2 hd, k', fun i _ => hk' i, funext hxe⟩

theorem finConj_map {H H' : Type} [Group H] [Group H'] (ψ : H ≃* H') (U : Subgroup H) (U' : Subgroup H')
    (hU : ∀ k, k ∈ U ↔ ψ k ∈ U') (a : H) (h : FinConj U' (ψ a)) : FinConj U a := by
  intro E
  obtain ⟨D, hD⟩ := h (E.image ψ)
  refine ⟨D.image ψ.symm, fun x ⟨e, he, k, hk, hx⟩ => ?_⟩
  obtain ⟨t, ht, d, hd, k', hk', hxe⟩ := hD (ψ x) ⟨ψ e, Finset.mem_image_of_mem _ he, ψ k, (hU k).1 hk,
    by rw [← map_inv, ← map_mul, ← map_mul, hx, map_mul]⟩
  refine ⟨ψ.symm t, ?_, ψ.symm d, Finset.mem_image_of_mem _ hd, ψ.symm k', (hU _).2 (by simpa using hk'), ?_⟩
  · apply ψ.injective; simp [map_mul, ht]
  · apply ψ.injective; simp [map_mul, hxe]

theorem finConj_field {k : Type} [NontriviallyNormedField k] {n : ℕ} (U : Subgroup (GL (Fin n) k))
    (hUo : IsOpen (U : Set (GL (Fin n) k))) (hUc : IsCompact (U : Set (GL (Fin n) k))) (a : GL (Fin n) k)
    (ha : (a : Matrix (Fin n) (Fin n) k).charpoly.Separable) : FinConj U a := by
  intro E
  set Z : Set (Matrix (Fin n) (Fin n) k) := (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k)) ''
    (⋃ e ∈ E, (fun u => e * u) '' (U : Set (GL (Fin n) k))) with hZdef
  have hZ : IsCompact Z := (E.isCompact_biUnion fun e _ =>
    hUc.image (continuous_const.mul continuous_id)).image Units.continuous_val
  obtain ⟨C, hC, hCg⟩ := GlobalTheory.OrbCpt.gl_orbit_cpt (a : Matrix (Fin n) (Fin n) k) ha Z hZ
  have hCi : IsCompact ((fun c => c⁻¹) '' C) := hC.image continuous_inv
  obtain ⟨D, hD⟩ := hCi.elim_finite_subcover (fun d : GL (Fin n) k => (fun u => d * u) '' (U : Set _))
    (fun d => isOpenMap_mul_left d _ hUo)
    (fun y _ => Set.mem_iUnion.2 ⟨y, 1, U.one_mem, mul_one y⟩)
  refine ⟨D, fun x ⟨e, he, u, hu, hx⟩ => ?_⟩
  have hxZ : ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * a *
      ((x⁻¹⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ∈ Z :=
    ⟨x⁻¹ * a * x, Set.mem_iUnion₂.2 ⟨e, he, u, hu, hx.symm⟩, by simp [inv_inv]⟩
  obtain ⟨c, hc, t, ht, hxct⟩ := hCg x⁻¹ hxZ
  obtain ⟨d, hdD, v, hv, hdv⟩ := Set.mem_iUnion₂.1 (hD ⟨c, hc, rfl⟩)
  have ht' : t * a = a * t := Units.ext ht
  refine ⟨t⁻¹, ?_, d, hdD, v, hv, ?_⟩
  · calc t⁻¹ * a = t⁻¹ * (a * t) * t⁻¹ := by group
      _ = t⁻¹ * (t * a) * t⁻¹ := by rw [ht']
      _ = a * t⁻¹ := by group
  · have hdv' : d * v = c⁻¹ := hdv
    rw [mul_assoc, hdv', ← _root_.mul_inv_rev, ← hxct, inv_inv]

def glPi {R S : Type} [CommRing R] [CommRing S] (k n : ℕ) (e : R ≃+* (Fin k → S)) :
    GL (Fin n) R ≃* (Fin k → GL (Fin n) S) :=
  (Units.mapEquiv (e.mapMatrix.trans (matPiEquiv S n k)).toMulEquiv).trans MulEquiv.piUnits

theorem glPi_mem_iff {R S : Type} [CommRing R] [CommRing S] (k n : ℕ) (e : R ≃+* (Fin k → S))
    (A : Subring R) (B : Subring S) (hAB : ∀ x : R, x ∈ A ↔ ∀ i, e x i ∈ B) (g : GL (Fin n) R) :
    g ∈ (GeneralLinearGroup.map (n := Fin n) A.subtype).range ↔
      glPi k n e g ∈ Subgroup.pi Set.univ (fun _ => (GeneralLinearGroup.map (n := Fin n) B.subtype).range) := by
  rw [Subgroup.mem_pi]
  simp only [Set.mem_univ, true_implies, mem_range_map_subtype_iff, hAB]
  constructor
  · rintro ⟨h1, h2⟩ i
    exact ⟨fun a b => h1 a b i, fun a b => h2 a b i⟩
  · intro h
    exact ⟨fun a b i => (h i).1 a b, fun a b i => (h i).2 a b⟩

variable (p : ℕ) [Fact p.Prime]

theorem finConj_res_split (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [hK : FiniteDimensional ℚ_[p] K] (n r : ℕ)
    (k m : ℕ) (hm : 0 < m) (e : KQ p K r ≃+* (Fin k → ReciprocityTheory.DiscreteGroups.LocalClassField.Kn p K m))
    (hint : ∀ x : KQ p K r, x ∈ intKQ p K r ↔ ∀ i, e x i ∈ GlobalTheory.LKLoc.intR p K m)
    (g : GL (Fin n) K) (hg : (g : Matrix (Fin n) (Fin n) K).charpoly.Separable) :
    FinConj (Kres p K n r) (GeneralLinearGroup.map (inclK p K r).toRingHom g) := by
  have hp0 : ‖algebraMap ℚ_[p] (ReciprocityTheory.DiscreteGroups.LocalClassField.Kn p K m) p‖ = (p : ℝ)⁻¹ := by
    show ‖algebraMap ℚ_[p] (PadicAlgCl p) p‖ = _
    rw [PadicAlgCl.norm_extends, Padic.norm_p]
  have hp1 : (p : ℝ)⁻¹ ≠ 1 := inv_ne_one.2 (by exact_mod_cast (Fact.out : p.Prime).one_lt.ne')
  have hp2 : (p : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  letI : NontriviallyNormedField (ReciprocityTheory.DiscreteGroups.LocalClassField.Kn p K m) :=
    NontriviallyNormedField.ofNormNeOne ⟨algebraMap ℚ_[p] (ReciprocityTheory.DiscreteGroups.LocalClassField.Kn p K m) p, ?_, ?_⟩
  rotate_left
  · intro h; rw [h, norm_zero] at hp0; exact hp2 hp0.symm
  · rw [hp0]; exact hp1
  refine finConj_map (glPi _ n e) _ _ (fun k => glPi_mem_iff _ n e _ _ hint k) _ ?_
  refine finConj_pi _ _ fun i => ?_
  refine finConj_field _ (GlobalTheory.LKLoc.isOpen_Kint p K n m) (GlobalTheory.LKLoc.isCompact_Kint p K hK n m hm) _ ?_
  have hmat : ((glPi _ n e (GeneralLinearGroup.map (inclK p K r).toRingHom g) i : GL (Fin n) _) :
      Matrix (Fin n) (Fin n) _) = (g : Matrix (Fin n) (Fin n) K).map
        (((Pi.evalRingHom _ i).comp e.toRingHom).comp (inclK p K r).toRingHom) := by
    ext a b; rfl
  rw [hmat, Matrix.charpoly_map]
  exact hg.map

theorem finConj_res (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [hK : FiniteDimensional ℚ_[p] K] (n r : ℕ)
    (hr : 0 < r) (g : GL (Fin n) K) (hg : (g : Matrix (Fin n) (Fin n) K).charpoly.Separable) :
    FinConj (Kres p K n r) (GeneralLinearGroup.map (inclK p K r).toRingHom g) := by
  obtain ⟨e, τ, -, -, -, -, -, hint⟩ :=
    GlobalTheory.T.unramified_extension_product_decomposition p K hK (ReciprocityTheory.DiscreteGroups.LocalClassField.fK p K) r (ReciprocityTheory.DiscreteGroups.LocalClassField.qK_eq_pow_fK p K hK) hr
  exact finConj_res_split p K n r _ _ (Nat.div_pos (Nat.gcd_le_right _ hr) (Nat.gcd_pos_of_pos_right _ hr))
    e hint g hg

end GlobalTheory.OrbFinP

namespace GlobalTheory.OrbFinP

theorem orbit_fin_p : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → ∀ γ : Gp G, regular₂ G γ →
    ∀ E : Finset (Gr G r), ∃ D : Finset (Gr G r), ∀ x : Gr G r,
      (∃ e ∈ E, ∃ k ∈ KHT p G.m G.n r G.Fw, x⁻¹ * inclG G r γ * x = e * k) →
      ∃ t : Gr G r, t * inclG G r γ = inclG G r γ * t ∧ ∃ d ∈ D, ∃ k ∈ KHT p G.m G.n r G.Fw, x = t * d * k := by
  intro p _ G r hr γ hγ
  have key : FinConj (KHT p G.m G.n r G.Fw) (inclG G r γ) := by
    show FinConj ((GlobalTheory.LKLoc.Kint p (Q0 p) 1 r).prod (Subgroup.pi Set.univ fun i => Kres p (G.Fw i) G.n r))
      (GeneralLinearGroup.scalar (Fin 1) (Units.map (algebraMap ℚ_[p] (Qr p r)).toMonoidHom γ.1),
        fun w => GeneralLinearGroup.map (inclK p (G.Fw w) r).toRingHom (γ.2 w))
    refine finConj_prod _ _ _ _ (finConj_of_central _ _ fun x => ?_)
      (finConj_pi _ _ fun w => finConj_res p (G.Fw w) G.n r hr (γ.2 w) (hγ w))
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [Matrix.mul_apply, mul_comm]
  exact key

end GlobalTheory.OrbFinP
end
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_finite_decomposition : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → ∀ γ : Gp G, regular₂ G γ → ∀ E : Finset (Gr G r), ∃ D : Finset (Gr G r), ∀ x : Gr G r, (∃ e ∈ E, ∃ k ∈ KHT p G.m G.n r G.Fw, x⁻¹ * inclG G r γ * x = e * k) → ∃ t : Gr G r, t * inclG G r γ = inclG G r γ * t ∧ ∃ d ∈ D, ∃ k ∈ KHT p G.m G.n r G.Fw, x = t * d * k := by
  first | (exact @GlobalTheory.OrbFinP.orbit_fin_p) | (exact GlobalTheory.OrbFinP.orbit_fin_p) | (intros; apply GlobalTheory.OrbFinP.orbit_fin_p <;> assumption)
end

section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKLoc

noncomputable section

namespace GlobalTheory.LKLoc.GLOneUnit

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ)

def nv : GL (Fin 1) (Kn p K r) →* ℝ where
  toFun g := ‖((((GeneralLinearGroup.det g : (Kn p K r)ˣ) : Kn p K r) : PadicAlgCl p))‖
  map_one' := by simp
  map_mul' a b := by simp [norm_mul]

theorem nv_apply (g : GL (Fin 1) (Kn p K r)) :
    nv p K r g = ‖(((g : Matrix (Fin 1) (Fin 1) (Kn p K r)) 0 0 : Kn p K r) : PadicAlgCl p)‖ := by
  show ‖((((GeneralLinearGroup.det g : (Kn p K r)ˣ) : Kn p K r) : PadicAlgCl p))‖ = _
  rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]

theorem nv_pos (g : GL (Fin 1) (Kn p K r)) : 0 < nv p K r g := by
  show 0 < ‖((((GeneralLinearGroup.det g : (Kn p K r)ˣ) : Kn p K r) : PadicAlgCl p))‖
  refine norm_pos_iff.2 fun h => (GeneralLinearGroup.det g).ne_zero ?_
  exact Subtype.ext h

theorem nv_inv (g : GL (Fin 1) (Kn p K r)) : nv p K r g⁻¹ = (nv p K r g)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel, map_one])

theorem comm {R : Type} [CommRing R] (a b : GL (Fin 1) R) : a * b = b * a := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply, mul_comm]

theorem mem_intR {x : Kn p K r} : x ∈ intR p K r ↔ ‖(x : PadicAlgCl p)‖ ≤ 1 :=
  mem_Obar_iff

theorem mem_Kint_of_nv (g : GL (Fin 1) (Kn p K r)) (h : nv p K r g = 1) : g ∈ Kint p K 1 r := by
  rw [nv_apply] at h
  have hinv : (((g⁻¹ : GL (Fin 1) (Kn p K r)) : Matrix (Fin 1) (Fin 1) (Kn p K r)) 0 0) *
      ((g : Matrix (Fin 1) (Fin 1) (Kn p K r)) 0 0) = 1 := by
    have := congrArg (fun M : Matrix (Fin 1) (Fin 1) (Kn p K r) => M 0 0) (Units.inv_mul g)
    simpa [Matrix.mul_apply] using this
  have hi : ‖((((g⁻¹ : GL (Fin 1) (Kn p K r)) : Matrix (Fin 1) (Fin 1) (Kn p K r)) 0 0 : Kn p K r) :
      PadicAlgCl p)‖ = 1 := by
    have := congrArg (fun x : Kn p K r => ‖(x : PadicAlgCl p)‖) hinv
    simpa [norm_mul, h] using this
  have h0 : (((g : Matrix (Fin 1) (Fin 1) (Kn p K r)) 0 0 : Kn p K r) : PadicAlgCl p) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h; exact zero_ne_one h
  refine ⟨⟨Matrix.of fun _ _ => ⟨_, (mem_intR p K r).2 h.le⟩,
    Matrix.of fun _ _ => ⟨_, (mem_intR p K r).2 hi.le⟩, ?_, ?_⟩, ?_⟩
  · ext i j; fin_cases i; fin_cases j
    simp [Matrix.mul_apply, h0]
  · ext i j; fin_cases i; fin_cases j
    simp [Matrix.mul_apply, h0]
  · apply GeneralLinearGroup.ext
    intro i j
    fin_cases i; fin_cases j
    rfl

theorem sig_eq_of_mem (g : GL (Fin 1) (Kn p K r))
    (hg : (((g : Matrix (Fin 1) (Fin 1) (Kn p K r)) 0 0 : Kn p K r) : PadicAlgCl p) ∈ K) :
    sig p K 1 r g = g := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i; fin_cases j
  apply Subtype.ext
  exact (frobK p K).commutes ⟨_, hg⟩

theorem mem_twCent_of_mem (δ g : GL (Fin 1) (Kn p K r))
    (hg : (((g : Matrix (Fin 1) (Fin 1) (Kn p K r)) 0 0 : Kn p K r) : PadicAlgCl p) ∈ K) :
    g ∈ GlobalTheory.BCT.twCent (sig p K 1 r) δ := by
  show g * δ = δ * sig p K 1 r g
  rw [sig_eq_of_mem p K r g hg, comm]

theorem exists_decomp (hK : FiniteDimensional ℚ_[p] K) (hr : 0 < r) (δ x : GL (Fin 1) (Kn p K r)) :
    ∃ t ∈ GlobalTheory.BCT.twCent (sig p K 1 r) δ, ∃ k ∈ Kint p K 1 r, x = t * k := by
  obtain ⟨y, hy, hxy⟩ := norm_Kn p K hK hr ((x : Matrix (Fin 1) (Fin 1) (Kn p K r)) 0 0).2
  have hxy' : nv p K r x = ‖y‖ := by rw [nv_apply]; exact hxy
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hxy'
    exact (nv_pos p K r x).ne' hxy'
  let u : (Kn p K r)ˣ := Units.mk0 ⟨y, le_Kn p K r hy⟩ (fun h => hy0 (congrArg Subtype.val h))
  let t : GL (Fin 1) (Kn p K r) :=
    Units.map (Matrix.scalar (Fin 1) : Kn p K r →+* Matrix (Fin 1) (Fin 1) (Kn p K r)).toMonoidHom u
  have ht00 : (((t : Matrix (Fin 1) (Fin 1) (Kn p K r)) 0 0 : Kn p K r) : PadicAlgCl p) = y := by
    simp [t, u]
  refine ⟨t, mem_twCent_of_mem p K r δ t (by rw [ht00]; exact hy), t⁻¹ * x,
    mem_Kint_of_nv p K r _ ?_, (mul_inv_cancel_left t x).symm⟩
  rw [map_mul, nv_inv, hxy', nv_apply, ht00]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.2 hy0)

end GlobalTheory.LKLoc.GLOneUnit

namespace GlobalTheory.LKLoc.GLOneUnit

end GlobalTheory.LKLoc.GLOneUnit
end
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.TwFinGL1

theorem twisted_finiteness_gl1 : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ), 0 < r → ∀ δ N : GL (Fin 1) (Qr p r),
    GlobalTheory.TwFin.TwFin (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) (GlobalTheory.LKLoc.Kint p (Q0 p) 1 r) δ N := by
  intro p _ r hr δ N E
  refine ⟨{1}, fun t _ _ => ?_⟩
  obtain ⟨u, hu, k, hk, htk⟩ :=
    GlobalTheory.LKLoc.GLOneUnit.exists_decomp p (Q0 p) r inferInstance hr δ t
  exact ⟨u, hu, 1, Finset.mem_singleton_self _, k, hk, by rw [htk, mul_one]⟩

end GlobalTheory.TwFinGL1
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_finiteness_gl1_unramified : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ), 0 < r → ∀ δ N : GL (Fin 1) (Qr p r), GlobalTheory.TwFin.TwFin (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) (GlobalTheory.LKLoc.Kint p (Q0 p) 1 r) δ N := by
  first | (exact @GlobalTheory.TwFinGL1.twisted_finiteness_gl1) | (exact GlobalTheory.TwFinGL1.twisted_finiteness_gl1) | (intros; apply GlobalTheory.TwFinGL1.twisted_finiteness_gl1  <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.TwFin

theorem prod {H₁ H₂ : Type} [Group H₁] [Group H₂] (θ₁ : H₁ →* H₁) (θ₂ : H₂ →* H₂) (K₁ : Subgroup H₁)
    (K₂ : Subgroup H₂) (δ₁ N₁ : H₁) (δ₂ N₂ : H₂) (h₁ : TwFin θ₁ K₁ δ₁ N₁) (h₂ : TwFin θ₂ K₂ δ₂ N₂) :
    TwFin (θ₁.prodMap θ₂) (K₁.prod K₂) (δ₁, δ₂) (N₁, N₂) := by
  intro E
  obtain ⟨D₁, hD₁⟩ := h₁ (E.image Prod.fst)
  obtain ⟨D₂, hD₂⟩ := h₂ (E.image Prod.snd)
  refine ⟨D₁ ×ˢ D₂, fun t ht ⟨e, he, k, hk, hte⟩ => ?_⟩
  have ht1 : t.1 * N₁ = N₁ * t.1 := congrArg Prod.fst ht
  have ht2 : t.2 * N₂ = N₂ * t.2 := congrArg Prod.snd ht
  obtain ⟨u₁, hu₁, d₁, hd₁, k₁, hk₁, e₁⟩ :=
    hD₁ t.1 ht1 ⟨e.1, Finset.mem_image_of_mem _ he, k.1, hk.1, congrArg Prod.fst hte⟩
  obtain ⟨u₂, hu₂, d₂, hd₂, k₂, hk₂, e₂⟩ :=
    hD₂ t.2 ht2 ⟨e.2, Finset.mem_image_of_mem _ he, k.2, hk.2, congrArg Prod.snd hte⟩
  refine ⟨(u₁, u₂), ?_, (d₁, d₂), Finset.mem_product.2 ⟨hd₁, hd₂⟩, (k₁, k₂), ⟨hk₁, hk₂⟩, Prod.ext e₁ e₂⟩
  exact Prod.ext hu₁ hu₂

theorem pi {ι : Type} [Fintype ι] [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)] (θ : ∀ i, H i →* H i)
    (K : ∀ i, Subgroup (H i)) (δ N : ∀ i, H i) (h : ∀ i, TwFin (θ i) (K i) (δ i) (N i)) :
    TwFin (Pi.monoidHom fun i => (θ i).comp (Pi.evalMonoidHom H i)) (Subgroup.pi Set.univ K) δ N := by
  intro E
  have h' := fun i => h i (E.image fun x => x i)
  choose D hD using h'
  refine ⟨Fintype.piFinset D, fun t ht ⟨e, he, k, hk, hte⟩ => ?_⟩
  have hi : ∀ i, ∃ u ∈ GlobalTheory.BCT.twCent (θ i) (δ i), ∃ d ∈ D i, ∃ k ∈ K i, t i = u * d * k := fun i =>
    hD i (t i) (congrFun ht i) ⟨e i, Finset.mem_image_of_mem _ he, k i, hk i (Set.mem_univ i), congrFun hte i⟩
  choose u hu d hd k' hk' e' using hi
  refine ⟨u, ?_, d, Fintype.mem_piFinset.2 hd, k', fun i _ => hk' i, funext e'⟩
  funext i
  exact hu i

theorem map_nrmG {H H' : Type} [Group H] [Group H'] (θ : H →* H) (θ' : H' →* H') (f : H →* H')
    (hf : ∀ x, f (θ x) = θ' (f x)) (r : ℕ) (δ : H) : f (nrmG θ r δ) = nrmG θ' r (f δ) := by
  unfold nrmG
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact Function.Semiconj.iterate_right hf i δ

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → ∀ γ : Gp G, regular₂ G γ → ∀ δ z : Gr G r, IsNrm G r γ δ z → ∀ E : Finset (Gr G r), ∃ D : Finset (Gr G r), ∀ t : Gr G r, t * nrmG (sigG G r) r δ = nrmG (sigG G r) r δ * t → (∃ e ∈ E, ∃ k ∈ KHT p G.m G.n r G.Fw, t⁻¹ * δ * sigG G r t = e * k) → ∃ u ∈ GlobalTheory.BCT.twCent (sigG G r) δ, ∃ d ∈ D, ∃ k ∈ KHT p G.m G.n r G.Fw, t = u * d * k := by
  intro p _ G r hr γ hγ δ z hN
  have e2 : ∀ i, (nrmG (sigG G r) r δ).2 i = nrmRes p (G.Fw i) G.n r (δ.2 i) := fun i =>
    map_nrmG (sigG G r) _ ((Pi.evalMonoidHom _ i).comp (MonoidHom.snd _ _)) (fun x => rfl) r δ
  have hsep : ∀ i, (nrmRes p (G.Fw i) G.n r (δ.2 i)).val.charpoly.Separable := by
    intro i
    rw [← e2, hN]
    have h1 : ((z⁻¹ * inclG G r γ * z).2 i).val =
        ((z.2 i)⁻¹).val * (γ.2 i).val.map ((inclK p (G.Fw i) r : G.Fw i →+* KQ p (G.Fw i) r)) * (z.2 i).val := rfl
    rw [h1, Matrix.coe_units_inv, Matrix.charpoly_units_conj', Matrix.charpoly_map]
    exact (hγ i).map
  have key : TwFin (sigG G r) (KHT p G.m G.n r G.Fw) (δ.1, δ.2)
      ((nrmG (sigG G r) r δ).1, (nrmG (sigG G r) r δ).2) :=
    prod _ _ _ _ _ _ _ _ (GlobalTheory.T.twisted_finiteness_gl1_unramified p r hr _ _) (pi _ _ _ _ fun i => by
      rw [e2 i]; exact GlobalTheory.T.twisted_finiteness_separable_norm p (G.Fw i) inferInstance G.n r hr _ (hsep i))
  exact key

end GlobalTheory.TwFin
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_centralizer_decomposition : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → ∀ γ : Gp G, regular₂ G γ → ∀ δ z : Gr G r, IsNrm G r γ δ z → ∀ E : Finset (Gr G r), ∃ D : Finset (Gr G r), ∀ t : Gr G r, t * nrmG (sigG G r) r δ = nrmG (sigG G r) r δ * t → (∃ e ∈ E, ∃ k ∈ KHT p G.m G.n r G.Fw, t⁻¹ * δ * sigG G r t = e * k) → ∃ u ∈ GlobalTheory.BCT.twCent (sigG G r) δ, ∃ d ∈ D, ∃ k ∈ KHT p G.m G.n r G.Fw, t = u * d * k := by
  first | (exact @GlobalTheory.TwFin.main) | (exact GlobalTheory.TwFin.main) | (intros; apply GlobalTheory.TwFin.main <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.TwOrbFin

section Generic

variable {H : Type} [Group H]

def Bnd (K₀ : Subgroup H) (D : Set H) : Prop := ∃ S : Finset H, ∀ d ∈ D, ∃ s ∈ S, ∃ k ∈ K₀, d = s * k

def Cmd (K₀ : Subgroup H) : Prop := ∀ s : H, ∃ S : Finset H, ∀ k ∈ K₀, ∃ s' ∈ S, ∃ k' ∈ K₀, k * s = s' * k'

variable {K₀ : Subgroup H}

theorem Bnd.mono {D E : Set H} (h : D ⊆ E) (hE : Bnd K₀ E) : Bnd K₀ D := by
  obtain ⟨S, hS⟩ := hE
  exact ⟨S, fun d hd => hS d (h hd)⟩

theorem bnd_finset (S : Finset H) : Bnd K₀ {g | ∃ s ∈ S, ∃ k ∈ K₀, g = s * k} :=
  ⟨S, fun _ hd => hd⟩

theorem bnd_singleton (g : H) : Bnd K₀ {g} :=
  ⟨{g}, fun d hd => ⟨g, Finset.mem_singleton_self _, 1, K₀.one_mem, by rw [hd, mul_one]⟩⟩

theorem Bnd.mul (hc : Cmd K₀) {D E : Set H} (hD : Bnd K₀ D) (hE : Bnd K₀ E) :
    Bnd K₀ {g | ∃ d ∈ D, ∃ e ∈ E, g = d * e} := by
  choose Sc hSc using hc
  obtain ⟨S, hS⟩ := hD
  obtain ⟨T, hT⟩ := hE
  refine ⟨S.biUnion fun s => T.biUnion fun t => (Sc t).image (s * ·), ?_⟩
  rintro g ⟨d, hd, e, he, rfl⟩
  obtain ⟨s, hs, k, hk, rfl⟩ := hS d hd
  obtain ⟨t, ht, l, hl, rfl⟩ := hT e he
  obtain ⟨s', hs', k', hk', e'⟩ := hSc t k hk
  refine ⟨s * s', Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_biUnion.2 ⟨t, ht, Finset.mem_image.2 ⟨s', hs', rfl⟩⟩⟩,
    k' * l, K₀.mul_mem hk' hl, ?_⟩
  calc s * k * (t * l) = s * (k * t) * l := by group
    _ = _ := by rw [e']; group

theorem Bnd.inv (hc : Cmd K₀) {D : Set H} (hD : Bnd K₀ D) : Bnd K₀ {g | g⁻¹ ∈ D} := by
  choose Sc hSc using hc
  obtain ⟨S, hS⟩ := hD
  refine ⟨S.biUnion fun s => Sc s⁻¹, ?_⟩
  intro g hg
  obtain ⟨s, hs, k, hk, e⟩ := hS _ hg
  obtain ⟨s', hs', k', hk', e'⟩ := hSc s⁻¹ k⁻¹ (K₀.inv_mem hk)
  refine ⟨s', Finset.mem_biUnion.2 ⟨s, hs, hs'⟩, k', hk', ?_⟩
  rw [← e', ← _root_.mul_inv_rev, ← e, inv_inv]

theorem Bnd.map (θ : H →* H) (hθ : ∀ k ∈ K₀, θ k ∈ K₀) {D : Set H} (hD : Bnd K₀ D) : Bnd K₀ (θ '' D) := by
  obtain ⟨S, hS⟩ := hD
  refine ⟨S.image θ, ?_⟩
  rintro _ ⟨d, hd, rfl⟩
  obtain ⟨s, hs, k, hk, rfl⟩ := hS d hd
  exact ⟨θ s, Finset.mem_image.2 ⟨s, hs, rfl⟩, θ k, hθ k hk, map_mul θ s k⟩

theorem Bnd.iterate (θ : H →* H) (hθ : ∀ k ∈ K₀, θ k ∈ K₀) (j : ℕ) {D : Set H} (hD : Bnd K₀ D) :
    Bnd K₀ ((⇑θ)^[j] '' D) := by
  induction j with
  | zero => simpa using hD
  | succ j ih =>
    rw [Function.iterate_succ', Set.image_comp]
    exact ih.map θ hθ

theorem nrmG_succ (θ : H →* H) (j : ℕ) (y : H) : nrmG θ (j + 1) y = nrmG θ j y * (⇑θ)^[j] y := by
  simp [nrmG, List.range_succ, List.map_append, List.prod_append]

theorem Bnd.nrm (hc : Cmd K₀) (θ : H →* H) (hθ : ∀ k ∈ K₀, θ k ∈ K₀) (j : ℕ) {D : Set H} (hD : Bnd K₀ D) :
    Bnd K₀ (nrmG θ j '' D) := by
  induction j with
  | zero =>
    refine (bnd_singleton 1).mono ?_
    rintro _ ⟨d, -, rfl⟩
    simp [nrmG]
  | succ j ih =>
    refine (ih.mul hc (hD.iterate θ hθ j)).mono ?_
    rintro _ ⟨d, hd, rfl⟩
    exact ⟨_, ⟨d, hd, rfl⟩, _, ⟨d, hd, rfl⟩, nrmG_succ θ j d⟩

theorem nrmG_twConj (θ : H →* H) (j : ℕ) (x δ : H) :
    nrmG θ j (x⁻¹ * δ * θ x) = x⁻¹ * nrmG θ j δ * (⇑θ)^[j] x := by
  induction j with
  | zero => simp [nrmG]
  | succ j ih =>
    rw [nrmG_succ, nrmG_succ, ih, iterate_map_mul, iterate_map_mul, iterate_map_inv,
      ← Function.iterate_succ_apply θ j x]
    group

theorem finite_of_bnd (T K : Subgroup H) (hK : K.relIndex K₀ ≠ 0) (D : Set H) (hD : Bnd K₀ D) (P : H → Prop)
    (hP : ∀ x, P x → ∃ t ∈ T, ∃ d ∈ D, x = t * d) :
    {q : DoubleCoset.Quotient (T : Set H) (K : Set H) | P (Quotient.out q)}.Finite := by
  obtain ⟨S, hS⟩ := hD
  haveI : (K.subgroupOf K₀).FiniteIndex := ⟨hK⟩
  haveI : Finite (K₀ ⧸ K.subgroupOf K₀) := Subgroup.finite_quotient_of_finiteIndex
  let R : Set H := Set.range fun c : K₀ ⧸ K.subgroupOf K₀ => ((Quotient.out c : K₀) : H)
  have hR : R.Finite := Set.finite_range _
  have hcov : ∀ k ∈ K₀, ∃ c ∈ R, ∃ l ∈ K, k = c * l := by
    intro k hk
    let c : K₀ ⧸ K.subgroupOf K₀ := QuotientGroup.mk ⟨k, hk⟩
    have h1 : ((Quotient.out c : K₀))⁻¹ * ⟨k, hk⟩ ∈ K.subgroupOf K₀ :=
      QuotientGroup.leftRel_apply.mp (Quotient.exact' (Quotient.out_eq' c))
    refine ⟨((Quotient.out c : K₀) : H), ⟨c, rfl⟩, ((Quotient.out c : K₀) : H)⁻¹ * k, h1, by group⟩
  refine ((S.finite_toSet.prod hR).image fun sc : H × H => DoubleCoset.mk T K (sc.1 * sc.2)).subset ?_
  intro q hq
  obtain ⟨t, ht, d, hd, hx⟩ := hP _ hq
  obtain ⟨s, hs, k, hk, rfl⟩ := hS d hd
  obtain ⟨c, hc, l, hl, rfl⟩ := hcov k hk
  refine ⟨(s, c), ⟨hs, hc⟩, ?_⟩
  rw [← DoubleCoset.out_eq' T K q, DoubleCoset.eq]
  exact ⟨t, ht, l, hl, by rw [hx]; group⟩

end Generic

theorem bnd_dbl {H : Type} [Group H] {K₀ : Subgroup H} (hc : Cmd K₀) (S : Finset H) :
    Bnd K₀ {g | ∃ s ∈ S, ∃ k₁ ∈ K₀, ∃ k₂ ∈ K₀, g = k₁ * s * k₂} := by
  choose Sc hSc using hc
  refine ⟨S.biUnion Sc, ?_⟩
  rintro g ⟨s, hs, k₁, hk₁, k₂, hk₂, rfl⟩
  obtain ⟨s', hs', k', hk', e⟩ := hSc s k₁ hk₁
  exact ⟨s', Finset.mem_biUnion.2 ⟨s, hs, hs'⟩, k' * k₂, K₀.mul_mem hk' hk₂, by rw [e, mul_assoc]⟩

section Specific

variable {p : ℕ} [Fact p.Prime]

theorem sigG_iterate_apply (G : HTGroup p) (r k : ℕ) (g : Gr G r) :
    (⇑(sigG G r))^[k] g = ((⇑(GlobalTheory.LKLoc.sig p (Q0 p) 1 r))^[k] g.1,
      fun i => (⇑(sigRes p (G.Fw i) G.n r))^[k] (g.2 i)) := by
  induction k generalizing g with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    rfl

theorem sigG_iterate_self (G : HTGroup p) {r : ℕ} (hr : 0 < r) (g : Gr G r) : (⇑(sigG G r))^[r] g = g := by
  rw [sigG_iterate_apply]
  refine Prod.ext ?_ (funext fun i => ?_)
  · exact GlobalTheory.LKLoc.sig_iterate_r p (Q0 p) inferInstance 1 r hr g.1
  · exact sigRes_iterate_eq_self p (G.Fw i) G.n r hr (g.2 i)

end Specific

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ) (γ : Gp G) (δ z : Gr G r) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → regular₂ G γ → IsNrm G r γ δ z → IsTest (sigG G r) (KHT p G.m G.n r G.Fw) K φ → {q : DoubleCoset.Quotient (GlobalTheory.BCT.twCent (sigG G r) δ : Set (Gr G r)) (K : Set (Gr G r)) | φ ((Quotient.out q)⁻¹ * δ * sigG G r (Quotient.out q)) ≠ 0}.Finite := by
  intro p _ G r γ δ z K φ hr hγ hN hT
  obtain ⟨hcomm, -, -, S, hS⟩ := hT
  have hc : Cmd (KHT p G.m G.n r G.Fw) := fun s => GlobalTheory.T.finite_left_coset_representatives p G r hr s
  have hσ0 : ∀ k ∈ KHT p G.m G.n r G.Fw, sigG G r k ∈ KHT p G.m G.n r G.Fw :=
    fun k hk => GlobalTheory.LKRes.Model.sigHT_KHT p G.m G.n r G.Fw k hk
  let C : Set (Gr G r) := {g | φ g ≠ 0}
  have hC : Bnd (KHT p G.m G.n r G.Fw) C := (bnd_dbl hc S).mono fun g hg => by
    obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, e⟩ := hS g hg
    exact ⟨s, hs, k₁, hk₁, k₂, hk₂, e⟩
  obtain ⟨E, hE⟩ := hC.nrm hc (sigG G r) hσ0 r
  obtain ⟨D₁, hD₁⟩ := GlobalTheory.T.centralizer_finite_decomposition p G r hr γ hγ E
  let A : Set (Gr G r) := {g | ∃ d ∈ D₁, ∃ k ∈ KHT p G.m G.n r G.Fw, g = z⁻¹ * d * k}
  have hA : Bnd (KHT p G.m G.n r G.Fw) A := by
    refine ⟨D₁.image (z⁻¹ * ·), ?_⟩
    rintro g ⟨d, hd, k, hk, rfl⟩
    exact ⟨z⁻¹ * d, Finset.mem_image.2 ⟨d, hd, rfl⟩, k, hk, rfl⟩
  obtain ⟨E₂, hE₂⟩ := (hA.mul hc hC).mul hc ((hA.map (sigG G r) hσ0).inv hc)
  obtain ⟨D₃, hD₃⟩ := GlobalTheory.T.twisted_centralizer_decomposition p G r hr γ hγ δ z hN E₂
  refine finite_of_bnd (K₀ := KHT p G.m G.n r G.Fw) (GlobalTheory.BCT.twCent (sigG G r) δ) K hcomm.1 _
    ((bnd_finset D₃).mul hc hA) (fun x => φ (x⁻¹ * δ * sigG G r x) ≠ 0) ?_
  intro x hx
  have hy : nrmG (sigG G r) r (x⁻¹ * δ * sigG G r x) ∈ nrmG (sigG G r) r '' C := ⟨_, hx, rfl⟩
  obtain ⟨e, he, k, hk, hek⟩ := hE _ hy
  have key : (z * x)⁻¹ * inclG G r γ * (z * x) = e * k := by
    rw [← hek, nrmG_twConj, sigG_iterate_self G hr, hN]; group
  obtain ⟨t, htc, d, hd, k₁, hk₁, hzx⟩ := hD₁ (z * x) ⟨e, he, k, hk, key⟩
  have ht'c : z⁻¹ * t * z * nrmG (sigG G r) r δ = nrmG (sigG G r) r δ * (z⁻¹ * t * z) := by
    rw [hN]
    calc z⁻¹ * t * z * (z⁻¹ * inclG G r γ * z) = z⁻¹ * (t * inclG G r γ) * z := by group
      _ = z⁻¹ * (inclG G r γ * t) * z := by rw [htc]
      _ = _ := by group
  have hxe : x = z⁻¹ * t * z * (z⁻¹ * d * k₁) := by
    calc x = z⁻¹ * (z * x) := by group
      _ = _ := by rw [hzx]; group
  have ht' : z⁻¹ * t * z = x * (z⁻¹ * d * k₁)⁻¹ := by rw [hxe]; group
  have hmem : (z⁻¹ * t * z)⁻¹ * δ * sigG G r (z⁻¹ * t * z) ∈
      {g | ∃ u ∈ {g | ∃ a ∈ A, ∃ c ∈ C, g = a * c}, ∃ v ∈ {g | g⁻¹ ∈ sigG G r '' A}, g = u * v} := by
    refine ⟨(z⁻¹ * d * k₁) * (x⁻¹ * δ * sigG G r x), ⟨_, ⟨d, hd, k₁, hk₁, rfl⟩, _, hx, rfl⟩,
      (sigG G r (z⁻¹ * d * k₁))⁻¹, ?_, ?_⟩
    · show ((sigG G r (z⁻¹ * d * k₁))⁻¹)⁻¹ ∈ sigG G r '' A
      rw [inv_inv]
      exact ⟨_, ⟨d, hd, k₁, hk₁, rfl⟩, rfl⟩
    · rw [ht', map_mul, map_inv]; group
  obtain ⟨e₂, he₂, k₂, hk₂, h₂⟩ := hE₂ _ hmem
  obtain ⟨u, hu, d₃, hd₃, k₃, hk₃, hu'⟩ := hD₃ _ ht'c ⟨e₂, he₂, k₂, hk₂, h₂⟩
  refine ⟨u, hu, d₃ * k₃ * (z⁻¹ * d * k₁), ⟨d₃ * k₃, ⟨d₃, hd₃, k₃, hk₃, rfl⟩, _, ⟨d, hd, k₁, hk₁, rfl⟩, rfl⟩, ?_⟩
  rw [hxe, hu']; group

end GlobalTheory.TwOrbFin
end
end
