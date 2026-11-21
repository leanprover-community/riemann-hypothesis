import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductEqFinprod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueAdmissibleLocalComponentDefiniteUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAutFormsWeightLevelFiniteSumFixedVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIntegralFixedVectorsEqOneAlmostAllStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTraceIndicatorLevelLocalUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorLevelIndicatorEqInvIndex
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeProductOfLocalTestFunctionsSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTraceIndicatorLevelLocalUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLevelFixedVectorsDefiniteUnitaryEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceWeightFormsEqDimMulRationalClasses
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOpenNhdOneOfIntegralEqOneOnFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalComponentLevelFixedVectorsNeBotStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOperatorTestFamilyPreservesLevelForms

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_admissible_localComponent_definiteUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ w : Pl E, (∃ σ : SmIrr (UL n w), IsCompU π w σ ∧ ∀ U : Subgroup (UL n w), IsOpen (U : Set (UL n w)) → FiniteDimensional ℂ (fixed σ.ρ U)) ∧ ∀ σ σ' : SmIrr (UL n w), IsCompU π w σ → IsCompU π w σ' → Nonempty (σ.ρ.Equiv σ'.ρ) := by
  first | exact @GlobalTheory.BCT.LocCompU.exists_unique_locComp | exact GlobalTheory.BCT.LocCompU.exists_unique_locComp | (intros; apply GlobalTheory.BCT.LocCompU.exists_unique_locComp <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryHeckeOperator_levelIndicator_eq_inv_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ S : Set (Pl E), IsSection S → ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ φ ∈ fixed (RF E n) (globLev S K'), hop S K' (fun w => (K' w : Set (UL n w)).indicator 1) φ = (∏ᶠ w ∈ S, (((K' w).relIndex (KL n w) : ℕ) : ℂ))⁻¹ • φ := by
  first | exact @GlobalTheory.BCT.hop_indicator_level | exact GlobalTheory.BCT.hop_indicator_level | (intros; apply GlobalTheory.BCT.hop_indicator_level <;> assumption)
end

section
namespace GlobalTheory.TraceOnInjectiveMap

theorem trOn_map_of_injective {X V : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
    (j : X →ₗ[ℂ] V) (hj : Function.Injective j) (M : Submodule ℂ X) (L' : X →ₗ[ℂ] X) (L : V →ₗ[ℂ] V)
    (hL : ∀ x ∈ M, L (j x) = j (L' x)) :
    GlobalTheory.BCT.trOn (Submodule.map j M) L = GlobalTheory.BCT.trOn M L' := by
  have hpres : (∀ v ∈ Submodule.map j M, L v ∈ Submodule.map j M) ↔ ∀ x ∈ M, L' x ∈ M := by
    constructor
    · intro h x hx
      obtain ⟨y, hy, hyx⟩ := h (j x) ⟨x, hx, rfl⟩
      rw [hL x hx] at hyx
      exact hj hyx ▸ hy
    · rintro h _ ⟨x, hx, rfl⟩
      exact ⟨L' x, h x hx, (hL x hx).symm⟩
  unfold GlobalTheory.BCT.trOn
  by_cases h' : ∀ x ∈ M, L' x ∈ M
  · rw [dif_pos (hpres.2 h'), dif_pos h']
    let e : M ≃ₗ[ℂ] Submodule.map j M := Submodule.equivMapOfInjective j hj M
    have hc : L.restrict (hpres.2 h') = e.conj (L'.restrict h') := by
      apply LinearMap.ext
      intro w
      obtain ⟨x, rfl⟩ := e.surjective w
      apply Subtype.ext
      simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply, LinearMap.coe_restrict_apply, e,
        Submodule.coe_equivMapOfInjective_apply]
      exact hL x x.2
    rw [hc, LinearMap.trace_conj']
  · rw [dif_neg (mt hpres.1 h'), dif_neg h']

end GlobalTheory.TraceOnInjectiveMap
end

section
noncomputable section

open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.BCT.Peel

section Linear

variable {X V : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]

theorem trOn_map (j : X →ₗ[ℂ] V) (hj : Function.Injective j) (M : Submodule ℂ X) (L' : X →ₗ[ℂ] X) (L : V →ₗ[ℂ] V)
    (h : ∀ x ∈ M, L (j x) = j (L' x)) : trOn (M.map j) L = trOn M L' :=
  _root_.GlobalTheory.TraceOnInjectiveMap.trOn_map_of_injective j hj M L' L h

theorem trOn_of_not_finite (M : Submodule ℂ V) (L : V →ₗ[ℂ] V) (h : ¬ Module.Finite ℂ M) : trOn M L = 0 := by
  unfold trOn
  split_ifs with hL
  · rw [LinearMap.trace, dif_neg]
    · rfl
    · rintro ⟨s, ⟨b⟩⟩
      exact h (Module.Finite.of_basis b)
  · rfl

theorem trOn_bot (L : V →ₗ[ℂ] V) : trOn ⊥ L = 0 := by
  unfold trOn
  split_ifs with hL
  · rw [Subsingleton.elim (L.restrict hL) 0, map_zero]
  · rfl

end Linear

section Iso

variable {H X V W : Type} [Group H] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]

theorem map_fixed {σ : Representation ℂ H W} {τ : Representation ℂ H X} (f : σ.IntertwiningMap τ) (K : Subgroup H)
    {v : W} (hv : v ∈ fixed σ K) : f.toLinearMap v ∈ fixed τ K := by
  rw [GlobalTheory.TwTrLin.mem_fixed_iff] at hv ⊢
  intro k hk
  have := LinearMap.congr_fun (f.isIntertwining' k) v
  simp only [LinearMap.comp_apply] at this
  rw [← this, hv k hk]

theorem schur (σ : Representation ℂ H W) [σ.IsIrreducible] (K : Subgroup H) [Module.Finite ℂ (fixed σ K)]
    (h0 : fixed σ K ≠ ⊥) (φ : σ.IntertwiningMap σ) : ∃ c : ℂ, ∀ w, φ.toLinearMap w = c • w := by
  haveI : Nontrivial (fixed σ K) := Submodule.nontrivial_iff_ne_bot.2 h0
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue
    (φ.toLinearMap.restrict (p := fixed σ K) (q := fixed σ K) fun v hv => map_fixed φ K hv)
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hv1 : φ.toLinearMap v.1 = c • v.1 := congrArg Subtype.val hv.apply_eq_smul
  refine ⟨c, ?_⟩
  rcases ((isIrreducible_iff σ).1 inferInstance).2 (LinearMap.ker (φ.toLinearMap - c • LinearMap.id))
    (fun g u hu => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hu ⊢
      have := LinearMap.congr_fun (φ.isIntertwining' g) u
      simp only [LinearMap.comp_apply] at this
      rw [this, hu]
      simp) with h | h
  · exfalso
    have : v.1 ∈ LinearMap.ker (φ.toLinearMap - c • LinearMap.id) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
      exact hv1
    rw [h] at this
    exact hv.2 (Subtype.ext this)
  · intro w
    have : w ∈ LinearMap.ker (φ.toLinearMap - c • LinearMap.id) := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    exact this

theorem exists_decomp (σ : Representation ℂ H W) [σ.IsIrreducible] (τ : Representation ℂ H X) (ρ : Representation ℂ H V)
    (j : τ.IntertwiningMap ρ) (hj : Function.Injective j.toLinearMap)
    (h : ∀ x, j.toLinearMap x ∈ LocUniq.isoPart σ ρ) :
    ∃ (ι : Type) (s : ι → σ.IntertwiningMap τ) (p : ι → τ.IntertwiningMap σ),
      (∀ i i' w, (p i).toLinearMap ((s i').toLinearMap w) = if i' = i then w else 0) ∧
      ∀ x, (∀ i, (p i).toLinearMap x = 0) → x = 0 := by
  let R := MonoidAlgebra ℂ H
  let J : τ.asModule →ₗ[R] ρ.asModule := Representation.IntertwiningMap.equivLinearMapAsModule τ ρ j
  have hle : LocUniq.isoPart σ ρ ≤ ((isotypicComponent R ρ.asModule σ.asModule).restrictScalars ℂ).comap
      ρ.asModuleEquiv.symm.toLinearMap := by
    refine iSup_le fun f => ?_
    rintro _ ⟨v, rfl⟩
    let F : σ.asModule →ₗ[R] ρ.asModule := Representation.IntertwiningMap.equivLinearMapAsModule σ ρ f
    have h1 : LinearMap.range F ≤ isotypicComponent R ρ.asModule σ.asModule := by
      rcases LinearMap.injective_or_eq_zero F with hf | hf
      · exact le_sSup ⟨(LinearEquiv.ofInjective F hf).symm⟩
      · simp [hf]
    exact h1 ⟨σ.asModuleEquiv.symm v, rfl⟩
  let J' : τ.asModule →ₗ[R] isotypicComponent R ρ.asModule σ.asModule :=
    J.codRestrict _ fun x => hle (h (τ.asModuleEquiv x))
  have hJ' : Function.Injective J' := fun a b e => hj (congrArg Subtype.val e)
  haveI : IsSemisimpleModule R τ.asModule := IsSemisimpleModule.of_injective J' hJ'
  obtain ⟨ι, ⟨e⟩⟩ := ((IsIsotypicOfType.isotypicComponent R ρ.asModule σ.asModule).of_injective J' hJ').linearEquiv_finsupp
  refine ⟨ι, fun i => (Representation.IntertwiningMap.equivLinearMapAsModule σ τ).symm
      (e.symm.toLinearMap ∘ₗ Finsupp.lsingle i),
    fun i => (Representation.IntertwiningMap.equivLinearMapAsModule τ σ).symm (Finsupp.lapply i ∘ₗ e.toLinearMap),
    fun i i' w => ?_, fun x hx => ?_⟩
  · change e (e.symm (Finsupp.single i' (σ.asModuleEquiv.symm w))) i = _
    rw [e.apply_symm_apply, Finsupp.single_apply]
    rfl
  · have : e (τ.asModuleEquiv.symm x) = 0 := Finsupp.ext fun i => hx i
    exact e.injective (this.trans (map_zero e).symm)

end Iso

section Trace

variable {H X W : Type} [Group H] [AddCommGroup X] [Module ℂ X] [AddCommGroup W] [Module ℂ W]

theorem exists_factor (σ : Representation ℂ H W) [σ.IsIrreducible] (τ : Representation ℂ H X) {ι : Type} [Fintype ι]
    (s : ι → σ.IntertwiningMap τ) (p : ι → τ.IntertwiningMap σ)
    (hps : ∀ i i' w, (p i).toLinearMap ((s i').toLinearMap w) = if i' = i then w else 0)
    (hp : ∀ x, (∀ i, (p i).toLinearMap x = 0) → x = 0) (K : Subgroup H) [Module.Finite ℂ (fixed σ K)]
    [Module.Finite ℂ (fixed τ K)] (h0 : fixed σ K ≠ ⊥) (B : τ.IntertwiningMap τ) :
    ∃ t : ℂ, ∀ (A : X →ₗ[ℂ] X) (a : W →ₗ[ℂ] W), (∀ v ∈ fixed σ K, a v ∈ fixed σ K) →
      (∀ i w, A ((s i).toLinearMap w) = (s i).toLinearMap (a w)) →
      trOn (fixed τ K) (A ∘ₗ B.toLinearMap) = t * trOn (fixed σ K) a := by
  have hsum : ∀ x, x = ∑ i, (s i).toLinearMap ((p i).toLinearMap x) := fun x => by
    rw [← sub_eq_zero]
    refine hp _ fun i => ?_
    simp only [map_sub, map_sum, hps]
    simp
  choose b hb using fun i j => schur σ K h0 ((p j).comp (B.comp (s i)))
  have hb' : ∀ i j w, (p j).toLinearMap (B.toLinearMap ((s i).toLinearMap w)) = b i j • w := hb
  refine ⟨∑ i, b i i, fun A a ha hA => ?_⟩
  have hform : ∀ y, A (B.toLinearMap y) = ∑ i, ∑ j, b i j • (s j).toLinearMap (a ((p i).toLinearMap y)) := fun y => by
    conv_lhs => rw [hsum y]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsum (B.toLinearMap _), map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hb', map_smul, map_smul, hA]
  have hY : ∀ y ∈ fixed τ K, (A ∘ₗ B.toLinearMap) y ∈ fixed τ K := fun y hy => by
    rw [LinearMap.comp_apply, hform]
    exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (map_fixed _ K (ha _ (map_fixed _ K hy)))
  let sU : ι → (fixed σ K →ₗ[ℂ] fixed τ K) := fun i => (s i).toLinearMap.restrict fun v hv => map_fixed _ K hv
  let pU : ι → (fixed τ K →ₗ[ℂ] fixed σ K) := fun i => (p i).toLinearMap.restrict fun v hv => map_fixed _ K hv
  unfold trOn
  rw [dif_pos hY, dif_pos ha]
  have h1 : (A ∘ₗ B.toLinearMap).restrict hY = ∑ i, ∑ j, b i j • (sU j ∘ₗ (a.restrict ha ∘ₗ pU i)) := by
    refine LinearMap.ext fun y => Subtype.ext ?_
    change A (B.toLinearMap y.1) = _
    rw [hform]
    simp only [LinearMap.sum_apply, Submodule.coe_sum]
    rfl
  have h2 : ∀ i j, (a.restrict ha ∘ₗ pU i) ∘ₗ sU j = if j = i then a.restrict ha else 0 := fun i j => by
    refine LinearMap.ext fun v => Subtype.ext ?_
    change a ((p i).toLinearMap ((s j).toLinearMap v.1)) = _
    rw [hps]
    split_ifs
    · rfl
    · exact map_zero a
  rw [h1, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, Finset.sum_eq_single i]
  · rw [map_smul, LinearMap.trace_comp_comm', h2, if_pos rfl, smul_eq_mul]
  · intro j _ hj
    rw [map_smul, LinearMap.trace_comp_comm', h2, if_neg hj, map_zero, smul_zero]
  · simp

theorem trOn_cross {V : Type} [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ H W) [σ.IsIrreducible]
    (τ : Representation ℂ H X) (ρ : Representation ℂ H V) (j : τ.IntertwiningMap ρ)
    (hj : Function.Injective j.toLinearMap) (h : ∀ x, j.toLinearMap x ∈ LocUniq.isoPart σ ρ) (K : Subgroup H)
    (B : τ.IntertwiningMap τ) (A A' : X →ₗ[ℂ] X) (a a' : W →ₗ[ℂ] W) (ha : ∀ v ∈ fixed σ K, a v ∈ fixed σ K)
    (ha' : ∀ v ∈ fixed σ K, a' v ∈ fixed σ K)
    (hA : ∀ (s : σ.IntertwiningMap τ) w, A (s.toLinearMap w) = s.toLinearMap (a w))
    (hA' : ∀ (s : σ.IntertwiningMap τ) w, A' (s.toLinearMap w) = s.toLinearMap (a' w)) :
    trOn (fixed τ K) (A ∘ₗ B.toLinearMap) * trOn (fixed σ K) a' =
      trOn (fixed σ K) a * trOn (fixed τ K) (A' ∘ₗ B.toLinearMap) := by
  by_cases hU : Module.Finite ℂ (fixed σ K)
  swap
  · rw [trOn_of_not_finite _ a hU, trOn_of_not_finite _ a' hU, mul_zero, zero_mul]
  by_cases h0 : fixed σ K = ⊥
  · rw [h0, trOn_bot, trOn_bot, mul_zero, zero_mul]
  by_cases hY : Module.Finite ℂ (fixed τ K)
  swap
  · rw [trOn_of_not_finite _ _ hY, trOn_of_not_finite _ _ hY, mul_zero, zero_mul]
  obtain ⟨ι, s, p, hps, hp⟩ := exists_decomp σ τ ρ j hj h
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have hli : LinearIndependent ℂ fun i => (⟨(s i).toLinearMap u, map_fixed _ K hu⟩ : fixed τ K) := by
    refine LinearIndependent.of_comp (fixed τ K).subtype (linearIndependent_iff'.2 fun T g hg i hi => ?_)
    have := congrArg (p i).toLinearMap hg
    simp only [Function.comp_apply, Submodule.subtype_apply, map_sum, map_smul, hps, map_zero] at this
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg hj, smul_zero]) (fun h => absurd hi h), if_pos rfl] at this
    exact (smul_eq_zero.1 this).resolve_right hu0
  haveI : Finite ι := hli.finite
  haveI := Fintype.ofFinite ι
  obtain ⟨t, ht⟩ := exists_factor σ τ s p hps hp K h0 B
  rw [ht A a ha fun i => hA (s i), ht A' a' ha' fun i => hA' (s i)]
  ring

end Trace

section Split

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem levOp_nat {X : Type} [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ H W) (τ : Representation ℂ H X)
    (s : W →ₗ[ℂ] X) (hs : ∀ h w, s (σ h w) = τ h (s w)) (K₀ K : Subgroup H) (a : H → ℂ)
    (ha : {q : H ⧸ K | a q.out ≠ 0}.Finite) (w : W) :
    levOp τ K₀ K a LinearMap.id (s w) = s (levOp σ K₀ K a LinearMap.id w) := by
  rw [LevOpTmul.levOp_apply τ K₀ K a _ ha.toFinset (fun q hq => by simpa using hq),
    LevOpTmul.levOp_apply σ K₀ K a _ ha.toFinset (fun q hq => by simpa using hq)]
  simp only [map_smul, map_sum, hs, LinearMap.id_apply]

variable (ι : H →* G) (r : G →* H) (hr : ∀ h, r (ι h) = h) (hc : ∀ x ∈ r.ker, ∀ h, Commute x (ι h))
  {U : Subgroup G} {K : Subgroup H} (hK1 : ∀ k ∈ K, ι k ∈ U) (hK2 : ∀ k ∈ U, r k ∈ K)

include hr in

theorem exists_split (g : G) : ∃ x : r.ker, g = ι (r g) * x :=
  ⟨⟨(ι (r g))⁻¹ * g, by rw [MonoidHom.mem_ker, map_mul, map_inv, hr, inv_mul_cancel]⟩, by simp⟩

include hr hc hK1 hK2 in

theorem mk_eq_iff (h h' : H) (x x' : r.ker) :
    ((ι h * x : G) : G ⧸ U) = (ι h' * x' : G) ↔
      (h : H ⧸ K) = h' ∧ (x : r.ker ⧸ U.subgroupOf r.ker) = x' := by
  simp only [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have e : (ι h * x : G)⁻¹ * (ι h' * x') = ι (h⁻¹ * h') * ((x⁻¹ * x' : r.ker) : G) := by
    have := (hc _ (x⁻¹).2 (h⁻¹ * h')).eq
    simp only [Subgroup.coe_inv, Subgroup.coe_mul, map_mul, map_inv] at this ⊢
    rw [mul_inv_rev, ← mul_assoc _ (x : G)⁻¹, ← this]
    group
  rw [e]
  constructor
  · intro hm
    have h1 : h⁻¹ * h' ∈ K := by
      have := hK2 _ hm
      rwa [map_mul, hr, (x⁻¹ * x').2, mul_one] at this
    exact ⟨h1, (U.mul_mem_cancel_left (hK1 _ h1)).1 hm⟩
  · rintro ⟨h1, h2⟩
    exact U.mul_mem (hK1 _ h1) h2

include hr hc hK1 hK2 in

theorem levOp_split (ρ : Representation ℂ G V) (U₀ : Subgroup G) (K₀ : Subgroup H) (h0 : K.relIndex K₀ ≠ 0)
    (F : G → ℂ) (a : H → ℂ) (b : r.ker → ℂ) (hF : ∀ h (x : r.ker), F (ι h * x) = a h * b x)
    (hFr : ∀ k ∈ U, ∀ x, F (x * k) = F x) (har : ∀ k ∈ K, ∀ x, a (x * k) = a x)
    (hbr : ∀ k ∈ U.subgroupOf r.ker, ∀ x, b (x * k) = b x)
    (ha : {q : H ⧸ K | a q.out ≠ 0}.Finite) (hb : {q : r.ker ⧸ U.subgroupOf r.ker | b q.out ≠ 0}.Finite)
    (v : V) (hv : v ∈ fixed ρ U) :
    levOp ρ U₀ U F LinearMap.id v = levOp (ρ.comp ι) K₀ K a LinearMap.id
      ((((U.relIndex U₀ : ℕ) : ℂ)⁻¹ * (K.relIndex K₀ : ℕ)) •
        levOp (ρ.comp r.ker.subtype) (U.subgroupOf r.ker) (U.subgroupOf r.ker) b LinearMap.id v) := by
  have hv' := (GlobalTheory.TwTrLin.mem_fixed_iff ρ U v).1 hv
  have t3 := LevOpTmul.term_mk ρ U F hFr v hv'
  have t1 : ∀ g : H, a (g : H ⧸ K).out = a g := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    rw [hk, har _ k.2]
  have t2 : ∀ g : r.ker, b (g : r.ker ⧸ U.subgroupOf r.ker).out = b g := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf r.ker) g
    rw [hk, hbr _ k.2]
  let e : (H ⧸ K) × (r.ker ⧸ U.subgroupOf r.ker) → G ⧸ U := fun p => ((ι p.1.out * (p.2.out : r.ker) : G) : G ⧸ U)
  have he : Function.Injective e := by
    intro p q h
    have := (mk_eq_iff ι r hr hc hK1 hK2 _ _ _ _).1 h
    simp only [QuotientGroup.out_eq'] at this
    exact Prod.ext this.1 this.2
  have h0' : ((K.relIndex K₀ : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 h0
  rw [LevOpTmul.levOp_apply _ K₀ K a _ ha.toFinset (fun q hq => by simpa using hq),
    LevOpTmul.levOp_apply _ _ _ b _ hb.toFinset (fun q hq => by simpa using hq),
    LevOpTmul.levOp_apply ρ _ _ _ _ ((ha.toFinset ×ˢ hb.toFinset).image e) ?_,
    Finset.sum_image (fun p _ q _ h => he h), Finset.sum_product]
  · simp only [LinearMap.id_apply, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_smul, map_smul, map_sum,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    simp only [e]
    rw [(t3 _).1, (t3 _).2, hF, map_mul]
    simp only [smul_smul]
    congr 1
    field_simp
  · intro q hq
    obtain ⟨x, hx⟩ := exists_split ι r hr q.out
    refine Finset.mem_image.2 ⟨((r q.out : H ⧸ K), (x : r.ker ⧸ U.subgroupOf r.ker)), ?_, ?_⟩
    · simp only [Finset.mem_product, Set.Finite.mem_toFinset, Set.mem_setOf_eq, t1, t2]
      rw [hx, hF] at hq
      exact mul_ne_zero_iff.1 hq
    · conv_rhs => rw [← QuotientGroup.out_eq' q, hx]
      exact (mk_eq_iff ι r hr hc hK1 hK2 _ _ _ _).2 ⟨QuotientGroup.out_eq' _, QuotientGroup.out_eq' _⟩

include hr hc hK1 hK2 in

theorem trOn_levOp_cross (ρ : Representation ℂ G V) (X : Submodule ℂ V) (hX : ∀ g, ∀ v ∈ X, ρ g v ∈ X)
    (σ : Representation ℂ H W) [σ.IsIrreducible] (hiso : X ≤ LocUniq.isoPart σ (ρ.comp ι))
    (U₀ : Subgroup G) (K₀ : Subgroup H) (h0 : K.relIndex K₀ ≠ 0)
    (F F' : G → ℂ) (a a' : H → ℂ) (b : r.ker → ℂ) (hF : ∀ h (x : r.ker), F (ι h * x) = a h * b x)
    (hF' : ∀ h (x : r.ker), F' (ι h * x) = a' h * b x)
    (hFr : ∀ k ∈ U, ∀ x, F (x * k) = F x) (hFr' : ∀ k ∈ U, ∀ x, F' (x * k) = F' x)
    (hai : ∀ k ∈ K, ∀ x, a (k * x) = a x ∧ a (x * k) = a x) (hai' : ∀ k ∈ K, ∀ x, a' (k * x) = a' x ∧ a' (x * k) = a' x)
    (hbi : ∀ k ∈ U.subgroupOf r.ker, ∀ x, b (k * x) = b x ∧ b (x * k) = b x)
    (ha : {q : H ⧸ K | a q.out ≠ 0}.Finite) (ha' : {q : H ⧸ K | a' q.out ≠ 0}.Finite)
    (hb : {q : r.ker ⧸ U.subgroupOf r.ker | b q.out ≠ 0}.Finite) :
    trOn (X ⊓ fixed ρ U) (levOp ρ U₀ U F LinearMap.id) * twTr σ K₀ K a' LinearMap.id =
      twTr σ K₀ K a LinearMap.id * trOn (X ⊓ fixed ρ U) (levOp ρ U₀ U F' LinearMap.id) := by
  let L := U.subgroupOf r.ker
  let ρR : Representation ℂ r.ker V := ρ.comp r.ker.subtype
  let ρH : Representation ℂ H V := ρ.comp ι
  have hcomm : ∀ (h : H) (x : r.ker) v, ρH h (ρR x v) = ρR x (ρH h v) := fun h x v => by
    change (ρ (ι h) * ρ x) v = (ρ x * ρ (ι h)) v
    rw [← map_mul, ← map_mul, (hc _ x.2 h).eq]
  let X' : Submodule ℂ V := X ⊓ fixed ρR L
  have hX' : ∀ h, X' ≤ X'.comap (ρH h) := fun h v hv => by
    refine ⟨hX _ _ hv.1, (GlobalTheory.TwTrLin.mem_fixed_iff _ _ _).2 fun k hk => ?_⟩
    rw [← hcomm, (GlobalTheory.TwTrLin.mem_fixed_iff _ _ _).1 hv.2 k hk]
  let τ : Representation ℂ H X' := ρH.subrepresentation X' hX'
  let j : τ.IntertwiningMap ρH := ⟨X'.subtype, fun _ => rfl⟩
  let c : ℂ := ((U.relIndex U₀ : ℕ) : ℂ)⁻¹ * (K.relIndex K₀ : ℕ)
  let B₀ : V →ₗ[ℂ] V := c • levOp ρR L L b LinearMap.id
  have hB₀ : ∀ v ∈ X', B₀ v ∈ X' := fun v hv => by
    refine X'.smul_mem c ⟨?_, GlobalTheory.TwTrLin.levOp_mapsTo ρR L L _ b hb (fun k hk x => (hbi k hk x).1)
      (fun k hk x => (hbi k hk x).2) (fun _ h => h) v hv.2⟩
    rw [LevOpTmul.levOp_apply _ _ _ b _ hb.toFinset (fun q hq => by simpa using hq)]
    exact X.smul_mem _ (X.sum_mem fun q _ => X.smul_mem _ (hX _ _ hv.1))
  let B : τ.IntertwiningMap τ := ⟨B₀.restrict hB₀, fun h => LinearMap.ext fun v => Subtype.ext (by
    change c • levOp ρR L L b LinearMap.id (ρH h v.1) = ρH h (c • levOp ρR L L b LinearMap.id v.1)
    rw [map_smul, levOp_nat ρR ρR (ρH h) (hcomm h) L L b hb])⟩
  have hY : X ⊓ fixed ρ U = (fixed τ K).map X'.subtype := by
    ext v
    constructor
    · rintro ⟨h1, h2⟩
      have h3 := (GlobalTheory.TwTrLin.mem_fixed_iff _ _ _).1 h2
      exact ⟨⟨v, h1, (GlobalTheory.TwTrLin.mem_fixed_iff _ _ _).2 fun k hk => h3 _ hk⟩,
        (GlobalTheory.TwTrLin.mem_fixed_iff _ _ _).2 fun k hk => Subtype.ext (h3 _ (hK1 k hk)), rfl⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨v.2.1, (GlobalTheory.TwTrLin.mem_fixed_iff _ _ _).2 fun k hk => ?_⟩
      obtain ⟨x, hx⟩ := exists_split ι r hr k
      have hxU : x ∈ L := by
        have : ι (r k) * x ∈ U := hx ▸ hk
        exact (U.mul_mem_cancel_left (hK1 _ (hK2 k hk))).1 this
      have h1 : ρ x v.1 = v.1 := (GlobalTheory.TwTrLin.mem_fixed_iff _ _ _).1 v.2.2 x hxU
      have h2 : ρ (ι (r k)) v.1 = v.1 :=
        congrArg Subtype.val ((GlobalTheory.TwTrLin.mem_fixed_iff _ _ _).1 hv _ (hK2 k hk))
      change ρ k v.1 = v.1
      rw [hx, map_mul, Module.End.mul_apply, h1, h2]
  have key : ∀ (F : G → ℂ) (a : H → ℂ), (∀ h (x : r.ker), F (ι h * x) = a h * b x) → (∀ k ∈ U, ∀ x, F (x * k) = F x) →
      (∀ k ∈ K, ∀ x, a (x * k) = a x) → {q : H ⧸ K | a q.out ≠ 0}.Finite →
      trOn (X ⊓ fixed ρ U) (levOp ρ U₀ U F LinearMap.id) =
        trOn (fixed τ K) (levOp τ K₀ K a LinearMap.id ∘ₗ B.toLinearMap) := fun F a hF hFr har ha => by
    rw [hY]
    refine trOn_map _ X'.injective_subtype _ _ _ fun v hv => ?_
    have hv' : X'.subtype v ∈ X ⊓ fixed ρ U := hY ▸ ⟨v, hv, rfl⟩
    rw [levOp_split ι r hr hc hK1 hK2 ρ U₀ K₀ h0 F a b hF hFr har (fun k hk x => (hbi k hk x).2) ha hb _ hv'.2,
      LinearMap.comp_apply, ← levOp_nat τ ρH X'.subtype (fun _ _ => rfl) K₀ K a ha]
    rfl
  rw [key F a hF hFr (fun k hk x => (hai k hk x).2) ha, key F' a' hF' hFr' (fun k hk x => (hai' k hk x).2) ha']
  exact trOn_cross σ τ ρH j X'.injective_subtype (fun x => hiso x.2.1) K B _ _ _ _
    (GlobalTheory.TwTrLin.levOp_mapsTo σ K₀ K _ a ha (fun k hk x => (hai k hk x).1) (fun k hk x => (hai k hk x).2) fun _ h => h)
    (GlobalTheory.TwTrLin.levOp_mapsTo σ K₀ K _ a' ha' (fun k hk x => (hai' k hk x).1) (fun k hk x => (hai' k hk x).2)
      fun _ h => h)
    (fun s w => levOp_nat σ τ s.toLinearMap (fun h w => LinearMap.congr_fun (s.isIntertwining' h) w) K₀ K a ha w)
    (fun s w => levOp_nat σ τ s.toLinearMap (fun h w => LinearMap.congr_fun (s.isIntertwining' h) w) K₀ K a' ha' w)

end Split

end GlobalTheory.BCT.Peel
end
end

section
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.Peel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem globFn_eq (hU : Unr E) {S : Set (Pl E)} {f : ∀ w : Pl E, UL n w → ℂ}
    (hf : ∀ᶠ w in cofinite, f w = (KL n w : Set (UL n w)).indicator 1) {w : Pl E} (hw : w ∈ S) (x : finU E n) :
    globFn S f x = f w (toSub _ (cLoc w x.1)) * ∏ᶠ u ∈ S \ {w}, f u (toSub _ (cLoc u x.1)) := by
  have hfin : (Function.mulSupport fun w : Pl E => f w (toSub (UL n w) (cLoc w (x : UA E n)))).Finite := by
    have h := (GlobalTheory.BCT.LocAE.eventually_mem_KL E hU n x).and hf
    rw [Filter.eventually_cofinite] at h
    refine h.subset ?_
    rintro u hu ⟨h1, h2⟩
    apply hu
    show f u _ = 1
    rw [h2, Set.indicator_of_mem (show _ ∈ (KL n u : Set (UL n u)) from h1)]
    rfl
  unfold globFn
  conv_lhs => rw [← Set.insert_diff_self_of_mem hw]
  exact finprod_mem_insert' _ (fun h => h.2 rfl) (hfin.subset Set.inter_subset_right)

theorem trOn_hop_peel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Set (Pl E), IsSection S → ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ w ∈ S, ∀ σ : SmIrr (UL n w), IsCompU π w σ → trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' f) * twTr σ.ρ (KL n w) (K' w) ((K' w : Set (UL n w)).indicator 1) LinearMap.id = twTr σ.ρ (KL n w) (K' w) (f w) LinearMap.id * trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' (Function.update f w ((K' w : Set (UL n w)).indicator 1))) := by
  intro E _ _ _ hU n hn π hπ S hS K' hK' f hf w hw σ hσ
  obtain ⟨e, he⟩ := LocCompU.exists_equiv hU n w
  let ι : UL n w →* finU E n := (Subgroup.inclusion (inf_le_left : locU n w ≤ finU E n)).comp
    e.toMulEquiv.symm.toMonoidHom
  let r : finU E n →* UL n w := ((cLoc w).comp (finU E n).subtype).codRestrict _ fun x => GlobLev.cLoc_mem_UL w x.1
  have hιw : ∀ h, cLoc w (ι h).1 = h.1 := fun h => by
    change cLoc w ((e.symm h : locU n w) : UA E n) = _
    rw [← he, e.apply_symm_apply]
  have hιu : ∀ h, ∀ u ∈ S, u ≠ w → cLoc u (ι h).1 = 1 := fun h u hu huw => by
    obtain ⟨v, -, hv⟩ := hS w
    exact GlobalTheory.DefU.LocRet.mem_locU_ne (e.symm h).2 fun h' => huw ((hv u ⟨hu, h'⟩).trans (hv w ⟨hw, rfl⟩).symm)
  have hr : ∀ h, r (ι h) = h := fun h => Subtype.ext (hιw h)
  have hc : ∀ x ∈ r.ker, ∀ h, Commute x (ι h) := fun x hx h => by
    have h1 : cLoc w x.1 = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have h2 : GlobalTheory.DefU.LocRet.ret w n x.1 = 1 := by
      apply e.injective
      rw [map_one]
      refine Subtype.ext ((he _).trans ?_)
      exact (GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_eq rfl x.1).trans h1
    have h3 := GlobalTheory.DefU.LocRet.commute_ret x.1 (e.symm h)
    rw [h2, OneMemClass.coe_one, inv_one, one_mul] at h3
    exact Subtype.ext h3.eq
  have hK1 : ∀ k ∈ K' w, ι k ∈ globLev S K' := fun k hk => (GlobLev.mem_globLev S K' _).2 fun u hu => by
    by_cases huw : u = w
    · subst huw
      have : (⟨cLoc u (ι k).1, GlobLev.cLoc_mem_UL u _⟩ : UL n u) = k := Subtype.ext (hιw k)
      rwa [this]
    · have : (⟨cLoc u (ι k).1, GlobLev.cLoc_mem_UL u _⟩ : UL n u) = 1 := Subtype.ext (hιu k u hu huw)
      rw [this]
      exact one_mem _
  have hK2 : ∀ k ∈ globLev S K', r k ∈ K' w := fun k hk => (GlobLev.mem_globLev S K' _).1 hk w hw
  obtain ⟨hind, h0, -⟩ := GlobalTheory.TwTrUnit.twTr_unit E n w (K' w) (hK'.1 w) σ
  set a' : UL n w → ℂ := (K' w : Set (UL n w)).indicator 1 with ha'
  have hf' : IsTest (KL n) K' (Function.update f w a') := by
    refine ⟨fun u => ?_, ?_⟩
    · by_cases huw : u = w
      · subst huw
        rwa [Function.update_self]
      · rw [Function.update_of_ne huw]
        exact hf.1 u
    · filter_upwards [hf.2, (Set.finite_singleton w).compl_mem_cofinite] with u h1 h2
      rwa [Function.update_of_ne h2]
  let b : r.ker → ℂ := fun x => ∏ᶠ u ∈ S \ {w}, f u (toSub _ (cLoc u x.1.1))
  have hsplit : ∀ g : ∀ u : Pl E, UL n u → ℂ, IsTest (KL n) K' g → (∀ u, u ≠ w → g u = f u) →
      ∀ h (x : r.ker), globFn S g (ι h * x) = g w h * b x := fun g hg hgf h x => by
    rw [globFn_eq hU hg.2 hw]
    have h1 : cLoc w x.1.1 = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 x.2)
    congr 1
    · rw [Subgroup.coe_mul, map_mul, hιw, h1, mul_one, toSub, dif_pos h.2]
    · refine finprod_mem_congr rfl fun u hu => ?_
      rw [hgf u hu.2, Subgroup.coe_mul, map_mul, hιu h u hu.1 hu.2, one_mul]
  have hF := hsplit f hf fun _ _ => rfl
  have hF' := hsplit _ hf' fun u hu => Function.update_of_ne hu _ _
  simp only [Function.update_self] at hF'
  have hH := GlobHecke.isHecke_globFn E hU n hn S hS K' hK' f hf
  have hH' := GlobHecke.isHecke_globFn E hU n hn S hS K' hK' _ hf'
  have hb : ∀ x : r.ker, b x = globFn S (Function.update f w a') x := fun x => by
    have := hF' 1 x
    rw [map_one, one_mul, ha', Set.indicator_of_mem (K' w).one_mem, Pi.one_apply, one_mul] at this
    exact this.symm
  have hopen := (GlobLev.globLev_isOpen_isCompact_isLevel E hU n hn S hS K' hK').2.2.1
  have hbfin : {q : r.ker ⧸ (globLev S K').subgroupOf r.ker | b q.out ≠ 0}.Finite := by
    refine Set.Finite.of_finite_image (f := fun q => (((q.out : r.ker) : finU E n) : finU E n ⧸ globLev S K'))
      ((GlobalTheory.TwTrLin.finite_out_support hopen hH'.1).subset ?_) fun p _ q _ h => ?_
    · rintro _ ⟨q, hq, rfl⟩
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (globLev S K') ((q.out : r.ker) : finU E n)
      change globFn S _ _ ≠ 0
      rw [hk, (hH'.2 _ k.2 _).2, ← hb]
      exact hq
    · have h' : ((((p.out : r.ker) : finU E n)) : finU E n ⧸ globLev S K') = ((q.out : r.ker) : finU E n) := h
      rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q]
      refine QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ?_)
      have := QuotientGroup.eq.1 h'
      simpa using this
  haveI := σ.irred
  have hiso : π ≤ LocUniq.isoPart σ.ρ ((RF E n).comp ι) := by
    obtain ⟨p, hp, -, φ, hφ0, hφm, hφ⟩ := hσ
    have hpe : ∀ g, p (e.symm g) = g := fun g => Subtype.ext ((hp _).trans (hιw g))
    let π' : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
    let s : UL n w →* UA E n := (finU E n).subtype.comp ι
    let Φ : σ.ρ.IntertwiningMap (π'.rep.comp s) :=
      ⟨φ.codRestrict π hφm, fun g => LinearMap.ext fun v => Subtype.ext (by
        have := hφ (e.symm g) v
        rw [hpe] at this
        exact this)⟩
    have hΦ0 : Φ ≠ 0 := fun h =>
      hφ0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
    obtain ⟨h1, -⟩ := GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (UL n w) π σ.V σ.V π'.rep s σ.ρ σ.ρ π'.isIrreducible_rep
      σ.irred σ.irred (fun g => ⟨e (GlobalTheory.DefU.LocRet.ret w n g), fun y => by
        have h3 := GlobalTheory.DefU.LocRet.commute_ret g (e.symm y)
        have h4 : s (e (GlobalTheory.DefU.LocRet.ret w n g)) = GlobalTheory.DefU.LocRet.ret w n g := by
          change ((e.symm (e _) : locU n w) : UA E n) = _
          rw [e.symm_apply_apply]
        rw [h4]
        exact h3⟩) Φ hΦ0
    intro v hv
    have hle : (⨆ ψ : σ.ρ.IntertwiningMap (π'.rep.comp s), LinearMap.range ψ.toLinearMap) ≤
        (LocUniq.isoPart σ.ρ ((RF E n).comp ι)).comap π.subtype := by
      refine iSup_le fun ψ => ?_
      rintro _ ⟨u, rfl⟩
      exact Submodule.mem_iSup_of_mem (⟨π.subtype ∘ₗ ψ.toLinearMap, fun g => LinearMap.ext fun y =>
        congrArg Subtype.val (LinearMap.congr_fun (ψ.isIntertwining' g) y)⟩ :
          σ.ρ.IntertwiningMap ((RF E n).comp ι)) ⟨u, rfl⟩
    rw [h1] at hle
    exact hle (Submodule.mem_top : (⟨v, hv⟩ : π) ∈ ⊤)
  exact trOn_levOp_cross ι r hr hc hK1 hK2 (RF E n) π (fun g v hv => hπ.stable _ v hv) σ.ρ hiso _ (KL n w) h0 _ _
    (f w) a' b hF hF' (fun k hk x => (hH.2 k hk x).2) (fun k hk x => (hH'.2 k hk x).2) (hf.1 w).2 hind.2
    (fun k hk x => by
      rw [hb, hb, hb]
      exact hH'.2 _ hk _)
    (GlobalTheory.TwTrLin.finite_out_support (hK'.1 w).1 (hf.1 w).1) (GlobalTheory.TwTrLin.finite_out_support (hK'.1 w).1 hind.1) hbfin

end GlobalTheory.BCT.Peel
end
end

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_heckeOperator_split_one_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Set (Pl E), IsSection S → ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ w ∈ S, ∀ σ : SmIrr (UL n w), IsCompU π w σ → trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' f) * twTr σ.ρ (KL n w) (K' w) ((K' w : Set (UL n w)).indicator 1) LinearMap.id = twTr σ.ρ (KL n w) (K' w) (f w) LinearMap.id * trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' (Function.update f w ((K' w : Set (UL n w)).indicator 1))) := by
  atlas_forward_decl GlobalTheory.BCT.Peel.trOn_hop_peel
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem trOn_eq_zero_of_finrank_eq_zero {V : Type} [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V)
    (L : V →ₗ[ℂ] V) (h : Module.finrank ℂ M = 0) : trOn M L = 0 := by
  unfold trOn
  split_ifs with hL
  · by_cases hf : FiniteDimensional ℂ M
    · haveI := hf
      haveI : Subsingleton M := Module.finrank_zero_iff.mp h
      rw [Subsingleton.elim (L.restrict hL) 0, map_zero]
    · rw [LinearMap.trace, dif_neg]
      · rfl
      · rintro ⟨s, ⟨b⟩⟩
        exact hf (Module.Finite.of_basis b)
  · rfl

theorem trOn_of_eq_smul {V : Type} [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V)
    (L : V →ₗ[ℂ] V) (c : ℂ) (h : ∀ v ∈ M, L v = c • v) : trOn M L = c * Module.finrank ℂ M := by
  have hM : ∀ v ∈ M, L v ∈ M := fun v hv => by rw [h v hv]; exact M.smul_mem c hv
  unfold trOn
  rw [dif_pos hM]
  have hr : L.restrict hM = c • LinearMap.id := by
    ext v
    simp [LinearMap.restrict_apply, h v v.2]
  rw [hr, map_smul, smul_eq_mul]
  by_cases hf : FiniteDimensional ℂ M
  · rw [LinearMap.trace_id]
  · rw [LinearMap.trace, dif_neg, Module.finrank_of_not_finite hf]
    · simp
    · rintro ⟨s, ⟨b⟩⟩
      exact hf (Module.Finite.of_basis b)

theorem trOn_hop_eq_dimW_mul_finprod_twTr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n), (∀ v, HasWeightAt π v.embedding (lam v)) → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ σ : ∀ w : Pl E, SmIrr (UL n w), (∀ w, IsCompU π w (σ w)) → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' f) = dimW lam * ∏ᶠ w ∈ S, twTr (σ w).ρ (KL n w) (K' w) (f w) LinearMap.id := by
  intro E _ _ _ hU n hn π hπ S hS lam hlam K' hK' σ hσ f hf
  have hTW := fun w => GlobalTheory.T.twistedTrace_indicator_level_localUnitary E n w (K' w) (hK'.1 w) (σ w)
  have hcongr : ∀ g g' : ∀ w : Pl E, UL n w → ℂ, (∀ w ∈ S, g w = g' w) → hop S K' g = hop S K' g' := by
    intro g g' h
    have : globFn S g = globFn S g' := by
      funext x
      unfold globFn
      exact finprod_mem_congr rfl (fun w hw => by rw [h w hw])
    unfold hop
    rw [this]
  have hfin : {w | ¬ ((f w = ((KL n w : Set (UL n w)).indicator 1) ∧ K' w = KL n w) ∧
      Module.finrank ℂ (fixed (σ w).ρ (KL n w)) = 1)}.Finite :=
    Filter.eventually_cofinite.1 ((hf.2.and hK'.2).and (GlobalTheory.T.finrank_integral_fixed_vectors_eq_one_almost_all E hU n hn π hπ σ hσ))
  set F := hfin.toFinset with hF
  have hout : ∀ w, w ∉ F → f w = (K' w : Set (UL n w)).indicator 1 ∧
      twTr (σ w).ρ (KL n w) (K' w) ((K' w : Set (UL n w)).indicator 1) LinearMap.id = 1 ∧
      (K' w).relIndex (KL n w) = 1 ∧ Module.finrank ℂ (fixed (σ w).ρ (K' w)) = 1 := by
    intro w hw
    rw [hF, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hw
    obtain ⟨⟨h1, h2⟩, h3⟩ := hw
    have hr : (K' w).relIndex (KL n w) = 1 := by rw [h2]; exact Subgroup.relIndex_self _
    have hd : Module.finrank ℂ (fixed (σ w).ρ (K' w)) = 1 := by rw [h2]; exact h3
    refine ⟨by rw [h1, h2], ?_, hr, hd⟩
    rw [(hTW w).2.2.1, hr, hd]
    simp
  set one : ∀ w : Pl E, UL n w → ℂ := fun w => (K' w : Set (UL n w)).indicator 1 with hone
  have key : ∀ U : Finset (Pl E), (↑U : Set (Pl E)) ⊆ S →
      trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' (fun w => if w ∈ U then f w else one w)) *
        ∏ w ∈ U, twTr (σ w).ρ (KL n w) (K' w) (one w) LinearMap.id =
      (∏ w ∈ U, twTr (σ w).ρ (KL n w) (K' w) (f w) LinearMap.id) *
        trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' one) := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.notMem_empty, if_false, Finset.prod_empty, mul_one, one_mul]
    | insert a U ha ih =>
      intro hsub
      have haS : a ∈ S := hsub (Finset.mem_insert_self a U)
      have hUS : (↑U : Set (Pl E)) ⊆ S := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      have hg : IsTest (KL n) K' (fun w => if w ∈ insert a U then f w else one w) := by
        refine ⟨fun w => ?_, ?_⟩
        · by_cases h : w ∈ insert a U
          · simp only [h, if_true]; exact hf.1 w
          · simp only [h, if_false]; exact (hTW w).1
        · filter_upwards [hf.2, hK'.2] with w h1 h2
          by_cases h : w ∈ insert a U
          · simp only [h, if_true]; exact h1
          · simp only [h, if_false, hone]; rw [h2]
      have hstep := GlobalTheory.T.trace_heckeOperator_split_one_place E hU n hn π hπ S hS K' hK' _ hg a haS (σ a) (hσ a)
      have hupd : Function.update (fun w => if w ∈ insert a U then f w else one w) a
          ((K' a : Set (UL n a)).indicator 1) = fun w => if w ∈ U then f w else one w := by
        funext w
        by_cases h : w = a
        · subst h
          simp [ha, hone]
        · rw [Function.update_of_ne h]
          simp [Finset.mem_insert, h]
      rw [hupd] at hstep
      simp only [Finset.mem_insert_self, if_true] at hstep
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have e1 : twTr (σ a).ρ (KL n a) (K' a) (one a) LinearMap.id =
          twTr (σ a).ρ (KL n a) (K' a) ((K' a : Set (UL n a)).indicator 1) LinearMap.id := rfl
      rw [e1]
      calc _ = (trOn (π ⊓ fixed (RF E n) (globLev S K'))
              (hop S K' (fun w => if w ∈ insert a U then f w else one w)) *
            twTr (σ a).ρ (KL n a) (K' a) ((K' a : Set (UL n a)).indicator 1) LinearMap.id) *
            ∏ w ∈ U, twTr (σ w).ρ (KL n w) (K' w) (one w) LinearMap.id := by ring
        _ = twTr (σ a).ρ (KL n a) (K' a) (f a) LinearMap.id *
            (trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' (fun w => if w ∈ U then f w else one w)) *
            ∏ w ∈ U, twTr (σ w).ρ (KL n w) (K' w) (one w) LinearMap.id) := by rw [hstep]; ring
        _ = _ := by rw [ih hUS]; ring
  set U := F.filter (· ∈ S) with hUdef
  have hUS : (↑U : Set (Pl E)) ⊆ S := fun x hx => (Finset.mem_filter.1 hx).2
  have hfU : hop S K' (fun w => if w ∈ U then f w else one w) = hop S K' f := by
    refine hcongr _ _ fun w hw => ?_
    by_cases h : w ∈ F
    · have : w ∈ U := Finset.mem_filter.2 ⟨h, hw⟩
      simp only [this, if_true]
    · have : w ∉ U := fun h' => h (Finset.mem_filter.1 h').1
      simp only [this, if_false, hone]
      exact ((hout w h).1).symm
  have hkey := key U hUS
  rw [hfU] at hkey

  have hfp : ∀ g : Pl E → ℂ, (∀ w, w ∉ F → g w = 1) → ∏ᶠ w ∈ S, g w = ∏ w ∈ U, g w := by
    intro g hg
    refine finprod_mem_eq_prod_of_subset g ?_ (fun x hx => (Finset.mem_filter.1 hx).2)
    rintro w ⟨hwS, hw1⟩
    by_cases h : w ∈ F
    · exact Finset.mem_filter.2 ⟨h, hwS⟩
    · exact absurd (hg w h) hw1
  have hRf := hfp (fun w => (((K' w).relIndex (KL n w) : ℕ) : ℂ)) (fun w hw => by simp [(hout w hw).2.2.1])
  have hDf := hfp (fun w => (Module.finrank ℂ (fixed (σ w).ρ (K' w)) : ℂ)) (fun w hw => by simp [(hout w hw).2.2.2])
  have hTf := hfp (fun w => twTr (σ w).ρ (KL n w) (K' w) (f w) LinearMap.id) (fun w hw => by
    rw [(hout w hw).1]; exact (hout w hw).2.1)
  have hbase : trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' one) =
      (∏ᶠ w ∈ S, (((K' w).relIndex (KL n w) : ℕ) : ℂ))⁻¹ *
        Module.finrank ℂ ↥(π ⊓ fixed (RF E n) (globLev S K')) :=
    trOn_of_eq_smul _ _ _ fun φ hφ => GlobalTheory.T.unitaryHeckeOperator_levelIndicator_eq_inv_index E hU n hn S hS K' hK' φ (Submodule.mem_inf.1 hφ).2
  have hdim := GlobalTheory.T.finrank_levelFixedVectors_definiteUnitary_eq_prod E hU n hn π hπ S hS lam hlam K' hK' σ hσ
  have hone_w : ∀ w, twTr (σ w).ρ (KL n w) (K' w) (one w) LinearMap.id =
      ((((K' w).relIndex (KL n w) : ℕ) : ℂ))⁻¹ * (Module.finrank ℂ (fixed (σ w).ρ (K' w)) : ℂ) :=
    fun w => (hTW w).2.2.1
  rw [Finset.prod_congr rfl (fun w _ => hone_w w)] at hkey
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib] at hkey
  rw [hbase, hdim, hRf, hDf] at hkey
  rw [hTf]
  have hR : (∏ w ∈ U, (((K' w).relIndex (KL n w) : ℕ) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun w _ => Nat.cast_ne_zero.2 (hTW w).2.1
  by_cases hD : (∏ w ∈ U, (Module.finrank ℂ (fixed (σ w).ρ (K' w)) : ℂ)) = 0
  · obtain ⟨w, hwU, hw0⟩ := Finset.prod_eq_zero_iff.1 hD
    have hw0' : Module.finrank ℂ (fixed (σ w).ρ (K' w)) = 0 := by exact_mod_cast hw0
    have hT0 : (∏ w ∈ U, twTr (σ w).ρ (KL n w) (K' w) (f w) LinearMap.id) = 0 :=
      Finset.prod_eq_zero hwU ((hTW w).2.2.2 hw0' (f w))
    rw [hT0, mul_zero]
    apply trOn_eq_zero_of_finrank_eq_zero
    have : (Module.finrank ℂ ↥(π ⊓ fixed (RF E n) (globLev S K')) : ℂ) = 0 := by
      rw [hdim, hDf, hD, mul_zero]
    exact_mod_cast this
  · have hne : (∏ w ∈ U, (((K' w).relIndex (KL n w) : ℕ) : ℂ))⁻¹ *
        ∏ w ∈ U, (Module.finrank ℂ (fixed (σ w).ρ (K' w)) : ℂ) ≠ 0 := mul_ne_zero (inv_ne_zero hR) hD
    apply mul_right_cancel₀ hne
    rw [hkey]
    ring

end GlobalTheory.BCT
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_hecke_levelVectors_eq_dim_mul_local_traces : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n), (∀ v, HasWeightAt π v.embedding (lam v)) → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ σ : ∀ w : Pl E, SmIrr (UL n w), (∀ w, IsCompU π w (σ w)) → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' f) = dimW lam * ∏ᶠ w ∈ S, twTr (σ w).ρ (KL n w) (K' w) (f w) LinearMap.id := by
  first | exact @GlobalTheory.BCT.trOn_hop_eq_dimW_mul_finprod_twTr | exact GlobalTheory.BCT.trOn_hop_eq_dimW_mul_finprod_twTr | (intros; apply GlobalTheory.BCT.trOn_hop_eq_dimW_mul_finprod_twTr <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem trOn_iSup_eq_sum : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ι : Type) [Fintype ι] (M : ι → Submodule ℂ V)
    (L : V →ₗ[ℂ] V), iSupIndep M → (∀ i, FiniteDimensional ℂ (M i)) → (∀ i, ∀ v ∈ M i, L v ∈ M i) →
    trOn (⨆ i, M i) L = ∑ i, trOn (M i) L := by
  intro V _ _ ι _ M L hind hfin hinv
  haveI := hfin
  have hp : (⨆ i, M i) = ⨆ i ∈ (Finset.univ : Finset ι), M i := by simp
  have hs : iSupIndep (fun i : (Finset.univ : Finset ι) ↦ M i) :=
    hind.comp Subtype.val_injective
  have hf : ∀ i, Set.MapsTo L (M i) (M i) := fun i v hv ↦ hinv i v hv
  have hsup : ∀ v ∈ (⨆ i, M i), L v ∈ (⨆ i, M i) := by
    intro v hv
    refine Submodule.iSup_induction M (motive := fun v ↦ L v ∈ ⨆ i, M i) hv ?_ ?_ ?_
    · intro i x hx; exact Submodule.mem_iSup_of_mem i (hinv i x hx)
    · simp
    · intro x y hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  have key := LinearMap.trace_eq_sum_trace_restrict_of_eq_biSup (N := M) Finset.univ hs hf
    (⨆ i, M i) hp hsup
  unfold trOn
  rw [dif_pos hsup, key]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [dif_pos (hinv i)]

end GlobalTheory.BCT
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceOnInvariantSubmodule_iSup_eq_sum : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ι : Type) [Fintype ι] (M : ι → Submodule ℂ V) (L : V →ₗ[ℂ] V), iSupIndep M → (∀ i, FiniteDimensional ℂ (M i)) → (∀ i, ∀ v ∈ M i, L v ∈ M i) → trOn (⨆ i, M i) L = ∑ i, trOn (M i) L := by
  first | exact @GlobalTheory.BCT.trOn_iSup_eq_sum | exact GlobalTheory.BCT.trOn_iSup_eq_sum | (intros; apply GlobalTheory.BCT.trOn_iSup_eq_sum <;> assumption)
end

section
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FibreCut

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def idemF (P : Set (Pl E)) : Af E :=
  ⟨fun v => if v ∈ P then 1 else 0,
    Filter.Eventually.of_forall fun v => by
      dsimp only
      split_ifs
      · exact one_mem _
      · exact zero_mem _⟩

def idem (P : Set (Pl E)) : Ad E := sFin E (idemF P)

theorem idem_mul_idem (P : Set (Pl E)) : idem P * idem P = idem P := by
  refine Prod.ext (mul_zero _) (FiniteAdeleRing.ext E fun v => ?_)
  change (idemF P).1 v * (idemF P).1 v = (idemF P).1 v
  simp only [idemF]
  split_ifs <;> simp

def sIdem (P : Set (Pl E)) : Ad E →ₙ+* Ad E where
  toFun x := idem P * x
  map_mul' x y := by
    calc idem P * (x * y) = (idem P * idem P) * (x * y) := by rw [idem_mul_idem]
      _ = idem P * x * (idem P * y) := by ring
  map_zero' := mul_zero _
  map_add' x y := mul_add _ _ _

theorem pInf_sIdem (P : Set (Pl E)) (x : Ad E) : pInf E (sIdem P x) = 0 := by
  change pInf E (sFin E (idemF P) * x) = 0
  rw [map_mul]
  have : pInf E (sFin E (idemF P)) = 0 := map_zero (infEq E).symm
  rw [this, zero_mul]

theorem pLoc_sIdem_of_mem (P : Set (Pl E)) {v : Pl E} (hv : v ∈ P) (x : Ad E) :
    ((pLoc E v).comp (pFin E)) (sIdem P x) = ((pLoc E v).comp (pFin E)) x := by
  change ((pLoc E v).comp (pFin E)) (idem P) * _ = _
  have : ((pLoc E v).comp (pFin E)) (idem P) = 1 := by
    change (idemF P).1 v = 1
    simp only [idemF, if_pos hv]
  rw [this, one_mul]
  rfl

theorem pLoc_sIdem_of_not_mem (P : Set (Pl E)) {v : Pl E} (hv : v ∉ P) (x : Ad E) :
    ((pLoc E v).comp (pFin E)) (sIdem P x) = 0 := by
  change ((pLoc E v).comp (pFin E)) (idem P) * _ = _
  have : ((pLoc E v).comp (pFin E)) (idem P) = 0 := by
    change (idemF P).1 v = 0
    simp only [idemF, if_neg hv]
  rw [this, zero_mul]

theorem conjAd_idem (P : Set (Pl E))
    (hP : ∀ u v : Pl E, u.under (𝓞 (maximalRealSubfield E)) = v.under (𝓞 (maximalRealSubfield E)) → u ∈ P → v ∈ P) :
    conjAd E (idem P) = idem P := by
  refine Prod.ext ?_ (FiniteAdeleRing.ext E fun v => ?_)
  · change (infEq E) ((starRingEnd (Cinf E)) ((infEq E).symm 0)) = 0
    simp
  change pLoc E v (conjFin (IsCMField.complexConj E).toRingEquiv (idemF P)) = (idemF P).1 v
  rw [pLoc_conjFin]
  change conjLoc _ v ((idemF P).1 _) = (idemF P).1 v
  have hc := GlobalTheory.DefU.LocRet.under_conjSrc (E := E) v
  simp only [idemF]
  split_ifs with h1 h2 h2
  · simp
  · exact absurd (hP _ _ hc h1) h2
  · exact absurd (hP _ _ hc.symm h2) h1
  · simp

variable {n : ℕ}

theorem cT_corner (P : Set (Pl E))
    (hP : ∀ u v : Pl E, u.under (𝓞 (maximalRealSubfield E)) = v.under (𝓞 (maximalRealSubfield E)) → u ∈ P → v ∈ P)
    (M : Matrix (Fin n) (Fin n) (Ad E)) :
    cT (conjAd E) (corner (matN n (sIdem P)) M) = corner (matN n (sIdem P)) (cT (conjAd E) M) := by
  ext i j
  change conjAd E ((1 : Matrix (Fin n) (Fin n) (Ad E)) j i - idem P * (1 : Matrix (Fin n) (Fin n) (Ad E)) j i +
      idem P * M j i) = (1 : Matrix (Fin n) (Fin n) (Ad E)) i j - idem P * (1 : Matrix (Fin n) (Fin n) (Ad E)) i j +
      idem P * conjAd E (M j i)
  rw [map_add, map_sub, map_mul, map_mul, conjAd_idem P hP, Matrix.one_apply, Matrix.one_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h, Ne.symm h]

theorem corner_mem (P : Set (Pl E))
    (hP : ∀ u v : Pl E, u.under (𝓞 (maximalRealSubfield E)) = v.under (𝓞 (maximalRealSubfield E)) → u ∈ P → v ∈ P)
    (g : UA E n) : cornerGL n (sIdem P) g.1 ∈ UA E n := by
  have hg : cT (conjAd E) (g.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * g.1 = 1 := g.2
  change cT (conjAd E) (corner (matN n (sIdem P)) g.1.1) * 1 * corner (matN n (sIdem P)) g.1.1 = 1
  rw [cT_corner P hP, Matrix.mul_one, ← map_mul, ← Matrix.mul_one (cT (conjAd E) _), hg, map_one]

theorem exists_cut : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : Set (Pl E)),
    (∀ u v : Pl E, u.under (𝓞 (maximalRealSubfield E)) = v.under (𝓞 (maximalRealSubfield E)) → u ∈ P → v ∈ P) →
    ∀ g ∈ finU E n, ∃ x ∈ finU E n, ∀ v : Pl E, cLoc v x = if v ∈ P then cLoc v g else 1 := by
  intro E _ _ _ n P hP g _
  refine ⟨⟨cornerGL n (sIdem P) g.1, corner_mem P hP g⟩, ?_, fun v => ?_⟩
  · exact MonoidHom.mem_ker.2 (map_cornerGL_of_zero _ _ (pInf_sIdem P) _)
  · split_ifs with hv
    · exact map_cornerGL_of_hom _ _ _ (pLoc_sIdem_of_mem P hv) _
    · exact map_cornerGL_of_zero _ _ (pLoc_sIdem_of_not_mem P hv) _

end GlobalTheory.FibreCut

end
end

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelicUnitaryPoint_cut_to_fibreUnion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : Set (Pl E)),
    (∀ u v : Pl E, u.under (𝓞 (maximalRealSubfield E)) = v.under (𝓞 (maximalRealSubfield E)) → u ∈ P → v ∈ P) →
    ∀ g ∈ finU E n, ∃ x ∈ finU E n, ∀ v : Pl E, cLoc v x = if v ∈ P then cLoc v g else 1 := by
  atlas_forward_decl GlobalTheory.FibreCut.exists_cut
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_open_nhd_one_of_integral_eq_one_on_finset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (U : Set (finU E n)), IsOpen U →
    (1 : finU E n) ∈ U → ∃ T : Finset (Pl E), ∀ u : finU E n, (∀ v ∈ T, cLoc v (u : UA E n) = 1) →
    (∀ (v : Pl E) (i j : Fin n), (cLoc v (u : UA E n)) i j ∈ v.adicCompletionIntegers E) →
    (∀ (v : Pl E) (i j : Fin n), (cLoc v (u : UA E n))⁻¹ i j ∈ v.adicCompletionIntegers E) → u ∈ U := by
  first | exact @GlobalTheory.FixLevOpen.mem_of_isOpen_of_eq_one_on_finset | exact GlobalTheory.FixLevOpen.mem_of_isOpen_of_eq_one_on_finset | (intros; apply GlobalTheory.FixLevOpen.mem_of_isOpen_of_eq_one_on_finset <;> assumption)
end

section
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FixLev
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem ext_fin {x y : UA E n} (hx : x ∈ finU E n) (hy : y ∈ finU E n) (h : ∀ v : Pl E, cLoc v x = cLoc v y) : x = y := by
  have hx' : cInf x = 1 := hx
  have hy' : cInf y = 1 := hy
  apply Subtype.ext
  apply ga_ext
  · exact hx'.trans hy'.symm
  · exact Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v =>
      by
        have := congrArg (fun z : GLw n v => (z : Matrix (Fin n) (Fin n) (v.adicCompletion E)) i j) (h v)
        exact this)

theorem integral_eventually (g : UA E n) : ∀ᶠ v in cofinite, ∀ i j : Fin n,
    (cLoc v g) i j ∈ v.adicCompletionIntegers E ∧ (cLoc v g)⁻¹ i j ∈ v.adicCompletionIntegers E := by
  have h1 : ∀ x : Af E, ∀ᶠ v in cofinite, pLoc E v x ∈ v.adicCompletionIntegers E := fun x => x.2
  have h2 : ∀ i j : Fin n, ∀ᶠ v in cofinite,
      (cLoc v g) i j ∈ v.adicCompletionIntegers E ∧ (cLoc v g)⁻¹ i j ∈ v.adicCompletionIntegers E := by
    intro i j
    filter_upwards [h1 (pFin E ((g : GA E n) i j)), h1 (pFin E (((g⁻¹ : UA E n) : GA E n) i j))] with v hv hv'
    refine ⟨hv, ?_⟩
    rw [← map_inv]
    exact hv'
  exact Filter.eventually_all.2 fun i => Filter.eventually_all.2 (h2 i)

def fib (B : Finset (Pl E)) : Set (Pl E) :=
  {u | ∃ t ∈ B, u.under (𝓞 (maximalRealSubfield E)) = t.under (𝓞 (maximalRealSubfield E))}

theorem fib_closed (B : Finset (Pl E)) (u v : Pl E)
    (h : u.under (𝓞 (maximalRealSubfield E)) = v.under (𝓞 (maximalRealSubfield E))) (hu : u ∈ fib B) : v ∈ fib B := by
  obtain ⟨t, ht, e⟩ := hu
  exact ⟨t, ht, h.symm.trans e⟩

def stabU (φ : UA E n → ℂ) : Subgroup (UA E n) where
  carrier := {x | RU E n x φ = φ}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem one_entry_mem (v : Pl E) (i j : Fin n) : (1 : GLw n v) i j ∈ v.adicCompletionIntegers E := by
  change (1 : Matrix (Fin n) (Fin n) (v.adicCompletion E)) i j ∈ _
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem local_fixed (S : Set (Pl E)) (hS : IsSection S) (K' : ∀ w : Pl E, Subgroup (UL n w)) (φ : UA E n → ℂ)
    (hφ : ∀ w ∈ S, ∀ x ∈ locU n w, (∃ k ∈ K' w, k.1 = cLoc w x) → RU E n x φ = φ) (B : Finset (Pl E)) :
    ∀ h : UA E n, h ∈ finU E n → (∀ w ∈ S, ∃ k ∈ K' w, k.1 = cLoc w h) → (∀ v, v ∉ fib B → cLoc v h = 1) →
      h ∈ stabU φ := by
  induction B using Finset.induction_on with
  | empty =>
    intro h hfin _ h1
    have : h = 1 := ext_fin hfin (one_mem _) fun v => by
      rw [h1 v (by rintro ⟨t, ht, _⟩; simp at ht), map_one]
    rw [this]
    exact one_mem _
  | insert t B _ ih =>
    intro h hfin hK h1
    obtain ⟨wt, ⟨hwtS, hwt⟩, _⟩ := hS t
    obtain ⟨x, hxfin, hx⟩ := GlobalTheory.T.exists_finiteAdelicUnitaryPoint_cut_to_fibreUnion E n (fib {t}) (fib_closed {t}) h hfin
    have hxloc : x ∈ locU n wt := by
      refine Subgroup.mem_inf.2 ⟨hxfin, Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => ?_⟩
      rw [MonoidHom.mem_ker, hx u, if_neg]
      rintro ⟨t', ht', e⟩
      rw [Finset.mem_singleton] at ht'
      subst ht'
      exact hu (e.trans hwt.symm)
    have hwtf : wt ∈ fib {t} := ⟨t, Finset.mem_singleton_self t, hwt⟩
    have hxS : x ∈ stabU φ := by
      obtain ⟨k, hk, hkx⟩ := hK wt hwtS
      refine hφ wt hwtS x hxloc ⟨k, hk, ?_⟩
      rw [hx wt, if_pos hwtf, hkx]
    have hrest : x⁻¹ * h ∈ stabU φ := by
      refine ih _ (mul_mem (inv_mem hxfin) hfin) ?_ ?_
      · intro w hw
        rw [map_mul, map_inv, hx w]
        split_ifs
        · exact ⟨1, one_mem _, by rw [inv_mul_cancel]; rfl⟩
        · rw [inv_one, one_mul]; exact hK w hw
      · intro v hv
        rw [map_mul, map_inv, hx v]
        split_ifs with hvt
        · exact inv_mul_cancel _
        · rw [inv_one, one_mul]
          refine h1 v ?_
          rintro ⟨t', ht', e⟩
          rcases Finset.mem_insert.1 ht' with rfl | ht'
          · exact hvt ⟨t', Finset.mem_singleton_self _, e⟩
          · exact hv ⟨t', ht', e⟩
    have : h = x * (x⁻¹ * h) := by group
    rw [this]
    exact mul_mem hxS hrest

theorem inf_fixed_globLev_ne_bot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S →
    ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' →
    ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → HasLevel S π K' → π ⊓ fixed (RF E n) (globLev S K') ≠ ⊥ := by
  intro E _ _ _ n S hS K' _ π hπ hL
  obtain ⟨φ, hφπ, hφ0, hφfix⟩ := hL
  have hlev := (hπ.aut φ hφπ).level
  have key : ∀ g : finU E n, g ∈ globLev S K' → (g : UA E n) ∈ stabU φ := by
    intro g hg
    have hgS : ∀ w ∈ S, ∃ k ∈ K' w, k.1 = cLoc w (g : UA E n) := by
      intro w hw
      have h1 := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg w) hw
      rw [Subgroup.mem_comap] at h1
      obtain ⟨k, hk, e⟩ := Subgroup.mem_map.1 h1
      exact ⟨k, hk, e⟩
    obtain ⟨T, hT⟩ := GlobalTheory.T.mem_open_nhd_one_of_integral_eq_one_on_finset E n _ hlev (by simp)
    have hbad := Filter.eventually_cofinite.1 (integral_eventually (g : UA E n))
    let B : Finset (Pl E) := T ∪ hbad.toFinset
    obtain ⟨x, hxfin, hx⟩ := GlobalTheory.T.exists_finiteAdelicUnitaryPoint_cut_to_fibreUnion E n (fib B) (fib_closed B) (g : UA E n) g.2
    have hxS : x ∈ stabU φ := by
      refine local_fixed S hS K' φ hφfix B x hxfin ?_ ?_
      · intro w hw
        rw [hx w]
        split_ifs
        · exact hgS w hw
        · exact ⟨1, one_mem _, rfl⟩
      · intro v hv
        rw [hx v, if_neg hv]
    have hc : ∀ v, cLoc v (x⁻¹ * (g : UA E n)) = if v ∈ fib B then 1 else cLoc v (g : UA E n) := by
      intro v
      rw [map_mul, map_inv, hx v]
      split_ifs
      · exact inv_mul_cancel _
      · rw [inv_one, one_mul]
    have hint : ∀ v, v ∉ fib B → ∀ i j : Fin n, (cLoc v (g : UA E n)) i j ∈ v.adicCompletionIntegers E ∧
        (cLoc v (g : UA E n))⁻¹ i j ∈ v.adicCompletionIntegers E := by
      intro v hv
      by_contra hc'
      exact hv ⟨v, Finset.mem_union_right _ (hbad.mem_toFinset.2 hc'), rfl⟩
    have hrest : x⁻¹ * (g : UA E n) ∈ stabU φ := by
      have := hT ⟨x⁻¹ * (g : UA E n), mul_mem (inv_mem hxfin) g.2⟩ ?_ ?_ ?_
      · exact this
      · intro v hv
        change cLoc v (x⁻¹ * (g : UA E n)) = 1
        rw [hc v, if_pos ⟨v, Finset.mem_union_left _ hv, rfl⟩]
      · intro v i j
        change (cLoc v (x⁻¹ * (g : UA E n))) i j ∈ _
        rw [hc v]
        split_ifs with hv
        · exact one_entry_mem v i j
        · exact (hint v hv i j).1
      · intro v i j
        change (cLoc v (x⁻¹ * (g : UA E n)))⁻¹ i j ∈ _
        rw [hc v]
        split_ifs with hv
        · rw [inv_one]; exact one_entry_mem v i j
        · exact (hint v hv i j).2
    have : (g : UA E n) = x * (x⁻¹ * (g : UA E n)) := by group
    rw [this]
    exact mul_mem hxS hrest
  intro hbot
  have hmem : φ ∈ π ⊓ fixed (RF E n) (globLev S K') := by
    refine ⟨hφπ, ?_⟩
    intro h
    change RU E n ((h : finU E n) : UA E n) φ = (1 : ℂˣ) • φ
    rw [one_smul]
    exact key h h.2
  rw [hbot] at hmem
  exact hφ0 ((Submodule.mem_bot ℂ).1 hmem)

end GlobalTheory.FixLev
end
end

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inf_fixedVectors_adelicLevel_ne_bot_of_localLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → HasLevel S π K' → π ⊓ fixed (RF E n) (globLev S K') ≠ ⊥ := by
  atlas_forward_decl GlobalTheory.FixLev.inf_fixed_globLev_ne_bot
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeOperator_testFamily_preserves_level_forms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ v ∈ π ⊓ fixed (RF E n) (globLev S K'), hop S K' f v ∈ π ⊓ fixed (RF E n) (globLev S K') := by
  first | exact @GlobalTheory.BCT.hop_mem_inf_fixed | exact GlobalTheory.BCT.hop_mem_inf_fixed | (intros; apply GlobalTheory.BCT.hop_mem_inf_fixed <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem isCompU_of_equiv {π : Submodule ℂ (UA E n → ℂ)} {w : Pl E} {σ σ' : SmIrr (UL n w)}
    (h : IsCompU π w σ) (e : σ.ρ.Equiv σ'.ρ) : IsCompU π w σ' := by
  obtain ⟨p, hp, -, f, hf0, hfπ, hfe⟩ := h
  let g : σ'.V →ₗ[ℂ] σ.V := e.symm.toLinearEquiv.toLinearMap
  have hg : ∀ x v, g (σ'.ρ x v) = σ.ρ x (g v) := fun x v =>
    LinearMap.congr_fun (e.symm.isIntertwining' x) v
  refine ⟨p, hp, σ'.irred, f ∘ₗ g, ?_, fun v => hfπ _, fun x v => ?_⟩
  · intro h0
    apply hf0
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun h0 (e.toLinearEquiv v)
    simpa [g] using this
  · simp only [LinearMap.comp_apply, hg, hfe]

theorem hasLevel_of_fixed {S : Set (Pl E)} (hS : IsSection S) {π : Submodule ℂ (UA E n → ℂ)}
    {K' : ∀ w : Pl E, Subgroup (UL n w)} (h : π ⊓ fixed (RF E n) (globLev S K') ≠ ⊥) : HasLevel S π K' := by
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine ⟨φ, (Submodule.mem_inf.1 hφ).1, hφ0, fun w hw x hx hk => ?_⟩
  obtain ⟨k, hk, hkx⟩ := hk
  have hxf : x ∈ finU E n := hx.1
  have hmem : (⟨x, hxf⟩ : finU E n) ∈ globLev S K' := by
    simp only [globLev, Subgroup.mem_iInf, Subgroup.mem_comap, Subgroup.mem_map]
    intro w' hw'
    by_cases hww : w' = w
    · subst hww
      exact ⟨k, hk, hkx⟩
    · have hu : w'.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) := by
        intro he
        exact hww ((hS w).unique ⟨hw', he⟩ ⟨hw, rfl⟩)
      have hker : x ∈ (cLoc w').ker :=
        Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 w') hu
      refine ⟨1, one_mem _, ?_⟩
      simpa using (MonoidHom.mem_ker.1 hker).symm
  have := (Submodule.mem_inf.1 hφ).2 ⟨_, hmem⟩
  simpa [fixed, eig, RF] using this

theorem dimW_ne_zero (lam : InfinitePlace E → DomWeight n) : dimW lam ≠ 0 := by
  unfold dimW
  rw [Finset.prod_ne_zero_iff]
  intro v _
  rw [map_one, LinearMap.trace_one]
  exact_mod_cast Module.finrank_pos.ne'

end GlobalTheory.BCT
end
