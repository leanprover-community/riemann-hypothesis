import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPreFamilyOfLatticeFamilyTwo
import Development.WeilBound.CoreStatements.IdealCycleValues.IsModelOverRamifiedBaseChange
import BuildAid.ForwardExisting
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDvrConeDimTrdeg
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NatDegreeMinpolyEqOfClosed
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycNumIntAndComb

section
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem numbers_divCycle_baseChange_dvr : ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] (ϖ : O) (ϖ' : O') (u : O'ˣ) (e : ℕ), Irreducible ϖ → Irreducible ϖ' → 0 < e → algebraMap O O' ϖ = u * ϖ' ^ e → ∀ (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MvPolynomial (Σ k, J k) O)) (d : ℕ), IsModelOver P d → IsModelOver (P.map (MvPolynomial.map (algebraMap O O'))) d → ∀ (a : K → ℕ) (f : MvPolynomial (Σ k, J k) O), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f a → f ∉ P → ∀ l : List (K → ℤ), l.length = d → cycList (divCycle (P.map (MvPolynomial.map (algebraMap O O'))) (MvPolynomial.map (algebraMap O O') f)) l = e * cycList (divCycle P f) l :=
  BaseChangeColon.isModelOver_ramified_base_change

end GlobalTheory.CompanionTheory.Ar.Num
end

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_over_ramified_extension : ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] (ϖ : O) (ϖ' : O') (u : O'ˣ) (e : ℕ), Irreducible ϖ → Irreducible ϖ' → 0 < e → algebraMap O O' ϖ = u * ϖ' ^ e → ∀ (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MvPolynomial (Σ k, J k) O)) (d : ℕ), IsModelOver P d → IsModelOver (P.map (MvPolynomial.map (algebraMap O O'))) d → ∀ (a : K → ℕ) (f : MvPolynomial (Σ k, J k) O), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f a → f ∉ P → ∀ l : List (K → ℤ), l.length = d → cycList (divCycle (P.map (MvPolynomial.map (algebraMap O O'))) (MvPolynomial.map (algebraMap O O') f)) l = e * cycList (divCycle P f) l := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Num.numbers_divCycle_baseChange_dvr
end

section
section
namespace GlobalTheory.CompanionTheory.Ar.Num.BaseChange

noncomputable section

section Fields

open scoped IntermediateField

theorem linearDisjoint_algebraicClosure {F Ω L : Type} [Field F] [CharZero F] [Field Ω] [Field L]
    [Algebra F Ω] [Algebra Ω L] [Algebra F L] [IsScalarTower F Ω L]
    (h : ∀ a : Ω, IsAlgebraic F a → a ∈ Set.range (algebraMap F Ω)) :
    (algebraicClosure F L).LinearDisjoint Ω := by
  have : Algebra.IsIntegral F (algebraicClosure F L).toSubalgebra :=
    (algebraicClosure.isAlgebraic F L).isIntegral
  refine Subalgebra.LinearDisjoint.of_linearDisjoint_finite_left _ _ fun B hB _ => ?_
  have halg : B.IsAlgebraic := fun x hx => (mem_algebraicClosure_iff (F := F)).1 (hB hx)
  let M : IntermediateField F L := halg.toIntermediateField
  haveI : FiniteDimensional F M := ‹Module.Finite F B›
  change M.LinearDisjoint Ω
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element F M
  have hi : IsIntegral F (θ : L) := (Algebra.IsIntegral.isIntegral (R := F) θ).map M.val
  have e : F⟮(θ : L)⟯ = M := by
    have := congrArg (IntermediateField.lift (F := M)) hθ
    simpa using this
  rw [← e]
  refine IntermediateField.LinearDisjoint.of_basis_left
    (IntermediateField.adjoin.powerBasis hi).basis ?_
  have hd := GlobalTheory.CompanionTheory.Ar.Cmp.RegularTensor.natDegree_minpoly_eq_of_closed (k := F) (F := Ω) h hi
  have hl := linearIndependent_pow (K := Ω) (θ : L)
  rw [hd] at hl
  have he : (F⟮(θ : L)⟯.val ∘ (IntermediateField.adjoin.powerBasis hi).basis) =
      fun i : Fin (IntermediateField.adjoin.powerBasis hi).dim => (θ : L) ^ (i : ℕ) := by
    funext i
    simp
  rw [he]
  exact hl

theorem linearIndependent_of_closed {F Ω L : Type} [Field F] [CharZero F] [Field Ω] [Field L]
    [Algebra F Ω] [Algebra Ω L] [Algebra F L] [IsScalarTower F Ω L]
    (h : ∀ a : Ω, IsAlgebraic F a → a ∈ Set.range (algebraMap F Ω))
    {ι : Type} {e : ι → L} (he : ∀ i, IsAlgebraic F (e i)) (hli : LinearIndependent F e) :
    LinearIndependent Ω e := by
  have H := linearDisjoint_algebraicClosure (L := L) h
  let a : ι → algebraicClosure F L := fun i => ⟨e i, mem_algebraicClosure_iff.2 (he i)⟩
  have ha : LinearIndependent F a :=
    LinearIndependent.of_comp (algebraicClosure F L).val.toLinearMap hli
  exact H.linearIndependent_left ha

end Fields

section Rings

theorem linearIndependent_base {O Ω O' Ω' : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field Ω] [CharZero Ω] [Algebra O Ω] [CommRing O'] [IsDomain O']
    [Algebra O O'] [Algebra.IsAlgebraic O O'] [Field Ω'] [Algebra Ω Ω'] [Algebra O' Ω'] [Algebra O Ω']
    [IsScalarTower O O' Ω'] [IsScalarTower O Ω Ω'] (hcl : IsIntegrallyClosedIn O Ω)
    (hinj : Function.Injective (algebraMap O' Ω')) {ι : Type} {e : ι → O'}
    (hli : LinearIndependent O e) :
    LinearIndependent Ω (fun i => algebraMap O' Ω' (e i)) := by
  haveI := hcl
  have hOΩ : Function.Injective (algebraMap O Ω) := IsIntegralClosure.algebraMap_injective O O Ω
  haveI : FaithfulSMul O Ω := (faithfulSMul_iff_algebraMap_injective O Ω).2 hOΩ
  let F := FractionRing O
  letI : Algebra F Ω := FractionRing.liftAlgebra O Ω
  haveI : IsScalarTower O F Ω := FractionRing.isScalarTower_liftAlgebra O Ω
  letI : Algebra F Ω' := ((algebraMap Ω Ω').comp (algebraMap F Ω)).toAlgebra
  haveI : IsScalarTower F Ω Ω' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower O F Ω' := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap O Ω' a = algebraMap Ω Ω' (algebraMap F Ω (algebraMap O F a))
    rw [← IsScalarTower.algebraMap_apply O F Ω, ← IsScalarTower.algebraMap_apply O Ω Ω']
  haveI : CharZero F := RingHom.charZero (algebraMap F Ω)
  have hclosed : ∀ a : Ω, IsAlgebraic F a → a ∈ Set.range (algebraMap F Ω) := by
    intro a ha
    obtain ⟨r, hr, hint⟩ := ((IsFractionRing.isAlgebraic_iff O F Ω).2 ha).exists_integral_multiple
    obtain ⟨c, hc⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := O) (A := Ω)).1 hint
    have hr' : algebraMap O Ω r ≠ 0 := fun h0 => hr (hOΩ (by rw [h0, map_zero]))
    refine ⟨algebraMap O F c / algebraMap O F r, ?_⟩
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, hc,
      Algebra.smul_def]
    field_simp
  have he : ∀ i, IsAlgebraic F (algebraMap O' Ω' (e i)) := fun i =>
    (IsFractionRing.isAlgebraic_iff O F Ω').1
      ((Algebra.IsAlgebraic.isAlgebraic (R := O) (e i)).algHom (IsScalarTower.toAlgHom O O' Ω'))
  have hli' : LinearIndependent O (fun i => algebraMap O' Ω' (e i)) :=
    hli.map' (IsScalarTower.toAlgHom O O' Ω').toLinearMap
      (LinearMap.ker_eq_bot.2 hinj)
  exact linearIndependent_of_closed hclosed he ((LinearIndependent.iff_fractionRing O F).1 hli')

open MvPolynomial

theorem exists_decomp {O O' σ : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [CommRing O']
    [IsDomain O'] [Algebra O O'] (hinj : Function.Injective (algebraMap O O'))
    (f : MvPolynomial σ O') :
    ∃ (r : ℕ) (e : Fin r → O') (g : Fin r → MvPolynomial σ O), LinearIndependent O e ∧
      f = ∑ i, C (e i) * MvPolynomial.map (algebraMap O O') (g i) := by
  classical
  let M : Submodule O O' := Submodule.span O (↑(f.support.image (fun m => coeff m f)) : Set O')
  haveI : Module.Finite O M := Module.Finite.span_of_finite O (Finset.finite_toSet _)
  haveI : FaithfulSMul O O' := (faithfulSMul_iff_algebraMap_injective O O').2 hinj
  haveI : Module.Free O M := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis O M
  have hm : ∀ m, coeff m f ∈ M := by
    intro m
    by_cases h : m ∈ f.support
    · exact Submodule.subset_span (by simpa using ⟨m, by simpa using h, rfl⟩)
    · rw [notMem_support_iff.1 h]
      exact M.zero_mem
  let cm : (σ →₀ ℕ) → M := fun m => ⟨coeff m f, hm m⟩
  let g : Fin (Module.finrank O M) → MvPolynomial σ O :=
    fun i => ∑ m ∈ f.support, monomial m (b.repr (cm m) i)
  have hg : ∀ m i, coeff m (g i) = b.repr (cm m) i := by
    intro m i
    by_cases h : m ∈ f.support
    · simp [g, coeff_sum, coeff_monomial, h]
    · have h0 : cm m = 0 := Subtype.ext (notMem_support_iff.1 h)
      simp [g, coeff_sum, coeff_monomial, h, h0]
  refine ⟨_, fun i => (b i : O'), g, ?_, ?_⟩
  · exact b.linearIndependent.map' M.subtype (Submodule.ker_subtype _)
  · ext m
    have h1 : (cm m : O') = ∑ i, b.repr (cm m) i • (b i : O') := by
      have h := congrArg (fun z : M => (z : O')) (b.sum_repr (cm m))
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at h
      exact h.symm
    have h2 : coeff m f = (cm m : O') := rfl
    rw [h2, h1, coeff_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_C_mul, coeff_map, hg, Algebra.smul_def, mul_comm]

theorem trdeg_eq {σ O O' : Type} [CommRing O] [IsDomain O] [CommRing O'] [IsDomain O'] [Algebra O O']
    [Algebra.IsAlgebraic O O'] (hinj : Function.Injective (algebraMap O O'))
    {P : Ideal (MvPolynomial σ O)} {P' : Ideal (MvPolynomial σ O')} [P.IsPrime] [P'.IsPrime]
    (hc : P'.comap (MvPolynomial.map (algebraMap O O')) = P)
    (hC : P.comap (C : O →+* MvPolynomial σ O) = ⊥)
    (hC' : P'.comap (C : O' →+* MvPolynomial σ O') = ⊥) :
    Algebra.trdeg O' (MvPolynomial σ O' ⧸ P') = Algebra.trdeg O (MvPolynomial σ O ⧸ P) := by
  let φ : (MvPolynomial σ O ⧸ P) →+* (MvPolynomial σ O' ⧸ P') :=
    Ideal.quotientMap P' (MvPolynomial.map (algebraMap O O')) hc.ge
  have hφ : Function.Injective φ := Ideal.quotientMap_injective' hc.le
  let _ : Algebra (MvPolynomial σ O ⧸ P) (MvPolynomial σ O' ⧸ P') := φ.toAlgebra
  have hφa : ∀ t, algebraMap (MvPolynomial σ O ⧸ P) (MvPolynomial σ O' ⧸ P') (Ideal.Quotient.mk P t) =
      Ideal.Quotient.mk P' (MvPolynomial.map (algebraMap O O') t) := fun t => Ideal.quotientMap_mk
  have : IsScalarTower O (MvPolynomial σ O ⧸ P) (MvPolynomial σ O' ⧸ P') :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change _ = algebraMap (MvPolynomial σ O ⧸ P) (MvPolynomial σ O' ⧸ P')
        (Ideal.Quotient.mk P (C a))
      rw [hφa, map_C]
      rfl
  have : IsScalarTower O O' (MvPolynomial σ O' ⧸ P') := inferInstance
  have hOS : Function.Injective (algebraMap O (MvPolynomial σ O ⧸ P)) := by
    refine (injective_iff_map_eq_zero (algebraMap O (MvPolynomial σ O ⧸ P))).2 fun a ha => ?_
    have h : (C a : MvPolynomial σ O) ∈ P :=
      Ideal.Quotient.eq_zero_iff_mem.1 (show Ideal.Quotient.mk P (C a) = 0 from ha)
    have : a ∈ P.comap (C : O →+* MvPolynomial σ O) := h
    rw [hC] at this
    exact (Submodule.mem_bot _).1 this
  have hOS' : Function.Injective (algebraMap O' (MvPolynomial σ O' ⧸ P')) := by
    refine (injective_iff_map_eq_zero (algebraMap O' (MvPolynomial σ O' ⧸ P'))).2 fun a ha => ?_
    have h : (C a : MvPolynomial σ O') ∈ P' :=
      Ideal.Quotient.eq_zero_iff_mem.1 (show Ideal.Quotient.mk P' (C a) = 0 from ha)
    have : a ∈ P'.comap (C : O' →+* MvPolynomial σ O') := h
    rw [hC'] at this
    exact (Submodule.mem_bot _).1 this
  have : FaithfulSMul (MvPolynomial σ O ⧸ P) (MvPolynomial σ O' ⧸ P') :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  have : FaithfulSMul O (MvPolynomial σ O ⧸ P) := (faithfulSMul_iff_algebraMap_injective _ _).2 hOS
  have : FaithfulSMul O' (MvPolynomial σ O' ⧸ P') := (faithfulSMul_iff_algebraMap_injective _ _).2 hOS'
  have : FaithfulSMul O O' := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : Algebra.IsAlgebraic (MvPolynomial σ O ⧸ P) (MvPolynomial σ O' ⧸ P') := by
    refine ⟨fun b => ?_⟩
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
    induction f using MvPolynomial.induction_on with
    | C a =>
      have h1 : IsAlgebraic O (algebraMap O' (MvPolynomial σ O' ⧸ P') a) :=
        (Algebra.IsAlgebraic.isAlgebraic (R := O) a).algHom
          (IsScalarTower.toAlgHom O O' (MvPolynomial σ O' ⧸ P'))
      exact h1.extendScalars hOS
    | add p q hp hq =>
      rw [map_add]
      exact hp.add hq
    | mul_X p i hp =>
      rw [map_mul]
      refine hp.mul ?_
      have h2 : Ideal.Quotient.mk P' (X i) = algebraMap (MvPolynomial σ O ⧸ P) (MvPolynomial σ O' ⧸ P')
          (Ideal.Quotient.mk P (X i)) := by
        rw [hφa, map_X]
      rw [h2]
      exact isAlgebraic_algebraMap _
  have h1 := trdeg_add_eq O O' (A := MvPolynomial σ O' ⧸ P')
  have h2 := trdeg_add_eq O (MvPolynomial σ O ⧸ P) (A := MvPolynomial σ O' ⧸ P')
  rw [trdeg_eq_zero (R := O) (A := O'), zero_add] at h1
  rw [trdeg_eq_zero (R := MvPolynomial σ O ⧸ P) (A := MvPolynomial σ O' ⧸ P'), add_zero] at h2
  exact h1.trans h2.symm

open GroundTheory.Heights₂.Heights.NumbersDVR

section Point

variable {O Ω O' Ω' : Type} [CommRing O] [Field Ω] [Algebra O Ω] [CommRing O']
  [Algebra O O'] [Field Ω'] [Algebra Ω Ω'] [Algebra O' Ω'] [Algebra O Ω']
  [IsScalarTower O O' Ω'] [IsScalarTower O Ω Ω']
  {K : Type} {J : K → Type} (y : (Σ k, J k) → Ω)

theorem pointConeMap_map (h : MvPolynomial (Σ k, J k) O) :
    pointConeMap O' (fun v => algebraMap Ω Ω' (y v)) (MvPolynomial.map (algebraMap O O') h) =
      MvPolynomial.map (algebraMap Ω Ω') (pointConeMap O y h) := by
  induction h using MvPolynomial.induction_on with
  | C a =>
    simp only [pointConeMap, map_C, aeval_C, MvPolynomial.algebraMap_apply]
    rw [← IsScalarTower.algebraMap_apply O O' Ω', ← IsScalarTower.algebraMap_apply O Ω Ω']
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    simp [pointConeMap]

theorem map_le_pointIdeal :
    (pointIdeal O y).map (MvPolynomial.map (algebraMap O O')) ≤
      pointIdeal O' (fun v => algebraMap Ω Ω' (y v)) := by
  rw [Ideal.map_le_iff_le_comap]
  intro h hh
  have h0 : pointConeMap O y h = 0 := hh
  change pointConeMap O' (fun v => algebraMap Ω Ω' (y v)) (MvPolynomial.map (algebraMap O O') h) = 0
  rw [pointConeMap_map, h0, map_zero]

theorem comap_pointIdeal :
    (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))).comap (MvPolynomial.map (algebraMap O O')) =
      pointIdeal O y := by
  ext h
  change pointConeMap O' (fun v => algebraMap Ω Ω' (y v)) (MvPolynomial.map (algebraMap O O') h) = 0 ↔
    pointConeMap O y h = 0
  rw [pointConeMap_map]
  exact map_eq_zero_iff _ (MvPolynomial.map_injective _ (algebraMap Ω Ω').injective)

theorem comap_C_pointIdeal_eq_bot (hinj : Function.Injective (algebraMap O' Ω')) :
    (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))).comap
      (C : O' →+* MvPolynomial (Σ k, J k) O') = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  have h0 : pointConeMap O' (fun v => algebraMap Ω Ω' (y v))
      (C a : MvPolynomial (Σ k, J k) O') = 0 := ha
  simp only [pointConeMap, aeval_C, MvPolynomial.algebraMap_eq] at h0
  have h1 : algebraMap O' Ω' a = 0 := by
    simpa using h0
  exact (Submodule.mem_bot _).2 (hinj (by rw [h1, map_zero]))

end Point

section Main

variable {O Ω O' Ω' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Ω]
  [CharZero Ω] [Algebra O Ω] [CommRing O'] [IsDomain O'] [Algebra O O'] [Algebra.IsAlgebraic O O']
  [Field Ω'] [Algebra Ω Ω'] [Algebra O' Ω'] [Algebra O Ω'] [IsScalarTower O O' Ω']
  [IsScalarTower O Ω Ω'] {K : Type} {J : K → Type} (y : (Σ k, J k) → Ω)

theorem exists_decomp_mem (hcl : IsIntegrallyClosedIn O Ω)
    (hinj : Function.Injective (algebraMap O' Ω')) (hOO' : Function.Injective (algebraMap O O'))
    {f : MvPolynomial (Σ k, J k) O'} (hf : f ∈ pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) :
    ∃ (r : ℕ) (e : Fin r → O') (g : Fin r → MvPolynomial (Σ k, J k) O),
      (∀ i, g i ∈ pointIdeal O y) ∧
        f = ∑ i, C (e i) * MvPolynomial.map (algebraMap O O') (g i) := by
  obtain ⟨r, e, g, hli, hfe⟩ := exists_decomp hOO' f
  refine ⟨r, e, g, ?_, hfe⟩
  have hLI := linearIndependent_base hcl hinj hli
  have h0 : pointConeMap O' (fun v => algebraMap Ω Ω' (y v)) f = 0 := hf
  have hz : ∑ i, (C (algebraMap O' Ω' (e i)) : MvPolynomial K Ω') *
      MvPolynomial.map (algebraMap Ω Ω') (pointConeMap O y (g i)) = 0 := by
    rw [hfe, map_sum] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, pointConeMap_map]
    congr 1
    simp [pointConeMap, MvPolynomial.algebraMap_apply]
  intro i
  change pointConeMap O y (g i) = 0
  ext n
  have hn := congrArg (coeff n) hz
  simp only [coeff_sum, coeff_C_mul, coeff_map, coeff_zero] at hn
  have := Fintype.linearIndependent_iff.1 hLI (fun i => coeff n (pointConeMap O y (g i)))
    (by simpa [Algebra.smul_def, mul_comm] using hn) i
  simpa using this

theorem pointIdeal_eq_map (hcl : IsIntegrallyClosedIn O Ω)
    (hinj : Function.Injective (algebraMap O' Ω')) (hOO' : Function.Injective (algebraMap O O')) :
    pointIdeal O' (fun v => algebraMap Ω Ω' (y v)) =
      (pointIdeal O y).map (MvPolynomial.map (algebraMap O O')) := by
  refine le_antisymm (fun f hf => ?_) (map_le_pointIdeal y)
  obtain ⟨r, e, g, hg, rfl⟩ := exists_decomp_mem y hcl hinj hOO' hf
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hg i))

variable [DecidableEq K]

theorem isMultiHomogIdeal_pointIdeal (hcl : IsIntegrallyClosedIn O Ω)
    (hinj : Function.Injective (algebraMap O' Ω')) (hOO' : Function.Injective (algebraMap O O'))
    (hP : IsMultiHomogIdeal (pointIdeal O y)) :
    IsMultiHomogIdeal (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) := by
  classical
  intro f hf b
  obtain ⟨r, e, g, hg, rfl⟩ := exists_decomp_mem y hcl hinj hOO' hf
  have hcomp : weightedHomogeneousComponent (blockWeight J) b
      (∑ i, C (e i) * MvPolynomial.map (algebraMap O O') (g i)) =
      ∑ i, C (e i) * MvPolynomial.map (algebraMap O O')
        (weightedHomogeneousComponent (blockWeight J) b (g i)) := by
    ext m
    simp only [coeff_weightedHomogeneousComponent, coeff_sum, coeff_C_mul, coeff_map]
    split_ifs <;> simp
  rw [hcomp]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _
    (map_le_pointIdeal y (Ideal.mem_map_of_mem _ (hP _ (hg i) b)))

end Main

end Rings

end

end GlobalTheory.CompanionTheory.Ar.Num.BaseChange

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

theorem GlobalTheory.CompanionTheory.Ar.Num.model_baseChange_algebraic : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [CharZero Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d → IsIntegrallyClosedIn O Ω → ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Algebra.IsAlgebraic O O'] (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra O' Ω'] [Algebra O Ω'] [IsScalarTower O O' Ω'] [IsScalarTower O Ω Ω'], Function.Injective (algebraMap O' Ω') → pointIdeal O' (fun v => algebraMap Ω Ω' (y v)) = (pointIdeal O y).map (MvPolynomial.map (algebraMap O O')) ∧ IsModelOver (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d := by
  intro O _ _ _ Ω _ _ _ K _ _ J _ y d hM hcl O' _ _ _ _ _ _ Ω' _ _ _ _ _ _ hinj
  haveI := hcl
  have hOΩ : Function.Injective (algebraMap O Ω) := IsIntegralClosure.algebraMap_injective O O Ω
  have hOO' : Function.Injective (algebraMap O O') := by
    intro a b h
    apply hOΩ
    apply (algebraMap Ω Ω').injective
    rw [← IsScalarTower.algebraMap_apply O Ω Ω', ← IsScalarTower.algebraMap_apply O Ω Ω',
      IsScalarTower.algebraMap_apply O O' Ω', IsScalarTower.algebraMap_apply O O' Ω' b, h]
  refine ⟨BaseChange.pointIdeal_eq_map y hcl hinj hOO', ?_⟩
  have hcomap := BaseChange.comap_pointIdeal (O := O) (O' := O') (Ω' := Ω') y
  have hC' := BaseChange.comap_C_pointIdeal_eq_bot (O' := O') (Ω' := Ω') y hinj
  have hprime : (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))).IsPrime :=
    RingHom.ker_isPrime _
  have hmp : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiProjPrime
      (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) := by
    refine ⟨hprime, BaseChange.isMultiHomogIdeal_pointIdeal y hcl hinj hOO' hM.multiProj.multiHomog, ?_⟩
    intro k
    obtain ⟨i, hi⟩ := hM.multiProj.relevant k
    refine ⟨i, fun h => hi ?_⟩
    rw [← hcomap]
    exact Ideal.mem_comap.2 (by rwa [map_X])
  haveI := hM.multiProj.isPrime
  have htr := BaseChange.trdeg_eq hOO' hcomap hM.noTorsion hC'
  have hd := GroundTheory.Heights₂.Heights.NumbersDVR.DvrConeDimTrdeg.proof O K J _ hM.multiProj hM.noTorsion
  have hd' := GroundTheory.Heights₂.Heights.NumbersDVR.DvrConeDimTrdeg.proof O' K J _ hmp hC'
  refine ⟨hmp, hC', ?_⟩
  rw [← hM.dim, hd, hd', htr]
end

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_over_dvr_extension : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [CharZero Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d → IsIntegrallyClosedIn O Ω → ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Algebra.IsAlgebraic O O'] (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra O' Ω'] [Algebra O Ω'] [IsScalarTower O O' Ω'] [IsScalarTower O Ω Ω'], Function.Injective (algebraMap O' Ω') → pointIdeal O' (fun v => algebraMap Ω Ω' (y v)) = (pointIdeal O y).map (MvPolynomial.map (algebraMap O O')) ∧ IsModelOver (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Num.model_baseChange_algebraic
end

section
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num.ModelDescentAlt

noncomputable section

open GroundTheory.Heights₂.Heights.NumbersDVR (classList classNum cycEval ratDiv IsVerticalDivisor pairNum psumExpansion isHomogeneous_psumExpansion)

variable {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
  {K : Type} [Fintype K] [DecidableEq K] {J : K → Type} [∀ k, Fintype (J k)]

def Scales (P : Ideal (MvPolynomial (Σ k, J k) O)) (P' : Ideal (MvPolynomial (Σ k, J k) O')) (d e : ℕ) : Prop :=
  ∀ (a : K → ℕ) (f : MvPolynomial (Σ k, J k) O), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f a → f ∉ P →
    ∀ l : List (K → ℤ), l.length = d →
      cycList (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P' (MvPolynomial.map (algebraMap O O') f)) l = e * cycList (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P f) l

theorem support_divCycle_finite {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (P : Ideal (MvPolynomial (Σ k, J k) R))
    (f : MvPolynomial (Σ k, J k) R) : (Function.support (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P f)).Finite := by
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {f})).subset ?_
  intro W hW
  by_contra h
  apply hW
  simp [GroundTheory.Heights₂.Heights.NumbersDVR.divCycle, h]

theorem length_classList {σ : Type} (cls : σ → K → ℤ) (μ : σ →₀ ℕ) {m : ℕ} {H : MvPolynomial σ ℝ}
    (hH : H.IsHomogeneous m) (hμ : μ ∈ H.support) : (classList cls μ).length = m := by
  have h := hH (mem_support_iff.mp hμ)
  simp only [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset]
  rw [← h]
  simp [Finsupp.weight_apply, Finsupp.sum]

theorem cycNum_scale {P : Ideal (MvPolynomial (Σ k, J k) O)} {P' : Ideal (MvPolynomial (Σ k, J k) O')} {d e : ℕ} (hs : Scales P P' d e)
    {a : K → ℕ} {f : MvPolynomial (Σ k, J k) O} (hf : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f a) (hfP : f ∉ P)
    {σ : Type} (cls : σ → K → ℤ) {H : MvPolynomial σ ℝ} {m : ℕ} (hH : H.IsHomogeneous m)
    (Q : List (K → ℤ)) (hQ : m + Q.length = d) :
    cycNum (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P' (MvPolynomial.map (algebraMap O O') f)) cls H Q =
      e * cycNum (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P f) cls H Q := by
  unfold cycNum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [hs a f hf hfP _ (by rw [List.length_append, length_classList cls μ hH hμ, hQ])]
  push_cast
  ring

theorem cycEval_scale {P : Ideal (MvPolynomial (Σ k, J k) O)} {P' : Ideal (MvPolynomial (Σ k, J k) O')} {d e : ℕ} (hs : Scales P P' d e)
    {a : K → ℕ} {f : MvPolynomial (Σ k, J k) O} (hf : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f a) (hfP : f ∉ P)
    {σ : Type} (cls : σ → K → ℤ) {H : MvPolynomial σ ℤ} {m : ℕ} (hH : H.IsHomogeneous m)
    (Q : List (K → ℤ)) (hQ : m + Q.length = d) :
    cycEval (fun W => classNum cls H Q W) (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P' (MvPolynomial.map (algebraMap O O') f)) =
      e * cycEval (fun W => classNum cls H Q W) (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P f) := by
  have h1 := (cycNum_int_and_comb O K J σ cls Q).1 (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P f) (support_divCycle_finite P f) H
  have h2 := (cycNum_int_and_comb O' K J σ cls Q).1 _
    (support_divCycle_finite P' (MvPolynomial.map (algebraMap O O') f)) H
  have hH' : (MvPolynomial.map (Int.castRingHom ℝ) H).IsHomogeneous m := hH.map _
  have h3 := cycNum_scale hs hf hfP cls hH' Q hQ
  rw [h1, h2] at h3
  exact_mod_cast h3

theorem cycEval_ratDiv {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (n : Ideal (MvPolynomial (Σ k, J k) R) → ℤ) (P : Ideal (MvPolynomial (Σ k, J k) R)) (f g : MvPolynomial (Σ k, J k) R) :
    cycEval n (ratDiv P f g) = cycEval n (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P f) - cycEval n (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P g) := by
  unfold cycEval ratDiv
  simp only [sub_mul]
  refine finsum_sub_distrib ?_ ?_
  · exact (support_divCycle_finite P f).subset fun W hW h => hW (by simp [show GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P f W = 0 from h])
  · exact (support_divCycle_finite P g).subset fun W hW h => hW (by simp [show GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P g W = 0 from h])

theorem ck_scale {P : Ideal (MvPolynomial (Σ k, J k) O)} {P' : Ideal (MvPolynomial (Σ k, J k) O')} {d e : ℕ} (hs : Scales P P' d e) {ϖ : O}
    {r : ℕ} (T : LocPair J O (Fin r)) (hT : T.IsVert P ϖ) {k : ℕ} (hk : 1 ≤ k) (Q : List (K → ℤ))
    (hQ : Q.length + k = d + 1) :
    (T.map (algebraMap O O')).ck P' k Q = e * T.ck P k Q := by
  unfold LocPair.ck pairNum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨⟨bf, bg, hf, hg, -⟩, hfP, hgP, -, -⟩ := hT i
  have hm : k - 1 + Q.length = d := by omega
  have hH := isHomogeneous_psumExpansion r k i
  show cycEval _ (ratDiv P' (MvPolynomial.map (algebraMap O O') (T.f i))
    (MvPolynomial.map (algebraMap O O') (T.g i))) = _
  rw [cycEval_ratDiv, cycEval_ratDiv, mul_sub]
  exact congrArg₂ _ (cycEval_scale hs hf hfP _ hH Q hm) (cycEval_scale hs hg hgP _ hH Q hm)

theorem laNum_scale {P : Ideal (MvPolynomial (Σ k, J k) O)} {P' : Ideal (MvPolynomial (Σ k, J k) O')} {d e : ℕ} (hs : Scales P P' d e)
    {p : ℕ} (hp : (C (p : O) : MvPolynomial (Σ k, J k) O) ∉ P) {r : ℕ} (x : Fin r → K → ℤ) {k : ℕ} (hk : 1 ≤ k)
    (Q : List (K → ℤ)) (hQ : Q.length + k = d + 1) :
    laNum P' (p : O') x k Q = e * laNum P (p : O) x k Q := by
  unfold laNum
  have hc : (C (p : O') : MvPolynomial (Σ k, J k) O') = MvPolynomial.map (algebraMap O O') (C (p : O)) := by simp
  have hH : (MvPolynomial.psum (Fin r) ℤ (k - 1)).IsHomogeneous (k - 1) := by
    unfold MvPolynomial.psum
    exact IsHomogeneous.sum _ _ _ fun i _ => by simpa using (isHomogeneous_X ℤ i).pow (k - 1)
  have hC : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (C (p : O) : MvPolynomial (Σ k, J k) O) (0 : K → ℕ) :=
    isWeightedHomogeneous_C _ _
  rw [hc, cycEval_scale hs hC hp x hH Q (by omega)]
  ring

theorem isHomogeneous_liePs {Ψ : Type} {N : ℕ} (j m : ℕ) (τ : Ψ ⊕ Ψ) :
    (liePs (N := N) j m τ : MvPolynomial (Ψ × Fin N) ℝ).IsHomogeneous m := by
  rcases τ with τ | τ
  · exact IsHomogeneous.sum _ _ _ fun i _ => by simpa using (isHomogeneous_X ℝ (τ, i)).pow m
  · exact IsHomogeneous.sum _ _ _ fun i _ => by simpa using ((isHomogeneous_X ℝ (τ, i)).neg).pow m

theorem isHomogeneous_bracket {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ))
    (p k : ℕ) (τ : Ψ) : (bracket (N := N) j φ p k τ).IsHomogeneous (k - 1) := by
  unfold bracket
  have h : (∑ τ', C (GroundTheory.Heights₂.Heights.ModelLeaves.co φ p k (Sum.inl τ) τ') *
      (liePs (N := N) j (k - 1) τ' : MvPolynomial (Ψ × Fin N) ℝ)).IsHomogeneous (k - 1) :=
    IsHomogeneous.sum _ _ _ fun τ' _ => by
      simpa using (isHomogeneous_C _ _).mul (isHomogeneous_liePs j (k - 1) τ')
  have h2 := (isHomogeneous_C (Ψ × Fin N) (k : ℝ)).mul h
  rwa [zero_add] at h2

end

end GlobalTheory.CompanionTheory.Ar.Num.ModelDescentAlt

namespace GlobalTheory.CompanionTheory.Ar.Num.ModelDescentAlt

noncomputable section

open GroundTheory.Heights₂.Heights.NumbersDVR (classList classNum cycEval ratDiv IsVerticalDivisor pairNum psumExpansion isHomogeneous_psumExpansion)

variable {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
  {K : Type} [Fintype K] [DecidableEq K] {J : K → Type} [∀ k, Fintype (J k)]

theorem flag_descends {P : Ideal (MvPolynomial (Σ k, J k) O)} {P' : Ideal (MvPolynomial (Σ k, J k) O')} {d e : ℕ}
    (hs : Scales P P' d e) (he : 0 < e) {ϖ : O} {p : ℕ} (hp : (C (p : O) : MvPolynomial (Σ k, J k) O) ∉ P)
    {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ))
    (T : LocPair J O (Ψ × Fin N)) (hT : T.IsVert P ϖ)
    (h : FlagChernComparison P' d p j φ (T.map (algebraMap O O'))) : FlagChernComparison P d p j φ T := by
  intro τ k hk Q hQ
  have h0 := h τ k hk Q hQ
  have e1 : ((T.map (algebraMap O O')).comp fun i : Fin N => (τ, i)) =
      (T.comp fun i : Fin N => (τ, i)).map (algebraMap O O') := rfl
  have hTc : (T.comp fun i : Fin N => (τ, i)).IsVert P ϖ := fun i => hT (τ, i)
  have hc : (C (p : O') : MvPolynomial (Σ k, J k) O') = MvPolynomial.map (algebraMap O O') (C (p : O)) := by simp
  have hC : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (C (p : O) : MvPolynomial (Σ k, J k) O) (0 : K → ℕ) :=
    isWeightedHomogeneous_C _ _
  rw [e1, ck_scale hs _ hTc hk Q hQ, show (T.map (algebraMap O O')).x = T.x from rfl, hc,
    cycNum_scale hs hC hp T.x (isHomogeneous_bracket j φ p k τ) Q (by omega)] at h0
  have he' : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.2 he.ne'
  push_cast at h0
  exact mul_left_cancel₀ he' h0

theorem whole_descends {P : Ideal (MvPolynomial (Σ k, J k) O)} {P' : Ideal (MvPolynomial (Σ k, J k) O')} {d e : ℕ}
    (hs : Scales P P' d e) (he : 0 < e) {ϖ : O} {p : ℕ}
    (hp : p ≠ 0 → (C (p : O) : MvPolynomial (Σ k, J k) O) ∉ P) {r s : ℕ}
    (lie : LocPair J O (Fin r)) (om : LocPair J O (Fin s)) (hl : lie.IsVert P ϖ) (ho : om.IsVert P ϖ)
    (h : BundleChernComparison P' d p (lie.map (algebraMap O O')) (om.map (algebraMap O O'))) : BundleChernComparison P d p lie om := by
  intro k hk Q hQ
  have h0 := h k hk Q hQ
  have he' : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.2 he.ne'
  rw [ck_scale hs _ hl hk Q hQ, ck_scale hs _ ho hk Q hQ] at h0
  by_cases hp0 : p = 0
  · subst hp0
    have hz : (1 / (((0 : ℕ) : ℝ) ^ k - 1) - 1 / (((0 : ℕ) : ℝ) - 1)) = 0 := by
      have : k ≠ 0 := by omega
      simp [this]
    rw [hz, zero_mul] at h0 ⊢
    push_cast at h0
    have h1 : (e : ℝ) * (((lie.ck P k Q : ℤ) : ℝ) + ((om.ck P k Q : ℤ) : ℝ)) = 0 := by linarith
    exact (mul_eq_zero.1 h1).resolve_left he'
  · rw [show (lie.map (algebraMap O O')).x = lie.x from rfl, laNum_scale hs (hp hp0) lie.x hk Q hQ] at h0
    push_cast at h0
    refine mul_left_cancel₀ he' ?_
    linarith

end

end GlobalTheory.CompanionTheory.Ar.Num.ModelDescentAlt

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem model_descends_from_dvr_ext : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [CharZero Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d → IsIntegrallyClosedIn O Ω → ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Algebra.IsAlgebraic O O'] (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra O' Ω'] [Algebra O Ω'] [IsScalarTower O O' Ω'] [IsScalarTower O Ω Ω'], Function.Injective (algebraMap O' Ω') → ∀ (ϖ : O), Irreducible ϖ → ∀ p : ℕ, (p ≠ 0 → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (T : LocPair J O (Ψ × Fin N)), T.IsVert (pointIdeal O y) ϖ → FlagChernComparison (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d p j φ (T.map (algebraMap O O')) → FlagChernComparison (pointIdeal O y) d p j φ T) ∧ ∀ (r s : ℕ) (lie : LocPair J O (Fin r)) (om : LocPair J O (Fin s)), lie.IsVert (pointIdeal O y) ϖ → om.IsVert (pointIdeal O y) ϖ → BundleChernComparison (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d p (lie.map (algebraMap O O')) (om.map (algebraMap O O')) → BundleChernComparison (pointIdeal O y) d p lie om := by
  intro O _ _ _ Ω _ _ _ K _ _ J _ y d hM hI O' _ _ _ _ _ _ Ω' _ _ _ _ _ _ hinj ϖ hϖ p
  obtain ⟨hEq, hM'⟩ := GlobalTheory.T.model_over_dvr_extension O Ω K J y d hM hI O' Ω' hinj
  have hCmem : ∀ a : O, (C a : MvPolynomial (Σ k, J k) O) ∈ pointIdeal O y → a = 0 := fun a ha => by
    have h' : a ∈ (pointIdeal O y).comap (C : O →+* MvPolynomial (Σ k, J k) O) := ha
    rw [hM.noTorsion] at h'
    simpa using h'
  have hΩ : Function.Injective (algebraMap O Ω) := by
    refine (injective_iff_map_eq_zero _).2 fun a ha => hCmem a ?_
    show GroundTheory.Heights₂.Heights.NumbersDVR.pointConeMap O y (C a) = 0
    simp [GroundTheory.Heights₂.Heights.NumbersDVR.pointConeMap, ha]
  have hOO : Function.Injective (algebraMap O O') := by
    have h2 : Function.Injective (algebraMap O' Ω' ∘ algebraMap O O') := by
      have e : (algebraMap O' Ω' ∘ algebraMap O O' : O → Ω') = algebraMap Ω Ω' ∘ algebraMap O Ω := by
        funext a
        simp only [Function.comp]
        rw [← IsScalarTower.algebraMap_apply O O' Ω', ← IsScalarTower.algebraMap_apply O Ω Ω']
      rw [e]
      exact (algebraMap Ω Ω').injective.comp hΩ
    exact h2.of_comp
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible O'
  have hne : algebraMap O O' ϖ ≠ 0 := fun h0 => hϖ.ne_zero (hOO (by simpa using h0))
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne hϖ'
  have hrel : algebraMap O O' ϖ = ((u⁻¹ : O'ˣ) : O') * ϖ' ^ e := by
    rw [← hu]
    simp [mul_comm]
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · exfalso
      have hU : IsUnit (algebraMap O O' ϖ) := by
        rw [hrel]
        simp
      exact hϖ.not_isUnit ((isUnit_map_iff (algebraMap O O') ϖ).1 hU)
    · exact h
  have hs : ModelDescentAlt.Scales (pointIdeal O y) ((pointIdeal O y).map (MvPolynomial.map (algebraMap O O'))) d e :=
    fun a f hf hfP l hl => GlobalTheory.T.model_over_ramified_extension O O' ϖ ϖ' u⁻¹ e hϖ hϖ' he hrel K J (pointIdeal O y) d hM (hEq ▸ hM') a f hf hfP l hl
  have hp : p ≠ 0 → (C (p : O) : MvPolynomial (Σ k, J k) O) ∉ pointIdeal O y := fun h0 hmem => by
    have h1 := hCmem _ hmem
    have h2 : ((p : ℕ) : Ω) = 0 := by
      have := congrArg (algebraMap O Ω) h1
      simpa using this
    exact h0 (by exact_mod_cast h2)
  rw [hEq]
  exact ⟨fun h0 Ψ _ _ N j φ T hT h => ModelDescentAlt.flag_descends hs he (hp h0) j φ T hT h,
    fun r s lie om hl ho h => ModelDescentAlt.whole_descends hs he hp lie om hl ho h⟩

end GlobalTheory.CompanionTheory.Ar.Num
end

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_descent_integral_closure : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [CharZero Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d → IsIntegrallyClosedIn O Ω → ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Algebra.IsAlgebraic O O'] (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra O' Ω'] [Algebra O Ω'] [IsScalarTower O O' Ω'] [IsScalarTower O Ω Ω'], Function.Injective (algebraMap O' Ω') → ∀ (ϖ : O), Irreducible ϖ → ∀ p : ℕ, (p ≠ 0 → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (T : LocPair J O (Ψ × Fin N)), T.IsVert (pointIdeal O y) ϖ → FlagChernComparison (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d p j φ (T.map (algebraMap O O')) → FlagChernComparison (pointIdeal O y) d p j φ T) ∧ ∀ (r s : ℕ) (lie : LocPair J O (Fin r)) (om : LocPair J O (Fin s)), lie.IsVert (pointIdeal O y) ϖ → om.IsVert (pointIdeal O y) ϖ → BundleChernComparison (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d p (lie.map (algebraMap O O')) (om.map (algebraMap O O')) → BundleChernComparison (pointIdeal O y) d p lie om := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Num.model_descends_from_dvr_ext
end
