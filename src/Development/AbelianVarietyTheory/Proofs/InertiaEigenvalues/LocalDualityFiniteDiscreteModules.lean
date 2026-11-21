import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GreenbergWilesTotallyComplex
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFCocIff

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

noncomputable section

open Pointwise

namespace GlobalTheory.SelInf

section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

theorem conj_Ine {A : ValuationSubring Ω} {g σ : G F Ω} (hσ : σ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Ine (F := F) A := by
  have m : ∀ y : Ω, y ∈ g • A ↔ (g⁻¹ : G F Ω) y ∈ A := fun y => by
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  have m' : ∀ y : Ω, (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : G F Ω) y) < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', m, m, map_inv₀,
      map_eq_zero_iff _ (g⁻¹ : G F Ω).injective]
  have c : ∀ x : Ω, (g⁻¹ : G F Ω) (g x) = x := fun x => by
    show (g⁻¹ * g) x = x
    simp
  refine ⟨?_, fun x hx => ?_⟩
  · have h : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h, inv_smul_smul]
  · have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff, m, c]
      exact (A.valuation_le_one_iff x).1 hx
    have h := (m' _).1 (hσ.2 _ hx')
    rw [map_sub, c] at h
    exact h

variable {R R' : Type} [CommRing R] [CommRing R'] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [DiscreteTopology M] {M' : Type} [AddCommGroup M'] [Module R' M'] [TopologicalSpace M'] [DiscreteTopology M']
  {S : Set (HeightOneSpectrum (𝓞 F))} {ρ : Representation R (G F Ω) M} {ρS : Representation R' (GS Ω S) M'}
  (e : M ≃+ M') (he : ∀ g m, e (ρ g m) = ρS (toGS Ω S g) (e m))

include he in

theorem triv_of_mem {σ : G F Ω} (hσ : σ ∈ NS Ω S) (m : M) : ρ σ m = m := by
  apply e.injective
  have : toGS Ω S σ = 1 := (QuotientGroup.eq_one_iff σ).2 hσ
  rw [he, this, map_one]
  rfl

def infZ (z : Z1 ρS) : Z1 ρ :=
  ⟨fun g => e.symm (z.1 (toGS Ω S g)),
    (continuous_of_discreteTopology (f := e.symm)).comp (z.2.1.comp (continuous_toGS Ω S)), fun g h => by
      apply e.injective
      beta_reduce
      rw [map_add, he, map_mul, z.2.2]
      simp⟩

theorem infZ_apply (z : Z1 ρS) (g : G F Ω) : (infZ e he z).1 g = e.symm (z.1 (toGS Ω S g)) := rfl

theorem mk_infZ_eq_iff (z z' : Z1 ρS) :
    (Submodule.Quotient.mk (infZ e he z) : H1 ρ) = Submodule.Quotient.mk (infZ e he z') ↔
      (Submodule.Quotient.mk z : H1 ρS) = Submodule.Quotient.mk z' := by
  rw [Submodule.Quotient.eq, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.mem_comap, mem_coboundaries1, mem_coboundaries1]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨e m, fun g => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g', toGS Ω S g' = g := QuotientGroup.mk'_surjective _ g
    have h1 : e.symm (z.1 (toGS Ω S g)) - e.symm (z'.1 (toGS Ω S g)) = ρ g m - m := hm g
    have h2 := congrArg e h1
    rw [map_sub, map_sub, he, e.apply_symm_apply, e.apply_symm_apply] at h2
    exact h2
  · rintro ⟨m, hm⟩
    refine ⟨e.symm m, fun g => ?_⟩
    have h1 : z.1 (toGS Ω S g) - z'.1 (toGS Ω S g) = ρS (toGS Ω S g) m - m := hm (toGS Ω S g)
    change e.symm (z.1 (toGS Ω S g)) - e.symm (z'.1 (toGS Ω S g)) = _
    apply e.injective
    rw [map_sub, map_sub, he, e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply]
    exact h1

def infH : H1 ρS → H1 ρ := fun x => Submodule.Quotient.mk (infZ e he x.out)

theorem infH_mk (z : Z1 ρS) : infH e he (Submodule.Quotient.mk z) = Submodule.Quotient.mk (infZ e he z) :=
  (mk_infZ_eq_iff e he _ _).2 (Quotient.out_eq' _)

theorem infH_injective : Function.Injective (infH e he) := by
  intro x y h
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [infH_mk, infH_mk] at h
  exact (mk_infZ_eq_iff e he _ _).1 h

theorem Ine_le_NS {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) {A : ValuationSubring Ω} (hA : IsPlaceOver A v)
    {σ : G F Ω} (hσ : σ ∈ Ine (F := F) A) : σ ∈ NS Ω S := by
  apply Subgroup.le_topologicalClosure
  apply Subgroup.subset_normalClosure
  simp only [Set.mem_iUnion]
  exact ⟨v, hv, A, hA, hσ⟩

theorem z_one {Γ : Type} [Group Γ] [TopologicalSpace Γ] {π : Representation R Γ M} (z : Z1 π) : z.1 1 = 0 := by
  have := z.2.2 1 1
  simpa using this

include he in

theorem mem_unrAt_iff {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) {A : ValuationSubring Ω} (hA : IsPlaceOver A v)
    (z : Z1 ρ) :
    resH1 ρ (Dec (F := F) A).subtype continuous_subtype_val (Submodule.Quotient.mk z) ∈ Formalism.GaloisCohomology.unrAt ρ A ↔
      ∀ σ ∈ Ine (F := F) A, z.1 σ = 0 := by
  have h0 : resH1 ρ (Dec (F := F) A).subtype continuous_subtype_val (Submodule.Quotient.mk z) ∈ Formalism.GaloisCohomology.unrAt ρ A ↔
      (Submodule.Quotient.mk (restrictCocycles1 _ ((Ine (F := F) A).subgroupOf (Dec (F := F) A)).subtype continuous_subtype_val
        (restrictCocycles1 ρ (Dec (F := F) A).subtype continuous_subtype_val z)) : H1 _) = 0 := Iff.rfl
  rw [h0, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, mem_coboundaries1]
  constructor
  · rintro ⟨m, hm⟩ σ hσ
    have h1 : z.1 σ = ρ σ m - m := hm ⟨⟨σ, Ine_le_Dec A hσ⟩, hσ⟩
    rw [h1, triv_of_mem e he (Ine_le_NS hv hA hσ), sub_self]
  · intro h
    refine ⟨0, fun g => ?_⟩
    rw [map_zero, sub_zero]
    exact h g.1.1 g.2

include he in

theorem vanish_NS [IsAlgClosure F Ω] (A : Formalism.GaloisCohomology.Places F Ω) (z : Z1 ρ)
    (h : ∀ v ∉ S, ∀ σ ∈ Ine (F := F) (A.1 v), z.1 σ = 0) : ∀ σ ∈ NS Ω S, z.1 σ = 0 := by
  have hz := z.2.2
  have hinv : ∀ g, z.1 g + ρ g (z.1 g⁻¹) = 0 := fun g => by
    rw [← hz, mul_inv_cancel, z_one]
  let K : Subgroup (G F Ω) :=
    { carrier := {g | g ∈ NS Ω S ∧ z.1 g = 0}
      one_mem' := ⟨one_mem _, z_one z⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        exact ⟨mul_mem ha hb, by rw [hz, ha', hb', map_zero, add_zero]⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, ?_⟩
        have := hinv a
        rwa [ha', zero_add, triv_of_mem e he ha] at this }
  have hK : K.Normal := ⟨by
    rintro a ⟨ha, ha'⟩ g
    refine ⟨(normal_NS S).conj_mem a ha g, ?_⟩
    rw [mul_assoc, hz, hz, ha', zero_add, triv_of_mem e he ha, hinv]⟩
  have hc : IsClosed (K : Set (G F Ω)) :=
    (isClosed_NS Ω S).inter ((isClosed_discrete {(0 : M)}).preimage z.2.1)
  have hle : Subgroup.normalClosure
      (⋃ v ∈ Sᶜ, ⋃ A ∈ {A : ValuationSubring (Ω) | IsPlaceOver A v}, Inertia (F := F) A) ≤ K := by
    apply Subgroup.normalClosure_le_normal
    intro τ hτ
    simp only [Set.mem_iUnion] at hτ
    obtain ⟨v, hv, B, hB, hτ⟩ := hτ
    obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) (A.2 v) hB
    have h1 := conj_Ine (F := F) hτ
    have h2 : g⁻¹ * τ * g ∈ K := ⟨Ine_le_NS hv (A.2 v) h1, h v hv _ h1⟩
    have h3 := hK.conj_mem _ h2 g
    have h4 : g * (g⁻¹ * τ * g) * g⁻¹ = τ := by group
    rwa [h4] at h3
  intro σ hσ
  exact (Subgroup.topologicalClosure_minimal _ hle hc hσ).2

theorem exists_infZ (z : Z1 ρ) (h : ∀ σ ∈ NS Ω S, z.1 σ = 0) : ∃ z', infZ e he z' = z := by
  have hz := z.2.2
  have hw : ∀ a b : G F Ω, (QuotientGroup.leftRel (NS Ω S)) a b → e (z.1 a) = e (z.1 b) := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab
    have : z.1 (a * (a⁻¹ * b)) = z.1 a := by rw [hz, h _ hab, map_zero, add_zero]
    rw [← this, mul_inv_cancel_left]
  refine ⟨⟨Quotient.lift (fun g => e (z.1 g)) hw,
    Continuous.quotient_lift ((continuous_of_discreteTopology (f := e)).comp z.2.1) hw, fun g g' => ?_⟩, ?_⟩
  · obtain ⟨g, rfl⟩ : ∃ g', toGS Ω S g' = g := QuotientGroup.mk'_surjective _ g
    obtain ⟨g', rfl⟩ : ∃ g'', toGS Ω S g'' = g' := QuotientGroup.mk'_surjective _ g'
    rw [← map_mul]
    change e (z.1 (g * g')) = e (z.1 g) + ρS (toGS Ω S g) (e (z.1 g'))
    rw [hz, map_add, he]
  · exact Subtype.ext (funext fun g => e.symm_apply_apply (z.1 g))

end

theorem selAll_equiv_sel : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (R R' : Type) [CommRing R] [CommRing R'] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (M' : Type) [AddCommGroup M'] [Module R' M'] [TopologicalSpace M'] [DiscreteTopology M'] (S : Finset (HeightOneSpectrum (𝓞 F))) (A : Formalism.GaloisCohomology.Places F Ω) (ρ : Representation R (G F Ω) M) (ρS : Representation R' (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M') (e : M ≃+ M'), ContAction ρ → (∀ g m, e (ρ g m) = ρS (toGS Ω _ g) (e m)) → ∀ (L : ∀ v, Submodule R (H1 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) (LS : LocCond ρS (locFam S (fun v => A.1 v.1))), (∀ v ∉ S, L v = Formalism.GaloisCohomology.unrAt ρ (A.1 v)) → (∀ (v : S) (z : Z1 (ρ.comp (Dec (F := F) (A.1 v.1)).subtype)) (z' : Z1 (ρS.comp (locFam S (fun v => A.1 v.1) v))), (∀ g, z'.1 g = e (z.1 g)) → (Submodule.Quotient.mk z ∈ L v.1 ↔ Submodule.Quotient.mk z' ∈ LS v)) → Nonempty (Formalism.GaloisCohomology.SelAll ρ A L ≃ Sel ρS (locFam S (fun v => A.1 v.1)) (continuous_locFam S _) LS) := by
  intro F Ω _ _ _ _ _ R R' _ _ M _ _ _ _ M' _ _ _ _ S A ρ ρS e _ he L LS hL hLS
  have key : ∀ (z : Z1 ρS) (v : S),
      resH1 ρ (Dec (F := F) (A.1 v.1)).subtype continuous_subtype_val (Submodule.Quotient.mk (infZ e he z)) ∈ L v.1 ↔
      resH1 ρS (locFam S (fun v => A.1 v.1) v) (continuous_locFam S _ v) (Submodule.Quotient.mk z) ∈ LS v :=
    fun z v => hLS v (restrictCocycles1 ρ (Dec (F := F) (A.1 v.1)).subtype continuous_subtype_val (infZ e he z))
      (restrictCocycles1 ρS (locFam S (fun v => A.1 v.1) v) (continuous_locFam S _ v) z)
      (fun g => (e.apply_symm_apply _).symm)
  have hall : ∀ y : H1 ρ, y ∈ Formalism.GaloisCohomology.SelAll ρ A L ↔
      ∀ v, resH1 ρ (Dec (F := F) (A.1 v)).subtype continuous_subtype_val y ∈ L v :=
    fun y => mem_Sel ρ (fun v => (Dec (F := F) (A.1 v)).subtype) (fun _ => continuous_subtype_val) L y
  have hmem : ∀ x : H1 ρS, x ∈ Sel ρS (locFam S (fun v => A.1 v.1)) (continuous_locFam S _) LS ↔
      infH e he x ∈ Formalism.GaloisCohomology.SelAll ρ A L := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [infH_mk, hall, mem_Sel]
    constructor
    · intro h v
      by_cases hv : v ∈ S
      · exact (key z ⟨v, hv⟩).2 (h ⟨v, hv⟩)
      · rw [hL v hv, mem_unrAt_iff e he (by simpa using hv) (A.2 v)]
        intro σ hσ
        have : toGS Ω (S : Set (HeightOneSpectrum (𝓞 F))) σ = 1 :=
          (QuotientGroup.eq_one_iff σ).2 (Ine_le_NS (by simpa using hv) (A.2 v) hσ)
        rw [infZ_apply, this, z_one, map_zero]
    · intro h v
      exact (key z v).1 (h v.1)
  refine ⟨(Equiv.ofBijective (fun x : Sel ρS (locFam S (fun v => A.1 v.1)) (continuous_locFam S _) LS =>
    (⟨infH e he x.1, (hmem _).1 x.2⟩ : Formalism.GaloisCohomology.SelAll ρ A L)) ⟨?_, ?_⟩).symm⟩
  · intro x y h
    exact Subtype.ext (infH_injective e he (congrArg Subtype.val h))
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hy' := (hall _).1 hy
    obtain ⟨z', rfl⟩ := exists_infZ e he z (vanish_NS e he A z fun v hv => by
      have hv' : v ∉ S := by simpa using hv
      have := hy' v
      rwa [hL v hv', mem_unrAt_iff e he hv (A.2 v)] at this)
    exact ⟨⟨Submodule.Quotient.mk z', (hmem _).2 (by rw [infH_mk]; exact hy)⟩, Subtype.ext (infH_mk e he z')⟩

end GlobalTheory.SelInf
end
end

section
namespace GlobalTheory

theorem finiteField_exists_traceForm_dualBases_pow_one :
    ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k] [CharP k l],
      ∃ t : k →+ ZMod (l ^ 1), (∀ b, (∀ a, t (a * b) = 0) → b = 0) ∧
        ∃ (n : ℕ) (a e : Fin n → k), ∀ z, z = ∑ j, ((t (a j * z)).val : k) * e j := by
  intro l _ k _ _ _
  rw [pow_one]
  let _ : Algebra (ZMod l) k := ZMod.algebra k l
  have hnd := traceForm_nondegenerate (ZMod l) k
  let b := Module.finBasis (ZMod l) k
  let d := (Algebra.traceForm (ZMod l) k).dualBasis hnd b
  refine ⟨(Algebra.trace (ZMod l) k).toAddMonoidHom, ?_, Module.finrank (ZMod l) k, b, d, ?_⟩
  · intro x hx
    apply hnd.1 x
    intro y
    rw [Algebra.traceForm_apply, mul_comm]
    exact hx y
  · intro z
    conv_lhs => rw [← d.sum_repr z]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, mul_comm z (b j)]
    simp only [LinearMap.toAddMonoidHom_coe]
    obtain ⟨c, hc⟩ : ∃ c, Algebra.trace (ZMod l) k (b j * z) = c := ⟨_, rfl⟩
    rw [hc]
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

end GlobalTheory
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual

namespace GlobalTheory.DualPairFormula

section Transport

variable {R R' : Type} [CommRing R] [CommRing R'] {D : Type} [Group D] [TopologicalSpace D]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  {M' : Type} [AddCommGroup M'] [Module R' M'] [TopologicalSpace M'] [DiscreteTopology M']
  (ρ : Representation R D M) (ρ' : Representation R' D M') (e : M ≃+ M')
  (he : ∀ g m, e (ρ g m) = ρ' g (e m))

def cocycleEquiv : Z1 ρ ≃+ Z1 ρ' where
  toFun z := ⟨fun g => e (z.1 g), continuous_of_discreteTopology.comp z.2.1, fun g h => by
    beta_reduce
    rw [z.2.2, map_add, he]⟩
  invFun z := ⟨fun g => e.symm (z.1 g), continuous_of_discreteTopology.comp z.2.1, fun g h => by
    apply e.injective
    rw [map_add, he]
    simp only [AddEquiv.apply_symm_apply]
    exact z.2.2 g h⟩
  left_inv z := Subtype.ext (funext fun g => e.symm_apply_apply _)
  right_inv z := Subtype.ext (funext fun g => e.apply_symm_apply _)
  map_add' z w := Subtype.ext (funext fun g => map_add e _ _)

include he in

theorem exists_H1_equiv_of_equivariant_equiv : ∃ T : H1 ρ ≃+ H1 ρ', ∀ (z : Z1 ρ) (z' : Z1 ρ'),
    (∀ g, z'.1 g = e (z.1 g)) → T (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' := by
  refine ⟨QuotientAddGroup.congr ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup
    ((B1 ρ').comap (Z1 ρ').subtype).toAddSubgroup (cocycleEquiv ρ ρ' e he) ?_, fun z z' h => ?_⟩
  · ext z'
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ _).1 hz
      refine (mem_coboundaries1 ρ' _).2 ⟨e m, fun g => ?_⟩
      change e (z.1 g) = _
      rw [← he, ← map_sub]
      exact congrArg e (hm g)
    · intro hz
      obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ' _).1 hz
      refine ⟨(cocycleEquiv ρ ρ' e he).symm z', (mem_coboundaries1 ρ _).2 ⟨e.symm m, fun g => ?_⟩,
        (cocycleEquiv ρ ρ' e he).apply_symm_apply z'⟩
      apply e.injective
      change e (e.symm (z'.1 g)) = _
      rw [map_sub, he, e.apply_symm_apply, e.apply_symm_apply]
      exact hm g
  · obtain rfl : z' = cocycleEquiv ρ ρ' e he z := Subtype.ext (funext h)
    rfl

end Transport

theorem exists_transport_cond {R : Type} [CommRing R] {n : ℕ} {D : Type} [Group D]
    [TopologicalSpace D] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [DiscreteTopology M] {M' : Type} [AddCommGroup M'] [Module (ZMod n) M'] [TopologicalSpace M']
    [DiscreteTopology M'] (ρ : Representation R D M) (ρ' : Representation (ZMod n) D M')
    (e : M ≃+ M') (he : ∀ g m, e (ρ g m) = ρ' g (e m)) (L : Submodule R (H1 ρ)) :
    ∃ L' : Submodule (ZMod n) (H1 ρ'), Nat.card L' = Nat.card L ∧ ∀ (z : Z1 ρ) (z' : Z1 ρ'),
      (∀ g, z'.1 g = e (z.1 g)) → (Submodule.Quotient.mk z ∈ L ↔ Submodule.Quotient.mk z' ∈ L') := by
  obtain ⟨T, hT⟩ := exists_H1_equiv_of_equivariant_equiv ρ ρ' e he
  refine ⟨AddSubgroup.toZModSubmodule n (L.toAddSubgroup.comap T.symm.toAddMonoidHom), ?_,
    fun z z' h => ?_⟩
  · exact Nat.card_congr (T.symm.toEquiv.subtypeEquiv fun _ => Iff.rfl)
  · rw [← hT z z' h]
    change _ ↔ T.symm (T _) ∈ L
    rw [T.symm_apply_apply]

theorem card_H0_eq_of_equivariant_equiv {R R' : Type} [CommRing R] [CommRing R'] {D D' : Type} [Group D] [Group D']
    {M : Type} [AddCommGroup M] [Module R M] {M' : Type} [AddCommGroup M'] [Module R' M']
    (ρ : Representation R D M) (ρ' : Representation R' D' M') (φ : D → D')
    (hφ : Function.Surjective φ) (e : M ≃+ M') (he : ∀ g m, e (ρ g m) = ρ' (φ g) (e m)) :
    Nat.card (H0 ρ') = Nat.card (H0 ρ) := by
  refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun m => ?_)).symm
  change (∀ g, ρ g m = m) ↔ ∀ g, ρ' g (e m) = e m
  rw [hφ.forall]
  refine forall_congr' fun g => ?_
  rw [← he, e.injective.eq_iff]

theorem exists_dual_equiv {n : ℕ} [NeZero n] {k : Type} [Field k] [Finite k]
    {M : Type} [AddCommGroup M] [Module k M] [Module (ZMod n) M] [Finite M]
    {M' : Type} [AddCommGroup M'] [Module k M'] [Finite M'] (P : M →ₗ[k] M' →ₗ[k] k)
    (h1 : ∀ x, (∀ y, P x y = 0) → x = 0) (h2 : ∀ y, (∀ x, P x y = 0) → y = 0)
    (t : k →+ ZMod n) (ht : ∀ b, (∀ a, t (a * b) = 0) → b = 0) :
    ∃ e : M' ≃+ TDual (ZMod n) M, ∀ y x, e y x = t (P x y) := by
  let f : M' →+ TDual (ZMod n) M := AddMonoidHom.mk'
    (fun y => TDual.mk ((t.comp (P.flip y).toAddMonoidHom).toZModLinearMap n))
    (fun y y' => by ext x; simp)
  have hf : ∀ y x, f y x = t (P x y) := fun _ _ => rfl
  have inj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    refine h2 y fun x => ht _ fun a => ?_
    have := hf y (a • x)
    rw [hy, map_smul P, LinearMap.smul_apply, smul_eq_mul] at this
    exact this.symm
  have c1 : Nat.card (TDual (ZMod n) M) = Nat.card M := GlobalTheory.ZModDual.card_dual_eq n M
  have : Finite (TDual (ZMod n) M) := Nat.finite_of_card_ne_zero (by rw [c1]; exact Nat.card_pos.ne')
  have c2 : Nat.card (Module.Dual k M') = Nat.card M' :=
    Nat.card_congr (Module.finBasis k M').toDualEquiv.symm.toEquiv
  have : Finite (Module.Dual k M') := Nat.finite_of_card_ne_zero (by rw [c2]; exact Nat.card_pos.ne')
  have c3 : Nat.card M ≤ Nat.card M' := by
    rw [← c2]
    refine Nat.card_le_card_of_injective (P : M → Module.Dual k M') ?_
    rw [injective_iff_map_eq_zero]
    exact fun x hx => h1 x fun y => by rw [hx]; rfl
  exact ⟨AddEquiv.ofBijective f (inj.bijective_of_nat_card_le (c1 ▸ c3)), hf⟩

theorem form_val_mul {n : ℕ} [NeZero n] {k : Type} [Field k] (t : k →+ ZMod n) (c : ZMod n) (a : k) :
    t ((c.val : k) * a) = c * t a := by
  rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]

theorem perp_iff {n : ℕ} [NeZero n] {k : Type} [Field k] (ι : ZMod n →+* k)
    {M : Type} [AddCommGroup M] [Module k M] [Module (ZMod n) M] [TopologicalSpace M]
    [DiscreteTopology M] {M' : Type} [AddCommGroup M'] [Module k M'] [TopologicalSpace M']
    [DiscreteTopology M'] {D Γ : Type} [Group D] [TopologicalSpace D] [Group Γ]
    (ρ : Representation k D M) (ρ' : Representation k D M') (P : M →ₗ[k] M' →ₗ[k] k)
    (μ : Γ →* (ZMod n)ˣ) (ρS : Representation (ZMod n) Γ M) (φ : D →* Γ)
    (hρ : ∀ g m, ρ g m = ρS (φ g) m) (hc : ContAction (ρS.comp φ)) (χ : D → k)
    (hχ : ∀ g, χ g = (((μ (φ g) : (ZMod n)ˣ) : ZMod n).val : k))
    (hP : ∀ g x y, P (ρ g x) (ρ' g y) = χ g * P x y)
    (t : k →+ ZMod n) {m : ℕ} (a b : Fin m → k) (hab : ∀ z, z = ∑ j, ((t (a j * z)).val : k) * b j)
    (L : Submodule k (H1 ρ)) (LS : Submodule (ZMod n) (H1 (ρS.comp φ)))
    (hL : ∀ (z : Z1 ρ) (z' : Z1 (ρS.comp φ)), (∀ g, z'.1 g = z.1 g) →
      (Submodule.Quotient.mk z ∈ L ↔ Submodule.Quotient.mk z' ∈ LS))
    (y : Z1 ρ') (y' : Z1 ((twDual μ ρS).comp φ)) (hy : ∀ g x, y'.1 g x = t (P x (y.1 g))) :
    (∀ x ∈ LS, cupH1H1TwistedDual μ ρS φ hc (Submodule.Quotient.mk y') x = 0) ↔
      ∀ x : Z1 ρ, Submodule.Quotient.mk x ∈ L → CupCob χ ρ' P x.1 y.1 := by
  have hι : ∀ c : ZMod n, ι c = (c.val : k) := fun c => by
    conv_lhs => rw [← ZMod.natCast_zmod_val c, map_natCast]
  have ht : ∀ g z, t (χ g * z) = ((μ (φ g) : (ZMod n)ˣ) : ZMod n) * t z := fun g z => by
    rw [hχ, form_val_mul]
  let E := cocycleEquiv ρ (ρS.comp φ) (AddEquiv.refl M) hρ
  have hE : ∀ x g, (E x).1 g = x.1 g := fun _ _ => rfl
  have key : ∀ (x : Z1 ρ) g h, t (P (x.1 (g * h)) (y.1 (g * h))) = t (P (x.1 g) (y.1 g)) +
      t (P (x.1 g) (ρ' g (y.1 h))) + t (P (ρ g (x.1 h)) (y.1 g)) +
      ((μ (φ g) : (ZMod n)ˣ) : ZMod n) * t (P (x.1 h) (y.1 h)) := fun x g h => by
    rw [x.2.2, y.2.2, ← ht, ← hP]
    simp only [map_add, LinearMap.add_apply]
    ring
  have cb : ∀ x : Z1 ρ, Continuous fun g => t (P (x.1 g) (y.1 g)) := fun x =>
    (continuous_of_discreteTopology (f := fun p : M × M' => t (P p.1 p.2))).comp
      (x.2.1.prodMk y.2.1)
  have hcup : ∀ x : Z1 ρ, cupH1H1TwistedDual μ ρS φ hc (Submodule.Quotient.mk y') (Submodule.Quotient.mk (E x)) = 0 ↔
      ∃ c : D → ZMod n, Continuous c ∧ ∀ g h, t (P (x.1 g) (ρ' g (y.1 h))) =
        ((μ (φ g) : (ZMod n)ˣ) : ZMod n) * c h - c (g * h) + c g := fun x => by
    have e0 : cupH1H1TwistedDual μ ρS φ hc (Submodule.Quotient.mk y') (Submodule.Quotient.mk (E x)) = 0 ↔
      ∃ c : D → ZMod n, Continuous c ∧ ∀ g h,
        ((μ (φ g) : (ZMod n)ˣ) : ZMod n) * c h - c (g * h) + c g = t (P (ρ g (x.1 h)) (y.1 g)) := by
      refine (Submodule.Quotient.mk_eq_zero _).trans ((separated_dvr_second_cohomology_mem _ _).trans ?_)
      refine exists_congr fun c => and_congr_right fun _ => ?_
      rw [funext_iff, Prod.forall]
      refine forall_congr' fun g => forall_congr' fun h => ?_
      rw [← hy, hρ]
      exact Iff.rfl
    rw [e0]
    constructor
    · rintro ⟨c, hc1, hc2⟩
      refine ⟨fun g => -c g - t (P (x.1 g) (y.1 g)), hc1.neg.sub (cb x), fun g h => ?_⟩
      linear_combination hc2 g h - key x g h
    · rintro ⟨c, hc1, hc2⟩
      refine ⟨fun g => -c g - t (P (x.1 g) (y.1 g)), hc1.neg.sub (cb x), fun g h => ?_⟩
      linear_combination hc2 g h + key x g h
  constructor
  · intro H x hx
    have H2 := fun j => (hcup (a j • x)).1 (H _ ((hL _ _ (hE _)).1 (by
      rw [Submodule.Quotient.mk_smul]; exact L.smul_mem _ hx)))
    choose c hc1 hc2 using H2
    refine ⟨fun g => ∑ j, ι (c j g) * b j, ?_, fun g h => ?_⟩
    · exact ((IsLocallyConstant.iff_continuous _).2 (continuous_pi hc1)).comp
        (fun w : Fin m → ZMod n => ∑ j, ι (w j) * b j)
    · rw [hab (P (x.1 g) (ρ' g (y.1 h))), Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have e1 := hc2 j g h
      have e2 : P ((a j • x).1 g) (ρ' g (y.1 h)) = a j * P (x.1 g) (ρ' g (y.1 h)) := by
        change P (a j • x.1 g) _ = _
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [e2] at e1
      rw [e1, hχ, ← hι, ← hι, map_add, map_sub, map_mul]
      ring
  · intro H x hx
    induction x using Submodule.Quotient.induction_on with | H x =>
    obtain ⟨x, rfl⟩ := E.surjective x
    obtain ⟨f, hf1, hf2⟩ := H x ((hL _ _ (hE _)).2 hx)
    refine (hcup x).2 ⟨fun g => t (f g), (hf1.comp t).continuous, fun g h => ?_⟩
    rw [hf2, map_add, map_sub, ht]

theorem exists_descent {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R (G F Ω) M) (hρ : ContAction ρ)
    (S : Set (HeightOneSpectrum (𝓞 F)))
    (h : ∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ σ ∈ Ine (F := F) B, ρ σ = 1) :
    ∃ ρS : Representation R (GS Ω S) M, ContAction ρS ∧ ∀ g m, ρ g m = ρS (toGS Ω S g) m := by
  have hk : NS Ω S ≤ MonoidHom.ker ρ := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) ?_
    · intro τ hτ
      simp only [Set.mem_iUnion] at hτ
      obtain ⟨v, hv, A, hA, hτ⟩ := hτ
      exact h v hv A hA τ hτ
    · have : (MonoidHom.ker ρ : Set (G F Ω)) = ⋂ m, {g | ρ g m = m} := by
        ext g
        simp [LinearMap.ext_iff]
      rw [this]
      exact isClosed_iInter fun m =>
        isClosed_eq (hρ.comp (continuous_id.prodMk continuous_const)) continuous_const
  refine ⟨QuotientGroup.lift _ ρ hk, ?_, fun _ _ => rfl⟩
  unfold ReciprocityTheory.Gal.ContAction
  rw [continuous_prod_of_discrete_right]
  intro m
  rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
  exact hρ.comp (continuous_id.prodMk continuous_const)

theorem greenbergWiles_dualPair : PoitouTateTotallyComplex → LocalFiniteness → GlobalFiniteness → GlobalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [TopologicalSpace M] [DiscreteTopology M] [Finite M] (M' : Type) [AddCommGroup M'] [Module k M'] [TopologicalSpace M'] [DiscreteTopology M'] [Finite M'] (ρ : Representation k (G F Ω) M) (ρ' : Representation k (G F Ω) M') (χ : G F Ω → k) (P : M →ₗ[k] M' →ₗ[k] k), ContAction ρ → ContAction ρ' → (∀ g, χ g = (((cycMod F Ω l 1 g : (ZMod (l ^ 1))ˣ) : ZMod (l ^ 1)).val : k)) → (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) → (∀ g x y, P (ρ g x) (ρ' g y) = χ g * P x y) → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (A : Formalism.GaloisCohomology.Places F Ω), ContainsAbove S l → (∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ σ ∈ Ine (F := F) B, ρ σ = 1) → ∀ (L : ∀ v, Submodule k (H1 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) (L' : ∀ v, Submodule k (H1 (ρ'.comp (Dec (F := F) (A.1 v)).subtype))), (∀ v ∉ S, L v = Formalism.GaloisCohomology.unrAt ρ (A.1 v)) → (∀ v ∉ S, L' v = Formalism.GaloisCohomology.unrAt ρ' (A.1 v)) → (∀ v ∈ S, ∀ y : Z1 (ρ'.comp (Dec (F := F) (A.1 v)).subtype), Submodule.Quotient.mk y ∈ L' v ↔ ∀ x : Z1 (ρ.comp (Dec (F := F) (A.1 v)).subtype), Submodule.Quotient.mk x ∈ L v → CupCob (fun g : Dec (F := F) (A.1 v) => χ g.1) (ρ'.comp (Dec (F := F) (A.1 v)).subtype) P x.1 y.1) → Finite (Formalism.GaloisCohomology.SelAll ρ A L) ∧ Finite (Formalism.GaloisCohomology.SelAll ρ' A L') ∧ Nat.card (Formalism.GaloisCohomology.SelAll ρ A L) * Nat.card (H0 ρ') * (∏ v ∈ S, Nat.card (H0 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) * Nat.card M ^ InfinitePlace.nrComplexPlaces F = Nat.card (Formalism.GaloisCohomology.SelAll ρ' A L') * Nat.card (H0 ρ) * ∏ v ∈ S, Nat.card (L v) := by
  intro hPT hLF hGF hEC F Ω _ _ _ _ _ _ l _ k _ _ _ M _ _ _ _ _ M' _ _ _ _ _ ρ ρ' χ P hρ hρ' hχ h1 h2
    hP S A hS hur L L' hL hL' hperp
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨t, ht, m, a, b, hab⟩ := GlobalTheory.finiteField_exists_traceForm_dualBases_pow_one l k
  haveI : Module (ZMod (l ^ 1)) M := AddCommGroup.zmodModule fun x => by
    rw [pow_one, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
  obtain ⟨ρS, hρS, hd⟩ := exists_descent (zmodRep (l ^ 1) ρ) hρ (S : Set _) fun v hv B hB σ hσ => by
    ext x
    change ρ σ x = x
    rw [hur v hv B hB σ hσ]
    rfl
  replace hd : ∀ (g : G F Ω) (x : M), ρ g x = ρS (toGS Ω (S : Set (HeightOneSpectrum (𝓞 F))) g) x := hd
  obtain ⟨μ, hμ⟩ := PoitouTate.exists_lift_cycMod (Ω := Ω) (r := 1) hS
  have hχ' : ∀ g, χ g = (((μ (toGS Ω _ g) : (ZMod (l ^ 1))ˣ) : ZMod (l ^ 1)).val : k) := fun g => by
    rw [hχ, ← hμ]
    rfl
  obtain ⟨e, he⟩ := exists_dual_equiv P h1 h2 t ht
  have hee : ∀ g y, e (ρ' g y) = twDual μ ρS (toGS Ω _ g) (e y) := fun g y => by
    ext x
    rw [twDual_apply, he, he, ← map_inv, ← hd, ← form_val_mul, ← hχ', ← hP,
      ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hex := fun v : S => exists_transport_cond (ρ.comp (Dec (F := F) (A.1 v.1)).subtype)
    (ρS.comp (locFam S (fun v => A.1 v.1) v)) (AddEquiv.refl M) (fun g x => hd g x) (L v.1)
  choose LS hLS1 hLS2 using hex
  obtain ⟨f1, f2, hmain⟩ := GlobalTheory.GWComplex.greenbergWiles_totallyComplex hPT hLF hGF hEC F Ω l 1 M S ρS one_pos hS hρS μ hμ
    (fun v => A.1 v.1) (fun v => A.2 v.1) LS
  obtain ⟨E1⟩ := GlobalTheory.SelInf.selAll_equiv_sel F Ω k (ZMod (l ^ 1)) M M S A ρ ρS (AddEquiv.refl M) hρ hd L LS hL hLS2
  obtain ⟨E2⟩ := GlobalTheory.SelInf.selAll_equiv_sel F Ω k (ZMod (l ^ 1)) M' _ S A ρ' (twDual μ ρS) e hρ' hee L'
    (perpCond μ ρS (locFam S fun v => A.1 v.1) (fun v => hρS.comp' (continuous_locFam S _ v)) LS) hL'
    fun v y y' hy => by
      rw [hperp v.1 v.2 y, mem_perpCond]
      exact (perp_iff (ZMod.castHom (by rw [pow_one]) k) (ρ.comp (Dec (F := F) (A.1 v.1)).subtype)
        (ρ'.comp (Dec (F := F) (A.1 v.1)).subtype) P μ ρS (locFam S (fun v => A.1 v.1) v)
        (fun g x => hd g x) _ (fun g => χ g.1) (fun g => hχ' g) (fun g => hP g) t a b hab (L v.1)
        (LS v) (hLS2 v) y y' (fun g x => by rw [hy, he])).symm
  have hs : Function.Surjective (toGS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) :=
    QuotientGroup.mk'_surjective _
  refine ⟨Finite.of_equiv _ E1.symm, Finite.of_equiv _ E2.symm, ?_⟩
  rw [Nat.card_congr E1, Nat.card_congr E2, ← card_H0_eq_of_equivariant_equiv ρ' _ _ hs e hee,
    ← card_H0_eq_of_equivariant_equiv ρ ρS _ hs (AddEquiv.refl M) hd, ← Finset.prod_coe_sort S, ← Finset.prod_coe_sort S]
  simp only [← hLS1]
  rw [← hmain]
  congr 2
  refine Finset.prod_congr rfl fun v _ => ?_
  exact (card_H0_eq_of_equivariant_equiv (ρ.comp (Dec (F := F) (A.1 v.1)).subtype)
    (ρS.comp (locFam S (fun v => A.1 v.1) v)) id Function.surjective_id (AddEquiv.refl M)
    (fun g x => hd g x)).symm

end GlobalTheory.DualPairFormula
end
end
