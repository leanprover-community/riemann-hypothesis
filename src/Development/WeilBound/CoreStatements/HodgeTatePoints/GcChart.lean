import Mathlib
import Development.WeilBound.CoreStatements.HodgeTatePoints.GcIncl
import Development.WeilBound.CoreStatements.HodgeTatePoints.GcDescend
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor

section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace PositivityTheory.HtPt.Gc

theorem isLocalizedModule_subtype {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω]
    [IsScalarTower A K Ω] (M : Submodule A Ω) (hM : Submodule.span K (M : Set Ω) = ⊤) :
    IsLocalizedModule (nonZeroDivisors A) M.subtype := by
  refine ⟨fun x => ?_, fun y => ?_, fun {x₁ x₂} h => ⟨1, by rw [one_smul, one_smul]; exact Subtype.ext h⟩⟩
  · have hx : algebraMap A K (x : A) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors x.2
    rw [Module.End.isUnit_iff]
    constructor
    · intro v w hvw
      have h' : (x : A) • v = (x : A) • w := by
        simpa [Module.algebraMap_end_apply] using hvw
      rw [← algebraMap_smul K (x : A) v, ← algebraMap_smul K (x : A) w] at h'
      exact smul_right_injective Ω hx h'
    · intro v
      refine ⟨(algebraMap A K (x : A))⁻¹ • v, ?_⟩
      rw [Module.algebraMap_end_apply, ← algebraMap_smul K (x : A), smul_smul,
        mul_inv_cancel₀ hx, one_smul]
  · have hy : y ∈ Submodule.span K (M : Set Ω) := hM ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem z hz => exact ⟨(⟨z, hz⟩, 1), by simp⟩
    | zero => exact ⟨(0, 1), by simp⟩
    | add y₁ y₂ _ _ h₁ h₂ =>
      obtain ⟨⟨m₁, s₁⟩, e₁⟩ := h₁
      obtain ⟨⟨m₂, s₂⟩, e₂⟩ := h₂
      refine ⟨((s₂ : A) • m₁ + (s₁ : A) • m₂, s₁ * s₂), ?_⟩
      have e₁' : (s₁ : A) • y₁ = (m₁ : Ω) := e₁
      have e₂' : (s₂ : A) • y₂ = (m₂ : Ω) := e₂
      simp only [map_add, map_smul, Submodule.subtype_apply, ← e₁', ← e₂', Submonoid.smul_def,
        Submonoid.coe_mul]
      rw [smul_add, mul_smul, mul_comm, mul_smul, smul_comm (s₂ : A) (s₁ : A) y₁,
        smul_comm (s₂ : A) (s₁ : A) y₂]
    | smul c z _ h =>
      obtain ⟨⟨m, s⟩, e⟩ := h
      obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors A) c
      dsimp only at hab
      have e' : (s : A) • z = (m : Ω) := e
      have hb : (b : A) • (c • z) = a • z := by
        rw [← algebraMap_smul K (b : A), smul_smul, mul_comm _ c, hab, algebraMap_smul]
      refine ⟨(a • m, b * s), ?_⟩
      rw [map_smul, Submodule.subtype_apply, ← e', Submonoid.smul_def, Submonoid.coe_mul,
        mul_comm, mul_smul, hb]
      exact smul_comm _ _ _

theorem finrank_lattice {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω]
    [IsScalarTower A K Ω] (M : Submodule A Ω) (hM : Submodule.span K (M : Set Ω) = ⊤) :
    finrank K Ω = finrank A M := by
  haveI := isLocalizedModule_subtype M hM
  rw [IsFractionRing.finrank_right_eq A K Ω]
  exact IsLocalizedModule.finrank_eq (nonZeroDivisors A) M.subtype le_rfl

private theorem rankAtStalk_eq_finrank' {R : Type} [CommRing R] [IsDomain R] {P : Type} [AddCommGroup P]
    [Module R P] (q : PrimeSpectrum R) : Module.rankAtStalk P q = Module.finrank R P := by
  unfold Module.rankAtStalk
  rw [IsLocalization.finrank_eq (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl
    q.asIdeal.primeCompl_le_nonZeroDivisors]
  exact IsLocalizedModule.finrank_eq q.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap q.asIdeal.primeCompl P) q.asIdeal.primeCompl_le_nonZeroDivisors

theorem bc_iso : ∀ (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (M : Submodule A Ω) (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [Algebra A O] (Ω' : Type) [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω'] (L : Submodule O Ω') (ι : M →ₛₗ[algebraMap A O] Ω'), M.IsLattice K → Module.Projective A M → L.IsLattice C → Submodule.span O (Set.range ι) = L → Module.finrank K Ω = Module.finrank C Ω' → ∃ j : O ⊗[A] M →ₗ[O] Ω', Function.Injective j ∧ LinearMap.range j = L ∧ ∀ x, j (1 ⊗ₜ x) = ι x := by
  intro A K _ _ _ _ _ Ω _ _ _ _ M C _ v O _ _ hv _ Ω' _ _ _ _ L ι hM hproj hL hspan hdim
  haveI : IsDomain O := hv.hom_inj.isDomain
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : IsFractionRing O C := hv.isFractionRing
  haveI : Module.Finite A M := Module.Finite.iff_fg.mpr hM.1
  haveI : Module.Finite O L := Module.Finite.iff_fg.mpr hL.1
  haveI : Module.Flat O L := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro x ⟨a, ha⟩
    rw [Submodule.mem_bot]
    have ha' : (a : O) • (x : Ω') = 0 := by
      have := congrArg Subtype.val ha
      simpa [Submonoid.smul_def] using this
    rw [← algebraMap_smul C (a : O)] at ha'
    have hne : algebraMap O C (a : O) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2
    exact Subtype.ext ((smul_eq_zero.mp ha').resolve_left hne)
  letI : Module A Ω' := Module.compHom Ω' (algebraMap A O)
  haveI : IsScalarTower A O Ω' := ⟨fun a o x => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  let ι' : M →ₗ[A] Ω' :=
    { toFun := ι, map_add' := map_add ι
      map_smul' := fun a x => by rw [LinearMap.map_smulₛₗ]; rfl }
  let j : O ⊗[A] M →ₗ[O] Ω' := ι'.liftBaseChange O
  have hj : ∀ x, j (1 ⊗ₜ x) = ι x := fun x => by
    show (1 : O) • ι x = ι x
    exact one_smul _ _
  have hrange : LinearMap.range j = L := by
    apply le_antisymm
    · rintro _ ⟨t, rfl⟩
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul o x =>
        show o • ι x ∈ L
        exact L.smul_mem o (hspan ▸ Submodule.subset_span ⟨x, rfl⟩)
      | add t₁ t₂ h₁ h₂ => rw [map_add]; exact L.add_mem h₁ h₂
    · rw [← hspan, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact ⟨1 ⊗ₜ x, hj x⟩
  refine ⟨j, ?_, hrange, hj⟩
  let j' : O ⊗[A] M →ₗ[O] L := j.codRestrict L (fun t => hrange ▸ LinearMap.mem_range_self j t)
  have hsurj : Function.Surjective j' := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨t, rfl⟩ := hy
    exact ⟨t, rfl⟩
  have hbij : Function.Bijective j' := by
    apply Module.bijective_of_surjective_of_rankAtStalk_eq hsurj
    intro m _
    rw [Module.rankAtStalk_baseChange, rankAtStalk_eq_finrank', rankAtStalk_eq_finrank', ← finrank_lattice M hM.2, hdim,
      finrank_lattice L hL.2]
  intro t₁ t₂ h
  exact hbij.1 (Subtype.ext h)

end PositivityTheory.HtPt.Gc
end

section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace PositivityTheory.HtPt.Gc

section

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  (D : HTChart A K c p R N Ω)

theorem om'_le : D.om' ≤ D.om := by
  refine sup_le (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨x, rfl⟩
    exact D.h_mem x
  · rintro _ ⟨x, hx, rfl⟩
    exact D.om.smul_mem _ hx

theorem pow_smul_mem {x : Ω} (hx : x ∈ D.om) : ((p : A) ^ R) • x ∈ D.om' :=
  Submodule.mem_sup_right ⟨x, hx, rfl⟩

theorem h_mem_om' (x : Fin N → 𝓞 E) : D.h x ∈ D.om' :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨x, rfl⟩)

theorem ht_mem_span {C O : Type} [Field C] [CommRing O] [Algebra O C] {κ' : O}
    {V Ω' : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
    [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω']
    (φ : A →+* O) (P : HTPoint C O c κ' N V Ω') (ι : D.om →ₛₗ[φ] Ω') (hred : D.ReducesTo φ P ι)
    {t : V} (ht : t ∈ P.T) :
    P.ht t ∈ Submodule.span O (ι '' {x : D.om | (x : Ω) ∈ D.om'}) := by
  classical
  set S := Submodule.span O (ι '' {x : D.om | (x : Ω) ∈ D.om'})
  have hp : ∀ y ∈ P.om, (p ^ R) • y ∈ S := by
    intro y hy
    rw [← hred.span_eq] at hy
    induction hy using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨m, rfl⟩ := hw
      refine Submodule.subset_span ⟨(p ^ R) • m, ?_, map_nsmul ι _ _⟩
      have := pow_smul_mem D m.2
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at this
      exact this
    | zero => simp
    | add a b _ _ ha hb => rw [smul_add]; exact S.add_mem ha hb
    | smul a w _ hw => rw [smul_comm]; exact S.smul_mem a hw
  have hT : P.T ≤ S.comap (P.ht.restrictScalars O) := by
    rw [P.free.2.2, Submodule.span_le]
    rintro _ ⟨⟨i, k⟩, rfl⟩
    obtain ⟨y, hy, he⟩ := hred.ht_eq (Pi.single i (RingOfIntegers.basis E k))
    have h1 : P.tate (Pi.single i (RingOfIntegers.basis E k)) =
        P.ρ (RingOfIntegers.basis E k) (P.t i) := by
      rw [HTPoint.tate, Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · simp
    rw [h1] at he
    change P.ht (P.ρ (RingOfIntegers.basis E k) (P.t i)) ∈ S
    rw [← sub_eq_iff_eq_add.2 he]
    exact S.sub_mem (Submodule.subset_span ⟨_, h_mem_om' D _, rfl⟩) (hp y hy)
  exact hT ht

end

theorem chart_ii : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A), κ ∣ (p : A) ^ R → Module.Projective A D.om' → D.HasTestPoints κ → D.om' ≤ D.om ∧ (∀ x ∈ D.om, κ • x ∈ D.om') := by
  intro A K _ _ _ _ _ _ _ _ E _ _ c hc p R N hp Ω _ _ _ _ D κ hκ hP hT
  refine ⟨om'_le D, fun x hx => ?_⟩
  have hp0 : algebraMap A K ((p : A) ^ R) ≠ 0 := by
    rw [map_pow, map_natCast]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  have hlat : D.om'.IsLattice K := by
    haveI : Module.Finite A D.om := haveI := D.om_lat; Submodule.IsLattice.finite K D.om
    refine ⟨Submodule.FG.of_le D.om_lat.fg (om'_le D), ?_⟩
    rw [eq_top_iff, ← D.om_lat.span_eq_top, Submodule.span_le]
    intro y hy
    have : y = (algebraMap A K ((p : A) ^ R))⁻¹ • (((p : A) ^ R) • y) := by
      rw [← algebraMap_smul K ((p : A) ^ R) y, smul_smul, inv_mul_cancel₀ hp0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (pow_smul_mem D hy))
  refine test_incl A K Ω D.om' _ hlat hP fun q hq h1 => ?_
  by_cases hpq : (p : A) ∈ q
  swap
  · refine ⟨(p : A) ^ R, fun h => hpq (hq.mem_of_pow_mem R h), ?_⟩
    exact pow_smul_mem D (D.om.smul_mem κ hx)
  obtain ⟨C, O, _, _, _, _, _, v, φ, V, Ω', _, _, _, _, _, _, _, _, P, ι, hv, hφ, hcen, hred⟩ :=
    hT q hq h1 hpq
  letI : Algebra A O := φ.toAlgebra
  obtain ⟨j, hj, -, hj1⟩ := bc_iso A K Ω D.om C v O hv Ω' P.om ι D.om_lat D.om_proj P.om_lat
    hred.span_eq hred.rank_eq
  obtain ⟨s, hs, hsx⟩ := test_descend A K C v O hv q D.om (D.om'.comap D.om.subtype)
    (κ • ⟨x, hx⟩) hq h1 hφ hcen (by
      obtain ⟨t, ht, hte⟩ := P.κ_mem (ι ⟨x, hx⟩)
        (hred.span_eq ▸ Submodule.subset_span ⟨_, rfl⟩)
      have h2 := ht_mem_span D φ P ι hred ht
      rw [hte, ← ι.map_smulₛₗ, ← hj1] at h2
      have h3 : Submodule.span O (ι '' {x : D.om | (x : Ω) ∈ D.om'}) =
          (Submodule.span O ((fun y : D.om => (1 : O) ⊗ₜ[A] y) ''
            (D.om'.comap D.om.subtype : Set D.om))).map j := by
        rw [Submodule.map_span, Set.image_image]
        simp only [hj1]
        rfl
      rw [h3] at h2
      obtain ⟨z, hz, hze⟩ := h2
      rwa [← hj hze])
  exact ⟨s, hs, hsx⟩

end PositivityTheory.HtPt.Gc
end
