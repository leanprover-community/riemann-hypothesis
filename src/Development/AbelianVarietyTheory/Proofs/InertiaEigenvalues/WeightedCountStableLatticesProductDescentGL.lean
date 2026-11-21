import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapInlMemStLat
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraEtaleOfSeparableCharpolyMulLeft
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralClosureFgFiniteEtaleDvr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteUnitOrbitsStableLatticesSeparable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardStableLattices

section
section
open Polynomial

namespace GlobalTheory.OrbitCounting

theorem stabilizer_smul_eq {G X : Type} [CommGroup G] [MulAction G X] (g : G) (x : X) :
    MulAction.stabilizer G (g • x) = MulAction.stabilizer G x := by
  ext h
  simp only [MulAction.mem_stabilizer_iff]
  rw [← mul_smul, mul_comm, mul_smul, smul_left_cancel_iff]

theorem ncard_fibre_inter_orbit {G X Y : Type} [CommGroup G] [MulAction G X] [MulAction G Y]
    (π : X → Y) (hπ : ∀ (g : G) (x : X), π (g • x) = g • π x) (x0 : X) :
    {x | π x = π x0 ∧ x ∈ MulAction.orbit G x0}.ncard =
      (MulAction.stabilizer G x0).relIndex (MulAction.stabilizer G (π x0)) := by
  have hset : {x | π x = π x0 ∧ x ∈ MulAction.orbit G x0} =
      MulAction.orbit (MulAction.stabilizer G (π x0)) x0 := by
    ext x; constructor
    · rintro ⟨hx, g, rfl⟩
      refine ⟨⟨g, ?_⟩, rfl⟩
      rw [MulAction.mem_stabilizer_iff, ← hπ]; exact hx
    · rintro ⟨⟨g, hg⟩, rfl⟩
      refine ⟨?_, ⟨g, rfl⟩⟩
      show π (g • x0) = π x0
      rw [hπ]; exact hg
  rw [hset, Subgroup.relIndex, ← MulAction.index_stabilizer]
  congr 1

theorem counting_principle : ∀ (G X Y : Type) [CommGroup G] [MulAction G X] [MulAction G Y] (Gc : Subgroup G) (π : X → Y), (∀ (g : G) (x : X), π (g • x) = g • π x) → (∀ y, (π ⁻¹' {y}).Finite) → (∀ y : Y, MulAction.stabilizer G y ≤ Gc ∧ (MulAction.stabilizer G y).relIndex Gc ≠ 0) → Finite (MulAction.orbitRel.Quotient G Y) → ∀ w : Y → ℚ, (∀ (g : G) (y : Y), w (g • y) = w y) → ∑ᶠ o : MulAction.orbitRel.Quotient G X, w (π (Quotient.out o)) * ((MulAction.stabilizer G (Quotient.out o)).relIndex Gc : ℚ) = ∑ᶠ o : MulAction.orbitRel.Quotient G Y, w (Quotient.out o) * ((π ⁻¹' {(Quotient.out o)}).ncard : ℚ) * ((MulAction.stabilizer G (Quotient.out o)).relIndex Gc : ℚ) := by
  intro G X Y _ _ _ Gc π hπ hfin hstab hY w hw
  classical
  have hmem : ∀ a b : X, a ∈ MulAction.orbit G b → π a ∈ MulAction.orbit G (π b) := by
    rintro a b ⟨g, rfl⟩; exact ⟨g, (hπ g b).symm⟩
  let q : MulAction.orbitRel.Quotient G X → MulAction.orbitRel.Quotient G Y :=
    Quotient.map π (fun a b h => MulAction.orbitRel_apply.2 (hmem a b (MulAction.orbitRel_apply.1 h)))
  have hq : ∀ x : X, q (Quotient.mk _ x) = Quotient.mk _ (π x) := fun x => rfl

  have hrep : ∀ (oX : MulAction.orbitRel.Quotient G X) (y : Y), q oX = Quotient.mk _ y →
      ∃ x0, π x0 = y ∧ Quotient.mk _ x0 = oX := by
    intro oX y h
    have h1 : q oX = Quotient.mk _ (π (Quotient.out oX)) := by
      rw [← hq, Quotient.out_eq]
    rw [h1] at h
    have h2 : y ∈ MulAction.orbit G (π (Quotient.out oX)) :=
      MulAction.orbitRel_apply.1 (Quotient.exact h.symm)
    obtain ⟨g, hg⟩ := h2
    refine ⟨g • Quotient.out oX, by rw [hπ]; exact hg, ?_⟩
    rw [← Quotient.out_eq oX]
    exact Quotient.sound (MulAction.orbitRel_apply.2 ⟨g, by rw [Quotient.out_eq]⟩)

  let F : X → ℚ := fun x => w (π x) * ((MulAction.stabilizer G x).relIndex Gc : ℚ)
  let H : Y → ℚ := fun y => w y * ((π ⁻¹' {y}).ncard : ℚ) * ((MulAction.stabilizer G y).relIndex Gc : ℚ)
  have hF : ∀ x x' : X, x' ∈ MulAction.orbit G x → F x' = F x := by
    rintro x x' ⟨g, rfl⟩
    simp only [F, hπ, hw, stabilizer_smul_eq]

  haveI : ∀ oY : MulAction.orbitRel.Quotient G Y, Finite ↥(π ⁻¹' {Quotient.out oY}) :=
    fun oY => (hfin _).to_subtype
  haveI hXf : Finite (MulAction.orbitRel.Quotient G X) := by
    refine Finite.of_surjective
      (fun p : (Σ oY : MulAction.orbitRel.Quotient G Y, ↥(π ⁻¹' {Quotient.out oY})) =>
        (Quotient.mk _ (p.2 : X) : MulAction.orbitRel.Quotient G X)) ?_
    intro oX
    obtain ⟨x0, hx0, hx0'⟩ := hrep oX (Quotient.out (q oX)) (Quotient.out_eq _).symm
    exact ⟨⟨q oX, ⟨x0, hx0⟩⟩, hx0'⟩
  haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient G X)
  haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient G Y)
  have hL : ∀ oX : MulAction.orbitRel.Quotient G X,
      w (π (Quotient.out oX)) * ((MulAction.stabilizer G (Quotient.out oX)).relIndex Gc : ℚ) = F (Quotient.out oX) := fun _ => rfl
  have hR : ∀ oY : MulAction.orbitRel.Quotient G Y,
      w (Quotient.out oY) * ((π ⁻¹' {(Quotient.out oY)}).ncard : ℚ) * ((MulAction.stabilizer G (Quotient.out oY)).relIndex Gc : ℚ) = H (Quotient.out oY) := fun _ => rfl
  simp only [hL, hR]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← Finset.sum_fiberwise Finset.univ q]
  refine Finset.sum_congr rfl (fun oY _ => ?_)
  set y := Quotient.out oY with hy
  have hyo : Quotient.mk _ y = oY := Quotient.out_eq oY
  set S := (hfin y).toFinset with hS
  have hcard : (π ⁻¹' {y}).ncard = S.card := Set.ncard_eq_toFinset_card _ (hfin y)
  have hmaps : (S : Set X).MapsTo (fun x => (Quotient.mk _ x : MulAction.orbitRel.Quotient G X))
      (Finset.univ.filter (fun oX => q oX = oY) : Finset _) := by
    intro x hx
    simp only [hS, Set.Finite.coe_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hx
    simp [hq, hx, hyo]
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  show _ = w y * ((π ⁻¹' {y}).ncard : ℚ) * ((MulAction.stabilizer G y).relIndex Gc : ℚ)
  rw [hcard, hsum]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun oX hoX => ?_)
  have hqo : q oX = Quotient.mk _ y := by
    rw [hyo]; simpa using hoX
  obtain ⟨x0, hx0, hx0'⟩ := hrep oX y hqo
  have hout : Quotient.out oX ∈ MulAction.orbit G x0 := by
    apply MulAction.orbitRel_apply.1
    apply Quotient.exact
    rw [Quotient.out_eq, hx0']
  rw [hF x0 _ hout]
  have hfilt : ((S.filter (fun x => (Quotient.mk _ x : MulAction.orbitRel.Quotient G X) = oX) : Finset X) : Set X)
      = {x | π x = π x0 ∧ x ∈ MulAction.orbit G x0} := by
    ext x
    simp only [hS, Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_preimage,
      Set.mem_singleton_iff, Set.mem_setOf_eq, hx0]
    rw [← hx0']
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, MulAction.orbitRel_apply.1 (Quotient.exact h2)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Quotient.sound (MulAction.orbitRel_apply.2 h2)⟩
  rw [← Set.ncard_coe_finset, hfilt, ncard_fibre_inter_orbit π hπ x0]
  have hle1 : MulAction.stabilizer G x0 ≤ MulAction.stabilizer G (π x0) := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff] at hg ⊢
    rw [← hπ, hg]
  rw [hx0] at hle1
  have hle2 : MulAction.stabilizer G y ≤ Gc := (hstab y).1
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hle1 hle2
  simp only [F, hx0]
  rw [← hmul]
  push_cast
  ring

end GlobalTheory.OrbitCounting
end

open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_orbits_counting_principle_finite_fibres : ∀ (G X Y : Type) [CommGroup G] [MulAction G X] [MulAction G Y] (Gc : Subgroup G) (π : X → Y), (∀ (g : G) (x : X), π (g • x) = g • π x) → (∀ y, (π ⁻¹' {y}).Finite) → (∀ y : Y, MulAction.stabilizer G y ≤ Gc ∧ (MulAction.stabilizer G y).relIndex Gc ≠ 0) → Finite (MulAction.orbitRel.Quotient G Y) → ∀ w : Y → ℚ, (∀ (g : G) (y : Y), w (g • y) = w y) → ∑ᶠ o : MulAction.orbitRel.Quotient G X, w (π (Quotient.out o)) * ((MulAction.stabilizer G (Quotient.out o)).relIndex Gc : ℚ) = ∑ᶠ o : MulAction.orbitRel.Quotient G Y, w (Quotient.out o) * ((π ⁻¹' {(Quotient.out o)}).ncard : ℚ) * ((MulAction.stabilizer G (Quotient.out o)).relIndex Gc : ℚ) := by
  atlas_forward_decl GlobalTheory.OrbitCounting.counting_principle
end

section
section
open GlobalTheory.UnitLemma Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma

section Bridge

variable {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A]

theorem stabLat_eq_stabilizer (g : A) (L : stLat O E g) :
    stabLat O (L : Submodule O A) = MulAction.stabilizer Aˣ L := by
  ext t
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff, stLat_smul_val]
  constructor
  · intro h
    ext x
    rw [mem_mulLat_iff]
    have := h (((t⁻¹ : Aˣ) : A) * x)
    rw [← mul_assoc, Units.mul_inv, one_mul] at this
    exact this
  · intro h y
    have := SetLike.ext_iff.mp h ((t : A) * y)
    rw [mem_mulLat_iff, ← mul_assoc, Units.inv_mul, one_mul] at this
    exact this

def orbEquiv (g : A) : Orb O (⊤ : Subgroup Aˣ) (stLat O E g) ≃ MulAction.orbitRel.Quotient Aˣ (stLat O E g) where
  toFun := Quot.lift (fun L => (Quotient.mk _ L : MulAction.orbitRel.Quotient Aˣ (stLat O E g)))
    (by
      rintro L M ⟨t, -, h⟩
      exact (Quotient.sound (show M ∈ MulAction.orbit Aˣ L from ⟨t, Subtype.ext (by rw [stLat_smul_val]; exact h.symm)⟩)).symm)
  invFun := Quotient.lift (fun L => (Quot.mk _ L : Orb O (⊤ : Subgroup Aˣ) (stLat O E g)))
    (by
      rintro a b ⟨t, ht⟩
      exact (Quot.sound ⟨t, Subgroup.mem_top t, by rw [← ht, stLat_smul_val]⟩).symm)
  left_inv := by
    intro o
    induction o using Quot.ind
    rfl
  right_inv := by
    intro o
    induction o using Quotient.inductionOn
    rfl

theorem stabilizer_eq_of_mem_orbit (g : A) {x y : stLat O E g} (h : y ∈ MulAction.orbit Aˣ x) :
    MulAction.stabilizer Aˣ y = MulAction.stabilizer Aˣ x := by
  obtain ⟨t, rfl⟩ := h
  ext s
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, smul_smul, mul_comm, ← smul_smul,
    smul_left_cancel_iff]

theorem countGL_eq_sum_orbits (O E A : Type) [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A]
    (g : A) : countGL O E g = ∑ᶠ o : MulAction.orbitRel.Quotient Aˣ (stLat O E g),
      ((MulAction.stabilizer Aˣ (Quotient.out o)).relIndex (intUnits O A) : ℚ) := by
  change orbSum O ⊤ (stLat O E g) (fun _ => 1) = _
  unfold orbSum
  rw [← finsum_comp_equiv (orbEquiv (O := O) (E := E) g)]
  refine finsum_congr fun o => ?_
  have h1 : (Quotient.mk _ (Quot.out o) : MulAction.orbitRel.Quotient Aˣ (stLat O E g)) = orbEquiv g o := by
    conv_rhs => rw [← Quot.out_eq o]
    rfl
  have h2 := Quotient.out_eq (orbEquiv (O := O) (E := E) g o)
  have h3 := Quotient.exact (h2.trans h1.symm)
  rw [one_mul, inf_top_eq, inf_top_eq, stabLat_eq_stabilizer g (Quot.out o),
    stabilizer_eq_of_mem_orbit g h3]

end Bridge

end GlobalTheory.UnitLemma
end
end

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stableLatticeOrbitCount_eq_sum_orbits : ∀ (O E A : Type) [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A] (g : A), countGL O E g = ∑ᶠ o : MulAction.orbitRel.Quotient Aˣ (stLat O E g), ((MulAction.stabilizer Aˣ (Quotient.out o)).relIndex (intUnits O A) : ℚ) := by
  atlas_forward_decl GlobalTheory.UnitLemma.countGL_eq_sum_orbits
end

section
section
noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial

variable {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A]

theorem isIntegral_of_mul_mem_lat {L : Submodule O A} (hL : IsLat O E L) (t : A)
    (ht : ∀ y ∈ L, t * y ∈ L) : IsIntegral O t := by
  haveI : Module.Finite O L := Module.Finite.iff_fg.mpr hL.1
  let f : Module.End O L := (LinearMap.mulLeft O t).restrict (fun y hy => ht y hy)
  obtain ⟨p, hp, hpf⟩ := LinearMap.exists_monic_and_aeval_eq_zero O f
  have hpow : ∀ (n : ℕ) (y : L), (((f ^ n) y : L) : A) = t ^ n * y := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ', Module.End.mul_apply]
      change t * (((f ^ n) y : L) : A) = _
      rw [ih, pow_succ', mul_assoc]
  have hev : ∀ y : L, ((aeval f p y : L) : A) = aeval t p * y := by
    intro y
    rw [aeval_eq_sum_range, aeval_eq_sum_range, Finset.sum_mul, LinearMap.sum_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [LinearMap.smul_apply, Submodule.coe_smul, hpow, smul_mul_assoc]
  have hkill : ∀ y ∈ L, aeval t p * y = 0 := by
    intro y hy
    have := hev ⟨y, hy⟩
    rw [hpf] at this
    simpa using this.symm
  have hall : ∀ z ∈ Submodule.span E (L : Set A), aeval t p * z = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem y hy => exact hkill y hy
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul e x _ hx => rw [mul_smul_comm, hx, smul_zero]
  have h1 : aeval t p = 0 := by
    have := hall 1 (by rw [hL.2]; trivial)
    simpa using this
  exact ⟨p, hp, by rw [← aeval_def]; exact h1⟩

theorem stabilizer_le_intUnits (O E A : Type) [CommRing O] [Field E] [CommRing A] [Algebra O A]
    [Algebra E A] (g : A) (L : stLat O E g) : MulAction.stabilizer Aˣ L ≤ intUnits O A := by
  intro t ht
  have key : ∀ s : Aˣ, s • L = L → ∀ y ∈ (L : Submodule O A), (s : A) * y ∈ (L : Submodule O A) := by
    intro s hs y hy
    have he : mulLat O (s : A) (L : Submodule O A) = L := by
      rw [← stLat_smul_val, hs]
    rw [← he]
    exact ⟨y, hy, rfl⟩
  have ht' : t⁻¹ ∈ MulAction.stabilizer Aˣ L := inv_mem ht
  exact ⟨isIntegral_of_mul_mem_lat (E := E) L.2.1 _ (key t ht),
    isIntegral_of_mul_mem_lat (E := E) L.2.1 _ (key t⁻¹ ht')⟩

end GlobalTheory.UnitLemma
end
end

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_stableLattice_le_integralUnitsSubgroup : ∀ (O E A : Type) [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A] (g : A) (L : stLat O E g), MulAction.stabilizer Aˣ L ≤ intUnits O A := by
  atlas_forward_decl GlobalTheory.UnitLemma.stabilizer_le_intUnits
end

section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraEtale_of_separable_charpoly_mulLeft : ∀ (E A : Type) [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → Algebra.Etale E A := by
  first | exact @GlobalTheory.etale_of_separable_charpoly_mulLeft | exact GlobalTheory.etale_of_separable_charpoly_mulLeft | (intros; apply GlobalTheory.etale_of_separable_charpoly_mulLeft <;> assumption)
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosure_fg_finiteEtale_dvr : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] [Algebra.Etale E A], (Subalgebra.toSubmodule (integralClosure O A)).FG := by
  first | exact @GlobalTheory.IntegralClosureFG.integralClosure_fg | exact GlobalTheory.IntegralClosureFG.integralClosure_fg | (intros; apply GlobalTheory.IntegralClosureFG.integralClosure_fg <;> assumption)
end

section
section
open GlobalTheory.UnitLemma Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.StabIdx

theorem relIndex_ne_zero_of_map {G X : Type} [Group G] [Finite X] (H K : Subgroup G) (f : K → X)
    (hf : ∀ a b : K, f a = f b → (a : G)⁻¹ * b ∈ H) : H.relIndex K ≠ 0 := by
  classical
  haveI : Finite (K ⧸ H.subgroupOf K) := by
    refine Finite.of_injective (fun q : K ⧸ H.subgroupOf K => f q.out) ?_
    intro q q' h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa using hf _ _ h
  exact Subgroup.index_ne_zero_of_finite

variable {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A]

theorem mem_stabilizer_of {g : A} (L : stLat O E g) (t : Aˣ)
    (h1 : ∀ y ∈ (L : Submodule O A), (t : A) * y ∈ (L : Submodule O A))
    (h2 : ∀ y ∈ (L : Submodule O A), ((t⁻¹ : Aˣ) : A) * y ∈ (L : Submodule O A)) :
    t ∈ MulAction.stabilizer Aˣ L := by
  rw [MulAction.mem_stabilizer_iff]
  apply Subtype.ext
  rw [stLat_smul_val]
  ext x
  rw [mem_mulLat_iff]
  constructor
  · intro hx
    have := h1 _ hx
    rwa [← mul_assoc, Units.mul_inv, one_mul] at this
  · intro hx
    exact h2 _ hx

theorem finite_quotient_span [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] {c : O} (hc : c ≠ 0) : Finite (O ⧸ Ideal.span {c}) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hne : Ideal.span {c} ≠ ⊥ := by simpa using hc
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) :=
    (inferInstance : Finite (IsLocalRing.ResidueField O))
  have := Ideal.finite_quotient_pow (IsNoetherian.noetherian (IsLocalRing.maximalIdeal O)) n
  rwa [hm, Ideal.span_singleton_pow, ← hn] at this

variable [IsDomain O] [Algebra O E] [IsFractionRing O E] [IsScalarTower O E A]

theorem exists_smul_mul_mem (C L : Submodule O A) (hC : C.FG) (hL : IsLat O E L) :
    ∃ c : O, c ≠ 0 ∧ ∀ x ∈ C, ∀ y ∈ L, c • (x * y) ∈ L := by
  classical
  obtain ⟨s, hs⟩ := hC
  obtain ⟨t, ht⟩ := hL.1
  have hex : ∀ p : A × A, ∃ r : O, r ≠ 0 ∧ r • (p.1 * p.2) ∈ L := fun p =>
    ReciprocityTheory.PGsh.L2.SecondCohomologyLattice.exists_smul_mem_of_mem_span (C := E) L (by rw [hL.2]; trivial)
  choose r hr0 hrm using hex
  refine ⟨∏ p ∈ s ×ˢ t, r p, Finset.prod_ne_zero_iff.2 fun p _ => hr0 p, ?_⟩
  have hgen : ∀ a ∈ s, ∀ b ∈ t, (∏ p ∈ s ×ˢ t, r p) • (a * b) ∈ L := by
    intro a ha b hb
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem r (Finset.mem_product.2 ⟨ha, hb⟩ : (a, b) ∈ s ×ˢ t)
    rw [hk, mul_comm, mul_smul]
    exact L.smul_mem _ (hrm (a, b))
  intro x hx y hy
  rw [← ht] at hy
  induction hy using Submodule.span_induction with
  | mem b hb =>
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem a ha => exact hgen a ha b hb
    | zero => simp
    | add u v _ _ hu hv => rw [add_mul, smul_add]; exact L.add_mem hu hv
    | smul o u _ hu => rw [smul_mul_assoc, smul_comm]; exact L.smul_mem _ hu
  | zero => simp
  | add u v _ _ hu hv => rw [mul_add, smul_add]; exact L.add_mem hu hv
  | smul o u _ hu => rw [mul_smul_comm, smul_comm]; exact L.smul_mem _ hu

theorem relIndex_ne_zero_of_fg [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
    {g : A} (hC : (Subalgebra.toSubmodule (integralClosure O A)).FG) (L : stLat O E g) :
    (MulAction.stabilizer Aˣ L).relIndex (intUnits O A) ≠ 0 := by
  classical
  set C := Subalgebra.toSubmodule (integralClosure O A) with hCdef
  obtain ⟨c, hc0, hcL⟩ := exists_smul_mul_mem (E := E) C (L : Submodule O A) hC L.2.1
  haveI := finite_quotient_span hc0
  haveI : Finite (C ⧸ (⊤ : Submodule O C)) := by
    haveI : Subsingleton (C ⧸ (⊤ : Submodule O C)) := Submodule.Quotient.subsingleton_iff.2 rfl
    infer_instance
  haveI : Finite (C ⧸ Ideal.span {c} • (⊤ : Submodule O C)) :=
    Submodule.finite_quotient_smul _ ((Submodule.fg_top C).2 hC)
  have hmemC : ∀ x : A, IsIntegral O x → x ∈ C := fun x hx => hx
  let f : intUnits O A → C ⧸ Ideal.span {c} • (⊤ : Submodule O C) := fun t =>
    Submodule.Quotient.mk ⟨((t : Aˣ) : A), hmemC _ t.2.1⟩
  refine relIndex_ne_zero_of_map _ _ f fun a b hab => ?_
  rw [Submodule.Quotient.eq, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hab
  obtain ⟨n, -, hn⟩ := hab
  have hn' : c • (n : A) = ((a : Aˣ) : A) - ((b : Aˣ) : A) := by
    have := congrArg Subtype.val hn
    simpa using this
  have ha : ((a : Aˣ)⁻¹ : Aˣ).val * (a : Aˣ).val = 1 := Units.inv_mul _
  have hb : ((b : Aˣ)⁻¹ : Aˣ).val * (b : Aˣ).val = 1 := Units.inv_mul _
  have hna : ((a : Aˣ)⁻¹ : Aˣ).val * (n : A) ∈ C := hmemC _ (a.2.2.mul n.2)
  have hnb : ((b : Aˣ)⁻¹ : Aˣ).val * (n : A) ∈ C := hmemC _ (b.2.2.mul n.2)
  apply mem_stabilizer_of L
  · intro y hy
    have e : (((a : Aˣ)⁻¹ * (b : Aˣ) : Aˣ) : A) * y =
        y - c • ((((a : Aˣ)⁻¹ : Aˣ).val * (n : A)) * y) := by
      rw [Units.val_mul]
      rw [Algebra.smul_def] at hn' ⊢
      linear_combination (((a : Aˣ)⁻¹ : Aˣ).val * y) * hn' + y * ha
    rw [e]
    exact L.1.sub_mem hy (hcL _ hna _ hy)
  · intro y hy
    have e : ((((a : Aˣ)⁻¹ * (b : Aˣ))⁻¹ : Aˣ) : A) * y =
        y + c • ((((b : Aˣ)⁻¹ : Aˣ).val * (n : A)) * y) := by
      rw [mul_inv_rev, inv_inv, Units.val_mul]
      rw [Algebra.smul_def] at hn' ⊢
      linear_combination (-(((b : Aˣ)⁻¹ : Aˣ).val * y)) * hn' + y * hb
    rw [e]
    exact L.1.add_mem hy (hcL _ hnb _ hy)

theorem stabilizer_relIndex_intUnits_ne_zero : ∀ (O E A : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field E] [Algebra O E]
    [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A]
    [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable →
    ∀ L : stLat O E g, (MulAction.stabilizer Aˣ L).relIndex (intUnits O A) ≠ 0 := by
  intro O E A _ _ _ _ _ _ _ _ _ _ _ _ g hg L
  haveI := GlobalTheory.T.algebraEtale_of_separable_charpoly_mulLeft E A g hg
  exact relIndex_ne_zero_of_fg (GlobalTheory.T.integralClosure_fg_finiteEtale_dvr O E A) L

end GlobalTheory.UnitLemma.StabIdx
end
end

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_relIndex_intUnits_ne_zero' : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → ∀ L : stLat O E g, (MulAction.stabilizer Aˣ L).relIndex (intUnits O A) ≠ 0 := by
  atlas_forward_decl GlobalTheory.UnitLemma.StabIdx.stabilizer_relIndex_intUnits_ne_zero
end

section
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem latProj_smul (O E A₁ A₂ : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] (g₁ : A₁) (g₂ : A₂) (t : (A₁ × A₂)ˣ) (M : stLat O E ((g₁, g₂) : A₁ × A₂)) :
    latProj O E g₁ g₂ (t • M) = t • latProj O E g₁ g₂ M := by
  rw [latPair_smul]
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · change (mulLat O (t : A₁ × A₂) (M : Submodule O (A₁ × A₂))).comap (LinearMap.inl O A₁ A₂) =
      mulLat O ((Units.map (MonoidHom.fst A₁ A₂) t : A₁ˣ) : A₁) ((M : Submodule O (A₁ × A₂)).comap (LinearMap.inl O A₁ A₂))
    ext y
    rw [Submodule.mem_comap, mem_mulLat_iff, mem_mulLat_iff, Submodule.mem_comap]
    have h : ((t⁻¹ : (A₁ × A₂)ˣ) : A₁ × A₂) * (LinearMap.inl O A₁ A₂ y) =
        LinearMap.inl O A₁ A₂ (((Units.map (MonoidHom.fst A₁ A₂) t)⁻¹ : A₁ˣ) * y) := by
      ext <;> simp
    rw [h]
  · change (mulLat O (t : A₁ × A₂) (M : Submodule O (A₁ × A₂))).map (LinearMap.snd O A₁ A₂) =
      mulLat O ((Units.map (MonoidHom.snd A₁ A₂) t : A₂ˣ) : A₂) ((M : Submodule O (A₁ × A₂)).map (LinearMap.snd O A₁ A₂))
    unfold mulLat
    rw [← Submodule.map_comp, ← Submodule.map_comp]
    congr 1

end GlobalTheory.UnitLemma
end

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stableLatticePair_projection_smul_units : ∀ (O E A₁ A₂ : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] (g₁ : A₁) (g₂ : A₂) (t : (A₁ × A₂)ˣ) (M : stLat O E ((g₁, g₂) : A₁ × A₂)), latProj O E g₁ g₂ (t • M) = t • latProj O E g₁ g₂ M := by
  atlas_forward_decl GlobalTheory.UnitLemma.latProj_smul
end

section
section
noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial

section Fibre

variable {O E A₁ A₂ : Type} [CommRing O] [Field E] [Algebra O E]
  [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂]
  [IsScalarTower O E A₁] [IsScalarTower O E A₂]

theorem inf_ker_snd_eq (M : Submodule O (A₁ × A₂)) :
    M ⊓ LinearMap.ker (LinearMap.snd O A₁ A₂) =
      (M.comap (LinearMap.inl O A₁ A₂)).map (LinearMap.inl O A₁ A₂) := by
  ext ⟨a, b⟩
  simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.snd_apply, Submodule.mem_map,
    Submodule.mem_comap, LinearMap.inl_apply]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨a, h, rfl⟩
  · rintro ⟨x, hx, h⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hx, rfl⟩

theorem isLat_of_comap_inl_map_snd {M : Submodule O (A₁ × A₂)}
    (h₁ : IsLat O E (M.comap (LinearMap.inl O A₁ A₂)))
    (h₂ : IsLat O E (M.map (LinearMap.snd O A₁ A₂))) : IsLat O E M := by
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.snd O A₁ A₂) h₂.1 ?_, ?_⟩
  · rw [inf_ker_snd_eq]; exact h₁.1.map _
  · set S := Submodule.span E (M : Set (A₁ × A₂)) with hS
    have hl : LinearMap.range (LinearMap.inl E A₁ A₂) ≤ S := by
      rw [LinearMap.range_eq_map, ← h₁.2, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      exact Submodule.subset_span (by simpa using hx)
    have hr : S.map (LinearMap.snd E A₁ A₂) = ⊤ := by
      rw [hS, Submodule.map_span, ← h₂.2]
      congr 1
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    have hb : b ∈ S.map (LinearMap.snd E A₁ A₂) := by rw [hr]; trivial
    obtain ⟨z, hz, hzb⟩ := hb
    have hab : ((a, b) : A₁ × A₂) = z + LinearMap.inl E A₁ A₂ (a - z.1) := by
      ext <;> simp [← hzb]
    rw [hab]
    exact S.add_mem hz (hl ⟨_, rfl⟩)

end Fibre

theorem ncard_fibre_latProj (O E A₁ A₂ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A₁]
    [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] [IsScalarTower O E A₁]
    [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂) :
    resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly ≠ 0 →
      ∀ y : LatPair O E g₁ g₂, ((latProj O E g₁ g₂ ⁻¹' {y}).ncard : ℚ) =
        (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^
          val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) := by
  intro hR y
  have key := GlobalTheory.T.card_stable_lattices_alt O E A₁ A₂ g₁ g₂ hR y.1.1 y.2.1 y.1.2.1 y.2.2.1 y.1.2.2 y.2.2.2
  let e : ↥(latProj O E g₁ g₂ ⁻¹' {y}) ≃
      {M : Submodule O (A₁ × A₂) // (∀ z ∈ M, (g₁, g₂) * z ∈ M) ∧
        M.comap (LinearMap.inl O A₁ A₂) = y.1.1 ∧ M.map (LinearMap.snd O A₁ A₂) = y.2.1} :=
    { toFun := fun M => ⟨M.1.1, M.1.2.2,
        congrArg (fun p : LatPair O E g₁ g₂ => (p.1 : Submodule O A₁)) M.2,
        congrArg (fun p : LatPair O E g₁ g₂ => (p.2 : Submodule O A₂)) M.2⟩
      invFun := fun M => ⟨⟨M.1, isLat_of_comap_inl_map_snd (by rw [M.2.2.1]; exact y.1.2.1)
          (by rw [M.2.2.2]; exact y.2.2.1), M.2.1⟩,
        Set.mem_singleton_iff.mpr (Prod.ext (Subtype.ext M.2.2.1) (Subtype.ext M.2.2.2))⟩
      left_inv := fun M => rfl
      right_inv := fun M => rfl }
  have hc : (latProj O E g₁ g₂ ⁻¹' {y}).ncard = Nat.card {M : Submodule O (A₁ × A₂) //
      (∀ z ∈ M, (g₁, g₂) * z ∈ M) ∧ M.comap (LinearMap.inl O A₁ A₂) = y.1.1 ∧
        M.map (LinearMap.snd O A₁ A₂) = y.2.1} := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr e
  rw [hc]
  exact key

end GlobalTheory.UnitLemma
end
end

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ncard_fibre_stableLatticePairProjection : ∀ (O E A₁ A₂ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂), resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly ≠ 0 → ∀ y : LatPair O E g₁ g₂, ((latProj O E g₁ g₂ ⁻¹' {y}).ncard : ℚ) = (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) := by
  atlas_forward_decl GlobalTheory.UnitLemma.ncard_fibre_latProj
end

section
section
noncomputable section

namespace GlobalTheory.UnitLemma.PairStab

open GlobalTheory.UnitLemma Polynomial

theorem relIndex_prod_prod {A B : Type} [Group A] [Group B] (H₁ K₁ : Subgroup A) (H₂ K₂ : Subgroup B) :
    (H₁.prod H₂).relIndex (K₁.prod K₂) = H₁.relIndex K₁ * H₂.relIndex K₂ := by
  have h : (H₁.prod H₂).subgroupOf (K₁.prod K₂) =
      ((H₁.subgroupOf K₁).prod (H₂.subgroupOf K₂)).comap (K₁.prodEquiv K₂).toMonoidHom := by
    ext x
    rfl
  unfold Subgroup.relIndex
  rw [h, Subgroup.index_comap_of_surjective _ (K₁.prodEquiv K₂).surjective, Subgroup.index_prod]

section

variable (O : Type) [CommRing O] {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂]

theorem intUnits_prod_eq :
    intUnits O (A₁ × A₂) = ((intUnits O A₁).prod (intUnits O A₂)).comap
      (MulEquiv.prodUnits (M := A₁) (N := A₂)).toMonoidHom := by
  ext t
  change (IsIntegral O (t : A₁ × A₂) ∧ IsIntegral O ((t⁻¹ : (A₁ × A₂)ˣ) : A₁ × A₂)) ↔
    (IsIntegral O (t : A₁ × A₂).1 ∧ IsIntegral O ((t⁻¹ : (A₁ × A₂)ˣ) : A₁ × A₂).1) ∧
    (IsIntegral O (t : A₁ × A₂).2 ∧ IsIntegral O ((t⁻¹ : (A₁ × A₂)ˣ) : A₁ × A₂).2)
  rw [IsIntegral.pair_iff, IsIntegral.pair_iff]
  tauto

variable (E : Type) [Field E] [Algebra E A₁] [Algebra E A₂]

theorem stabilizer_latPair_eq (g₁ : A₁) (g₂ : A₂) (y : LatPair O E g₁ g₂) :
    MulAction.stabilizer (A₁ × A₂)ˣ y = ((MulAction.stabilizer A₁ˣ y.1).prod
      (MulAction.stabilizer A₂ˣ y.2)).comap (MulEquiv.prodUnits (M := A₁) (N := A₂)).toMonoidHom := by
  ext t
  rw [MulAction.mem_stabilizer_iff, latPair_smul, Subgroup.mem_comap, Subgroup.mem_prod,
    MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  exact Prod.ext_iff

end

theorem stabilizer_pair_relIndex : ∀ (O E A₁ A₂ : Type) [CommRing O] [Field E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] (g₁ : A₁) (g₂ : A₂) (y : LatPair O E g₁ g₂), MulAction.stabilizer A₁ˣ y.1 ≤ intUnits O A₁ → MulAction.stabilizer A₂ˣ y.2 ≤ intUnits O A₂ → MulAction.stabilizer (A₁ × A₂)ˣ y ≤ intUnits O (A₁ × A₂) ∧ (MulAction.stabilizer (A₁ × A₂)ˣ y).relIndex (intUnits O (A₁ × A₂)) = (MulAction.stabilizer A₁ˣ y.1).relIndex (intUnits O A₁) * (MulAction.stabilizer A₂ˣ y.2).relIndex (intUnits O A₂) := by
  intro O E A₁ A₂ _ _ _ _ _ _ _ _ g₁ g₂ y h₁ h₂
  rw [stabilizer_latPair_eq, intUnits_prod_eq]
  refine ⟨Subgroup.comap_mono (fun t ht => ⟨h₁ ht.1, h₂ ht.2⟩), ?_⟩
  rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective
    (f := (MulEquiv.prodUnits (M := A₁) (N := A₂)).toMonoidHom) MulEquiv.prodUnits.surjective,
    relIndex_prod_prod]

end GlobalTheory.UnitLemma.PairStab
end
end

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_stableLatticePair_relIndex_integralUnits : ∀ (O E A₁ A₂ : Type) [CommRing O] [Field E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] (g₁ : A₁) (g₂ : A₂) (y : LatPair O E g₁ g₂), MulAction.stabilizer A₁ˣ y.1 ≤ intUnits O A₁ → MulAction.stabilizer A₂ˣ y.2 ≤ intUnits O A₂ → MulAction.stabilizer (A₁ × A₂)ˣ y ≤ intUnits O (A₁ × A₂) ∧ (MulAction.stabilizer (A₁ × A₂)ˣ y).relIndex (intUnits O (A₁ × A₂)) = (MulAction.stabilizer A₁ˣ y.1).relIndex (intUnits O A₁) * (MulAction.stabilizer A₂ˣ y.2).relIndex (intUnits O A₂) := by
  atlas_forward_decl GlobalTheory.UnitLemma.PairStab.stabilizer_pair_relIndex
end

section
section
noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial

section PairOrbits

variable (O E A₁ A₂ : Type) [CommRing O] [Field E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂]
  [Algebra E A₁] [Algebra E A₂] (g₁ : A₁) (g₂ : A₂)

theorem latPair_orbitRel_iff (p q : LatPair O E g₁ g₂) :
    (MulAction.orbitRel (A₁ × A₂)ˣ (LatPair O E g₁ g₂)) p q ↔
      (MulAction.orbitRel A₁ˣ (stLat O E g₁)) p.1 q.1 ∧ (MulAction.orbitRel A₂ˣ (stLat O E g₂)) p.2 q.2 := by
  simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  · rintro ⟨⟨t₁, h₁⟩, ⟨t₂, h₂⟩⟩
    refine ⟨MulEquiv.prodUnits.symm (t₁, t₂), ?_⟩
    rw [latPair_smul]
    have e₁ : Units.map (MonoidHom.fst A₁ A₂) (MulEquiv.prodUnits.symm (t₁, t₂)) = t₁ :=
      congrArg Prod.fst (MulEquiv.prodUnits.apply_symm_apply (t₁, t₂))
    have e₂ : Units.map (MonoidHom.snd A₁ A₂) (MulEquiv.prodUnits.symm (t₁, t₂)) = t₂ :=
      congrArg Prod.snd (MulEquiv.prodUnits.apply_symm_apply (t₁, t₂))
    rw [e₁, e₂, h₁, h₂]
    rfl

def latPairOrbitEquiv :
    MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂) ≃
      MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁) × MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂) where
  toFun := Quotient.lift (fun p : LatPair O E g₁ g₂ => ((Quotient.mk _ p.1 : MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁)),
      (Quotient.mk _ p.2 : MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂))))
    (fun p q h => by
      obtain ⟨h₁, h₂⟩ := (latPair_orbitRel_iff O E A₁ A₂ g₁ g₂ p q).1 h
      exact Prod.ext (Quotient.sound h₁) (Quotient.sound h₂))
  invFun x := Quotient.lift₂ (fun (a : stLat O E g₁) (b : stLat O E g₂) =>
      (Quotient.mk _ ((a, b) : LatPair O E g₁ g₂) : MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂)))
    (fun a₁ b₁ a₂ b₂ h₁ h₂ => Quotient.sound
      ((latPair_orbitRel_iff O E A₁ A₂ g₁ g₂ (a₁, b₁) (a₂, b₂)).2 ⟨h₁, h₂⟩)) x.1 x.2
  left_inv o := by
    induction o using Quotient.inductionOn with
    | h p => rfl
  right_inv x := by
    obtain ⟨x₁, x₂⟩ := x
    induction x₁ using Quotient.inductionOn with
    | h a => induction x₂ using Quotient.inductionOn with
      | h b => rfl

end PairOrbits

theorem latPair_orbit_finite_and_sum : ∀ (O E A₁ A₂ : Type) [CommRing O] [Field E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] (g₁ : A₁) (g₂ : A₂), Finite (MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁)) → Finite (MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂)) → Finite (MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂)) ∧ ∀ (f₁ : stLat O E g₁ → ℚ) (f₂ : stLat O E g₂ → ℚ), (∀ (t : A₁ˣ) (y : stLat O E g₁), f₁ (t • y) = f₁ y) → (∀ (t : A₂ˣ) (y : stLat O E g₂), f₂ (t • y) = f₂ y) → ∑ᶠ o : MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂), f₁ (Quotient.out o).1 * f₂ (Quotient.out o).2 = (∑ᶠ o : MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁), f₁ (Quotient.out o)) * (∑ᶠ o : MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂), f₂ (Quotient.out o)) := by
  intro O E A₁ A₂ _ _ _ _ _ _ _ _ g₁ g₂ h₁ h₂
  let e := latPairOrbitEquiv O E A₁ A₂ g₁ g₂
  haveI hfin : Finite (MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂)) := Finite.of_equiv _ e.symm
  refine ⟨hfin, ?_⟩
  intro f₁ f₂ hf₁ hf₂

  have inv₁ : ∀ a b : stLat O E g₁, (MulAction.orbitRel A₁ˣ (stLat O E g₁)) a b → f₁ a = f₁ b := by
    intro a b h
    obtain ⟨t, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
    exact hf₁ t b
  have inv₂ : ∀ a b : stLat O E g₂, (MulAction.orbitRel A₂ˣ (stLat O E g₂)) a b → f₂ a = f₂ b := by
    intro a b h
    obtain ⟨t, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
    exact hf₂ t b
  have key : ∀ x : MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁) × MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂),
      f₁ (Quotient.out (e.symm x)).1 * f₂ (Quotient.out (e.symm x)).2 = f₁ (Quotient.out x.1) * f₂ (Quotient.out x.2) := by
    intro x
    have hx : e (e.symm x) = x := e.apply_symm_apply x
    set o := e.symm x
    have h1 : (Quotient.mk _ (Quotient.out o).1 : MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁)) = x.1 := by
      rw [← hx]
      conv_rhs => rw [← Quotient.out_eq o]
      rfl
    have h2 : (Quotient.mk _ (Quotient.out o).2 : MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂)) = x.2 := by
      rw [← hx]
      conv_rhs => rw [← Quotient.out_eq o]
      rfl
    rw [inv₁ _ _ (Quotient.exact (h1.trans (Quotient.out_eq x.1).symm)),
      inv₂ _ _ (Quotient.exact (h2.trans (Quotient.out_eq x.2).symm))]
  haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁))
  haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂))
  rw [← finsum_comp_equiv e.symm]
  simp_rw [key]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Fintype.sum_prod_type,
    Finset.sum_mul_sum]

end GlobalTheory.UnitLemma
end
end

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stableLatticePair_orbits_finite_and_card_prod : ∀ (O E A₁ A₂ : Type) [CommRing O] [Field E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] (g₁ : A₁) (g₂ : A₂), Finite (MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁)) → Finite (MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂)) → Finite (MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂)) ∧ ∀ (f₁ : stLat O E g₁ → ℚ) (f₂ : stLat O E g₂ → ℚ), (∀ (t : A₁ˣ) (y : stLat O E g₁), f₁ (t • y) = f₁ y) → (∀ (t : A₂ˣ) (y : stLat O E g₂), f₂ (t • y) = f₂ y) → ∑ᶠ o : MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂), f₁ (Quotient.out o).1 * f₂ (Quotient.out o).2 = (∑ᶠ o : MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁), f₁ (Quotient.out o)) * (∑ᶠ o : MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂), f₂ (Quotient.out o)) := by
  atlas_forward_decl GlobalTheory.UnitLemma.latPair_orbit_finite_and_sum
end

section
section
open Polynomial

namespace GlobalTheory.UnitLemma.DescentGL

open GlobalTheory.UnitLemma

theorem stab_smul_comm {G X : Type} [CommGroup G] [MulAction G X] (t : G) (x : X) :
    MulAction.stabilizer G (t • x) = MulAction.stabilizer G x := by
  ext h
  simp only [MulAction.mem_stabilizer_iff]
  rw [smul_smul, mul_comm, ← smul_smul, smul_left_cancel_iff]

theorem countGL_prod : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂), ((LinearMap.mulLeft E g₁).charpoly * (LinearMap.mulLeft E g₂).charpoly).Separable → countGL O E ((g₁, g₂) : A₁ × A₂) = (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) * (countGL O E g₁ * countGL O E g₂) := by
  intro O _ _ _ _ E _ _ _ _ A₁ A₂ _ _ _ _ _ _ _ _ _ _ g₁ g₂ hsep
  have hs₁ := hsep.of_mul_left
  have hs₂ := hsep.of_mul_right
  have hres : resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly ≠ 0 :=
    resultant_ne_zero _ _ hsep.isCoprime
  rw [GlobalTheory.T.stableLatticeOrbitCount_eq_sum_orbits O E (A₁ × A₂) (g₁, g₂), GlobalTheory.T.stableLatticeOrbitCount_eq_sum_orbits O E A₁ g₁, GlobalTheory.T.stableLatticeOrbitCount_eq_sum_orbits O E A₂ g₂]
  haveI hf₁ := GlobalTheory.T.finite_unit_orbits_stable_lattices_separable O E A₁ g₁ hs₁
  haveI hf₂ := GlobalTheory.T.finite_unit_orbits_stable_lattices_separable O E A₂ g₂ hs₂
  obtain ⟨hfinY, hsum⟩ := GlobalTheory.T.stableLatticePair_orbits_finite_and_card_prod O E A₁ A₂ g₁ g₂ hf₁ hf₂
  have hq : (Nat.card (IsLocalRing.ResidueField O) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField O)).ne'
  have hfib := GlobalTheory.T.ncard_fibre_stableLatticePairProjection O E A₁ A₂ g₁ g₂ hres
  have hstab : ∀ y : LatPair O E g₁ g₂, MulAction.stabilizer (A₁ × A₂)ˣ y ≤ intUnits O (A₁ × A₂) ∧
      (MulAction.stabilizer (A₁ × A₂)ˣ y).relIndex (intUnits O (A₁ × A₂)) ≠ 0 := by
    intro y
    obtain ⟨h1, h2⟩ := GlobalTheory.T.stabilizer_stableLatticePair_relIndex_integralUnits O E A₁ A₂ g₁ g₂ y (GlobalTheory.T.stabilizer_stableLattice_le_integralUnitsSubgroup O E A₁ g₁ y.1) (GlobalTheory.T.stabilizer_stableLattice_le_integralUnitsSubgroup O E A₂ g₂ y.2)
    exact ⟨h1, by rw [h2]; exact mul_ne_zero (GlobalTheory.T.stabilizer_relIndex_intUnits_ne_zero' O E A₁ g₁ hs₁ y.1) (GlobalTheory.T.stabilizer_relIndex_intUnits_ne_zero' O E A₂ g₂ hs₂ y.2)⟩
  have hfin : ∀ y, (latProj O E g₁ g₂ ⁻¹' {y}).Finite := by
    intro y
    apply Set.finite_of_ncard_ne_zero
    have h := hfib y
    intro h0
    rw [h0, Nat.cast_zero] at h
    exact zpow_ne_zero _ hq h.symm
  have hCP := GlobalTheory.T.finsum_orbits_counting_principle_finite_fibres (A₁ × A₂)ˣ (stLat O E ((g₁, g₂) : A₁ × A₂)) (LatPair O E g₁ g₂) (intUnits O (A₁ × A₂))
    (latProj O E g₁ g₂) (GlobalTheory.T.stableLatticePair_projection_smul_units O E A₁ A₂ g₁ g₂) hfin hstab hfinY (fun _ => 1) (fun _ _ => rfl)
  simp only [one_mul] at hCP
  rw [hCP]
  have hterm : ∀ o : MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂),
      ((latProj O E g₁ g₂ ⁻¹' {Quotient.out o}).ncard : ℚ) *
        ((MulAction.stabilizer (A₁ × A₂)ˣ (Quotient.out o)).relIndex (intUnits O (A₁ × A₂)) : ℚ) =
      (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) *
        (((MulAction.stabilizer A₁ˣ (Quotient.out o).1).relIndex (intUnits O A₁) : ℚ) *
          ((MulAction.stabilizer A₂ˣ (Quotient.out o).2).relIndex (intUnits O A₂) : ℚ)) := by
    intro o
    rw [hfib, (GlobalTheory.T.stabilizer_stableLatticePair_relIndex_integralUnits O E A₁ A₂ g₁ g₂ _ (GlobalTheory.T.stabilizer_stableLattice_le_integralUnitsSubgroup O E A₁ g₁ _) (GlobalTheory.T.stabilizer_stableLattice_le_integralUnitsSubgroup O E A₂ g₂ _)).2, Nat.cast_mul]
  have hs := hsum (fun y => ((MulAction.stabilizer A₁ˣ y).relIndex (intUnits O A₁) : ℚ))
    (fun y => ((MulAction.stabilizer A₂ˣ y).relIndex (intUnits O A₂) : ℚ))
    (fun t y => by simp only [stab_smul_comm]) (fun t y => by simp only [stab_smul_comm])
  rw [finsum_congr hterm, ← mul_finsum, hs]

end GlobalTheory.UnitLemma.DescentGL
end

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weighted_count_stable_lattices_product_descent_GL : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂), ((LinearMap.mulLeft E g₁).charpoly * (LinearMap.mulLeft E g₂).charpoly).Separable → countGL O E ((g₁, g₂) : A₁ × A₂) = (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) * (countGL O E g₁ * countGL O E g₂) := by
  atlas_forward_decl GlobalTheory.UnitLemma.DescentGL.countGL_prod
end
