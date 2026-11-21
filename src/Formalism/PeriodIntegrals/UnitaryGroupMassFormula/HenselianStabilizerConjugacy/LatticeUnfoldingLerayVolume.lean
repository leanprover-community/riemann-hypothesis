import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HenselianStabilizerConjugacy.IsSelfDual

section
noncomputable section

open scoped Classical
open ValuativeRel

namespace PI.SelfDualHermitianLattices

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict

section ObjJ

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

def fixZ (H : HermSp M V) (Z : Submodule E V) : Subgroup (V ≃ₗ[E] V) :=
  Subgroup.closure {g | IsUnitary H g ∧ ∀ v ∈ Z, g v = v}

def Commens {G : Type*} [Group G] (K K' : Subgroup G) : Prop :=
  K.relIndex K' ≠ 0 ∧ K'.relIndex K ≠ 0

def OrbRel (G : Subgroup (V ≃ₗ[E] V)) (Λ Λ' : Submodule M.L.O V) : Prop :=
  ∃ g ∈ G, img g Λ = Λ'

def massOf (G K : Subgroup (V ≃ₗ[E] V)) (Rs : Set (Submodule M.L.O V)) : ENNReal :=
  ∑' Λ : Rs, ENNReal.ofReal (1 / volRel (G ⊓ Aut (Λ : Submodule M.L.O V)) K)

def SigZ (H : HermSp M V) (Z : Submodule E V) (Mh : Submodule M.L.O V) : Set (Submodule M.L.O V) :=
  {Λ | IsSelfDual H Λ ∧ Λ ⊓ Z.restrictScalars M.L.O = Mh}

def piIn (H : HermSp M V) (ϖ : 𝒪[F]) (Λs : Submodule M.L.O V) : Submodule M.L.O Λs :=
  (H.smulLat (algebraMap F E (ϖ : F)) Λs).comap Λs.subtype

def PrimTup (H : HermSp M V) (Λs : Submodule M.L.O V) {m : ℕ} (x : Fin m → Λs) : Prop :=
  ∀ c : Fin m → M.L.O, ∃ y ∈ Λs, ∀ a, H.h y (x a : V) = (c a : E)

def GramCong (H : HermSp M V) (ϖ : 𝒪[F]) {m : ℕ} (x : Fin m → V) (Gm : Matrix (Fin m) (Fin m) E) : Prop :=
  ∀ a b, ∃ e ∈ M.L.O, H.h (x b) (x a) - Gm a b = algebraMap F E (ϖ : F) * e

def dlCount (H : HermSp M V) (Λs : Submodule M.L.O V) (ϖ : 𝒪[F]) {m : ℕ} (Gm : Matrix (Fin m) (Fin m) E) : ℕ :=
  Nat.card {c : Fin m → (Λs ⧸ piIn H ϖ Λs) //
    ∃ x : Fin m → Λs, (∀ a, Submodule.Quotient.mk (x a) = c a) ∧ PrimTup H Λs x ∧
      GramCong H ϖ (fun a => (x a : V)) Gm}

def dl (H : HermSp M V) (Λs : Submodule M.L.O V) (ϖ : 𝒪[F]) {m : ℕ} (Gm : Matrix (Fin m) (Fin m) E) : ℝ :=
  (dlCount H Λs ϖ Gm : ℝ) / (qF F : ℝ) ^ (2 * Module.finrank E V * m - m ^ 2)

def idx (M : Model F E) {m : ℕ} (ff b : Fin m → V) : ℕ :=
  Nat.card (Submodule.span M.L.O (Set.range b) ⧸
    (Submodule.span M.L.O (Set.range ff)).comap (Submodule.span M.L.O (Set.range b)).subtype)

end ObjJ

def LatticeCountingFormula : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (m : ℕ) (ff : Fin m → V),
      IsUnit (H.gram ff).det →
      ∀ (Λs : Submodule M.L.O V), IsSelfDual H Λs → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ K : Subgroup (V ≃ₗ[E] V), K ≤ fixZ H (Submodule.span E (Set.range ff)) →
        Commens K (fixZ H (Submodule.span E (Set.range ff)) ⊓ Aut Λs) →
      ∃ κ : ℝ, 0 < κ ∧
        ∀ b : Fin m → V, (∀ a, b a ∈ Submodule.span E (Set.range ff)) →
          (∀ a, ff a ∈ Submodule.span M.L.O (Set.range b)) →
          ∀ Rs : Set (Submodule M.L.O V),
            IsTransv (OrbRel (fixZ H (Submodule.span E (Set.range ff))))
              (SigZ H (Submodule.span E (Set.range ff)) (Submodule.span M.L.O (Set.range b))) Rs →
            massOf (fixZ H (Submodule.span E (Set.range ff))) K Rs =
              ENNReal.ofReal (κ * ((idx M ff b : ℝ) ^ (Module.finrank E V - m))⁻¹ * dl H Λs ϖ (H.gram b))

end PI.SelfDualHermitianLattices

end
end

section
noncomputable section

open scoped Classical
open ValuativeRel

namespace PI.SelfDualHermitianLattices

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict

section Ler

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

def tupMul {m : ℕ} (y : Fin m → V) (A : Matrix (Fin m) (Fin m) M.L.O) : Fin m → V :=
  fun a => ∑ i, ((A i a : M.L.O) : E) • y i

def lerCnt (H : HermSp M V) (Λs : Submodule M.L.O V) (ϖ : 𝒪[F]) (J : ℕ) {m : ℕ}
    (A : Matrix (Fin m) (Fin m) M.L.O) (Gm : Matrix (Fin m) (Fin m) E) : ℕ :=
  Nat.card {c : Fin m → (Λs ⧸ piIn H (ϖ ^ J) Λs) //
    ∃ x y : Fin m → Λs, (∀ a, Submodule.Quotient.mk (x a) = c a) ∧ PrimTup H Λs y ∧
      (fun a => (x a : V)) = tupMul (fun i => (y i : V)) A ∧ GramCong H (ϖ ^ J) (fun a => (x a : V)) Gm}

def ler (H : HermSp M V) (Λs : Submodule M.L.O V) (ϖ : 𝒪[F]) (J : ℕ) {m : ℕ}
    (A : Matrix (Fin m) (Fin m) M.L.O) (Gm : Matrix (Fin m) (Fin m) E) : ℝ :=
  (lerCnt H Λs ϖ J A Gm : ℝ) / (qF F : ℝ) ^ (J * (2 * Module.finrank E V * m - m ^ 2))

end Ler

def LatticeUnfoldingLerayVolume : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (m : ℕ) (ff : Fin m → V),
      IsUnit (H.gram ff).det →
      ∀ (Λs : Submodule M.L.O V), IsSelfDual H Λs → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ K : Subgroup (V ≃ₗ[E] V), K ≤ fixZ H (Submodule.span E (Set.range ff)) →
        Commens K (fixZ H (Submodule.span E (Set.range ff)) ⊓ Aut Λs) →
      ∃ κ : ℝ, 0 < κ ∧
        ∀ (b : Fin m → V) (A : Matrix (Fin m) (Fin m) M.L.O), (∀ a, b a ∈ Submodule.span E (Set.range ff)) →
          ff = tupMul b A →
          ∀ Rs : Set (Submodule M.L.O V),
            IsTransv (OrbRel (fixZ H (Submodule.span E (Set.range ff))))
              (SigZ H (Submodule.span E (Set.range ff)) (Submodule.span M.L.O (Set.range b))) Rs →
            ∃ J0 : ℕ, ∀ J, J0 ≤ J →
              massOf (fixZ H (Submodule.span E (Set.range ff))) K Rs =
                ENNReal.ofReal (κ * ler H Λs ϖ J A (H.gram ff))

def LatticeRescalingMassFormula : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (m : ℕ) (ff : Fin m → V),
      IsUnit (H.gram ff).det →
      ∀ (Λs : Submodule M.L.O V), IsSelfDual H Λs → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ (b : Fin m → V) (A : Matrix (Fin m) (Fin m) M.L.O), ff = tupMul b A →
        ∃ J0 : ℕ, ∀ J, J0 ≤ J →
          ler H Λs ϖ J A (H.gram ff) = ((idx M ff b : ℝ) ^ (Module.finrank E V - m))⁻¹ * dl H Λs ϖ (H.gram b)

end PI.SelfDualHermitianLattices

end
end

section
noncomputable section

open scoped Classical
set_option linter.style.haveILetI false
open ValuativeRel

namespace PI.SelfDualHermitianLattices.Hd

open Formalism.MainNotions.S.Loc

section Alg

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem locE_nontrivial (L : LocE F E) : Nontrivial E := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have := L.rank
  rw [Module.finrank_zero_of_subsingleton] at this
  omega


theorem locE_algMap_mem (L : LocE F E) [IsNonarchimedeanLocalField F] {f : F} :
    algebraMap F E f ∈ L.O ↔ f ∈ 𝒪[F] := by
  haveI := locE_nontrivial L
  rw [L.O_def]
  constructor
  · intro h
    have h' : IsIntegral 𝒪[F] f :=
      (isIntegral_algHom_iff ((Algebra.ofId F E).restrictScalars 𝒪[F])
        (algebraMap F E).injective).mp h
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h'
    rw [← hy]; exact y.2
  · intro h
    have : algebraMap F E f = algebraMap 𝒪[F] E ⟨f, h⟩ := by
      rw [IsScalarTower.algebraMap_apply 𝒪[F] F E]; rfl
    rw [this]; exact isIntegral_algebraMap



end Alg

section Alg2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]


structure QBasis (L : LocE F E) where
  ω : E
  hω : ω ∈ L.O
  hnot : ω ∉ Set.range (algebraMap F E)
  t : 𝒪[F]
  n : 𝒪[F]
  hcj : L.cj ω = algebraMap F E (t : F) - ω
  hn : ω * L.cj ω = algebraMap F E (n : F)
  span : ∀ x ∈ L.O, ∃ a b : 𝒪[F], x = algebraMap F E (a : F) + algebraMap F E (b : F) * ω

theorem QBasis.sq {L : LocE F E} (Q : QBasis L) :
    Q.ω * Q.ω = algebraMap F E (Q.t : F) * Q.ω - algebraMap F E (Q.n : F) := by
  have := Q.hn; rw [Q.hcj] at this; rw [← this]; ring


end Alg2

section Alg3

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem exists_a_mod [IsNonarchimedeanLocalField F] (t n : 𝒪[F]) (hΔ : t * t - 4 * n ∈ 𝓂[F]) :
    ∃ a : 𝒪[F], t + 2 * a ∈ 𝓂[F] ∧ a * a - n ∈ 𝓂[F] := by
  by_cases h2 : IsUnit (2 : 𝒪[F])
  · obtain ⟨u, hu⟩ := h2
    have hmul : (u : 𝒪[F]) * ↑u⁻¹ = 1 := u.mul_inv
    refine ⟨-(t * ↑u⁻¹), ?_, ?_⟩
    · have : t + 2 * -(t * ↑u⁻¹) = 0 := by
        linear_combination (-t) * hmul + (t * ↑u⁻¹) * hu
      rw [this]; exact zero_mem _
    · have : -(t * ↑u⁻¹) * -(t * ↑u⁻¹) - n = ↑u⁻¹ * ↑u⁻¹ * (t * t - 4 * n) := by
        linear_combination (n * ((u : 𝒪[F]) * ↑u⁻¹ + 1)) * hmul +
          (-(n * ↑u⁻¹ * ↑u⁻¹ * ((u : 𝒪[F]) + 2))) * hu
      rw [this]; exact Ideal.mul_mem_left _ _ hΔ
  · have h2m : (2 : 𝒪[F]) ∈ 𝓂[F] := (IsLocalRing.mem_maximalIdeal _).mpr h2
    have htt : t * t ∈ 𝓂[F] := by
      have : t * t = (t * t - 4 * n) + 2 * (2 * n) := by ring
      rw [this]; exact add_mem hΔ (Ideal.mul_mem_right _ _ h2m)
    have ht : t ∈ 𝓂[F] := by
      rcases (IsLocalRing.maximalIdeal.isMaximal 𝒪[F]).isPrime.mem_or_mem htt with h | h <;> exact h
    have h2k : (2 : 𝓀[F]) = 0 := by
      have := (IsLocalRing.residue_eq_zero_iff (2 : 𝒪[F])).mpr h2m
      rwa [map_ofNat] at this
    have hinj : Function.Injective (fun x : 𝓀[F] => x * x) := by
      intro x y hxy
      simp only at hxy
      have h1 : (x + y) * (x + y) = 0 := by
        linear_combination (-1 : 𝓀[F]) * hxy + (x * x + x * y) * h2k
      have h3 : x + y = 0 := mul_self_eq_zero.mp h1
      linear_combination h3 - y * h2k
    obtain ⟨r, hr⟩ := (Finite.injective_iff_surjective.mp hinj) (IsLocalRing.residue 𝒪[F] n)
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective r
    refine ⟨a, add_mem ht (Ideal.mul_mem_right _ _ h2m), ?_⟩
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_mul, ha]
    simp only at hr; rw [hr, sub_self]

variable (L : LocE F E) [IsNonarchimedeanLocalField F]

theorem QBasis.normE {L : LocE F E} (Q : QBasis L) (a b : F) :
    (algebraMap F E a + algebraMap F E b * Q.ω) * L.cj (algebraMap F E a + algebraMap F E b * Q.ω) =
      algebraMap F E (a * a + (Q.t : F) * a * b + (Q.n : F) * b * b) := by
  have hn := Q.hn
  rw [Q.hcj] at hn
  rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, Q.hcj]
  simp only [map_add, map_mul]
  linear_combination (algebraMap F E b * algebraMap F E b) * hn

theorem QBasis.disc_unit {L : LocE F E} (Q : QBasis L) : IsUnit (Q.t * Q.t - 4 * Q.n) := by
  by_contra hΔ
  have hΔm : Q.t * Q.t - 4 * Q.n ∈ 𝓂[F] := (IsLocalRing.mem_maximalIdeal _).mpr hΔ
  obtain ⟨a, h1, h2⟩ := exists_a_mod Q.t Q.n hΔm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  rw [hϖ.maximalIdeal_eq] at h1 h2
  obtain ⟨p1, hp1⟩ := Ideal.mem_span_singleton'.mp h1
  obtain ⟨p2, hp2⟩ := Ideal.mem_span_singleton'.mp h2
  have e1 : algebraMap F E (p1 : F) * algebraMap F E (ϖ : F) =
      algebraMap F E (Q.t : F) + 2 * algebraMap F E (a : F) := by
    have e1F : (p1 : F) * (ϖ : F) = (Q.t : F) + 2 * (a : F) := by
      have := congrArg Subtype.val hp1; push_cast at this; exact this
    rw [← map_mul, e1F, map_add, map_mul, map_ofNat]
  have e2 : algebraMap F E (p2 : F) * algebraMap F E (ϖ : F) =
      algebraMap F E (a : F) * algebraMap F E (a : F) - algebraMap F E (Q.n : F) := by
    have e2F : (p2 : F) * (ϖ : F) = (a : F) * (a : F) - (Q.n : F) := by
      have := congrArg Subtype.val hp2; push_cast at this; exact this
    rw [← map_mul, e2F, map_sub, map_mul]
  set y := Q.ω + algebraMap F E (a : F) with hy
  have hyO : y ∈ L.O := add_mem Q.hω ((locE_algMap_mem L).mpr a.2)
  have hsq : y * y = algebraMap F E (p1 : F) * Q.ω * algebraMap F E (ϖ : F) +
      algebraMap F E (p2 : F) * algebraMap F E (ϖ : F) := by
    rw [hy]; linear_combination Q.sq - Q.ω * e1 - e2
  have hmemO : algebraMap F E (p1 : F) * Q.ω + algebraMap F E (p2 : F) ∈ L.O :=
    add_mem (mul_mem ((locE_algMap_mem L).mpr p1.2) Q.hω) ((locE_algMap_mem L).mpr p2.2)
  have hspan : y * y ∈ Submodule.span L.O {algebraMap F E ((ϖ : 𝒪[F]) : F)} := by
    rw [Submodule.mem_span_singleton]
    refine ⟨⟨_, hmemO⟩, ?_⟩
    rw [Subring.smul_def, smul_eq_mul, hsq]; simp only; ring
  have hyd := L.unram ϖ hϖ y hyO (by simpa using hspan)
  obtain ⟨⟨w, hw⟩, hwy⟩ := Submodule.mem_span_singleton.mp hyd
  rw [Subring.smul_def, smul_eq_mul] at hwy
  obtain ⟨a', b', hab'⟩ := Q.span w hw
  have hwy' : w * algebraMap F E (ϖ : F) = y := hwy
  rw [hab'] at hwy'
  apply Q.hnot
  have hne : (1 : F) - (ϖ : F) * (b' : F) ≠ 0 := by
    intro h
    apply hϖ.not_isUnit
    have hm : ϖ * b' = 1 := Subtype.ext (by push_cast; linear_combination -h)
    exact ⟨⟨ϖ, b', hm, by rw [mul_comm]; exact hm⟩, rfl⟩
  refine ⟨((ϖ : F) * (a' : F) - (a : F)) / (1 - (ϖ : F) * (b' : F)), ?_⟩
  have hu : IsUnit (algebraMap F E (1 - (ϖ : F) * (b' : F))) := (IsUnit.mk0 _ hne).map _
  apply hu.mul_left_cancel
  rw [← map_mul, mul_div_cancel₀ _ hne]
  simp only [map_sub, map_mul, map_one]
  rw [hy] at hwy'
  linear_combination hwy'

theorem QBasis.trace_nondeg {L : LocE F E} (Q : QBasis L) {ϖ : 𝒪[F]} {x : E} (hx : x ∈ L.O)
    (h : ∀ c ∈ L.O, ∃ z : 𝒪[F], c * x + L.cj (c * x) = algebraMap F E ((ϖ : F) * (z : F))) :
    ∃ w ∈ L.O, x = algebraMap F E (ϖ : F) * w := by
  haveI := locE_nontrivial L
  obtain ⟨a, b, hab⟩ := Q.span x hx
  obtain ⟨z1, hz1⟩ := h 1 (one_mem _)
  obtain ⟨z2, hz2⟩ := h Q.ω Q.hω
  have hn := Q.hn
  rw [Q.hcj] at hn
  have i1 : (2 * (a : F) + (b : F) * (Q.t : F)) = (ϖ : F) * (z1 : F) := by
    apply (algebraMap F E).injective
    rw [← hz1, one_mul, hab, map_add L.cj, map_mul L.cj, AlgEquiv.commutes, AlgEquiv.commutes, Q.hcj]
    simp only [map_add, map_mul, map_ofNat]; ring
  have i2 : ((a : F) * (Q.t : F) + (b : F) * ((Q.t : F) * (Q.t : F) - 2 * (Q.n : F))) =
      (ϖ : F) * (z2 : F) := by
    apply (algebraMap F E).injective
    rw [← hz2, hab, map_mul L.cj, map_add L.cj, map_mul L.cj, AlgEquiv.commutes, AlgEquiv.commutes, Q.hcj]
    simp only [map_add, map_mul, map_sub, map_ofNat]
    linear_combination (2 * algebraMap F E (b : F)) * hn
  obtain ⟨u, hu⟩ := Q.disc_unit
  have hinv : ((u⁻¹ : (𝒪[F])ˣ) : F) * ((Q.t : F) * (Q.t : F) - 4 * (Q.n : F)) = 1 := by
    have := congrArg (fun z : 𝒪[F] => (z : F)) (u.inv_mul)
    rw [hu] at this; push_cast at this; exact this
  set v : F := ((u⁻¹ : (𝒪[F])ˣ) : F)
  have hv : v ∈ 𝒪[F] := ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]).2
  set al : F := v * (((Q.t : F) * (Q.t : F) - 2 * (Q.n : F)) * (z1 : F) - (Q.t : F) * (z2 : F))
  set be : F := v * (2 * (z2 : F) - (Q.t : F) * (z1 : F))
  have hal : al ∈ 𝒪[F] := mul_mem hv (sub_mem (mul_mem (sub_mem (mul_mem Q.t.2 Q.t.2)
    (mul_mem (by simpa using (2 : 𝒪[F]).2) Q.n.2)) z1.2) (mul_mem Q.t.2 z2.2))
  have hbe : be ∈ 𝒪[F] := mul_mem hv (sub_mem (mul_mem (by simpa using (2 : 𝒪[F]).2) z2.2)
    (mul_mem Q.t.2 z1.2))
  have ha : (a : F) = (ϖ : F) * al := by
    linear_combination (v * ((Q.t : F) * (Q.t : F) - 2 * (Q.n : F))) * i1 + (-(v * (Q.t : F))) * i2 +
      (-(a : F)) * hinv
  have hb : (b : F) = (ϖ : F) * be := by
    linear_combination (-(v * (Q.t : F))) * i1 + (2 * v) * i2 + (-(b : F)) * hinv
  refine ⟨algebraMap F E al + algebraMap F E be * Q.ω,
    add_mem ((locE_algMap_mem L).mpr hal) (mul_mem ((locE_algMap_mem L).mpr hbe) Q.hω), ?_⟩
  rw [hab, ha, hb]; simp only [map_mul]; ring

end Alg3

end PI.SelfDualHermitianLattices.Hd
end
end

section
noncomputable section

open scoped Classical
open ValuativeRel

namespace PI.SelfDualHermitianLattices

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict

def SelfDualLatticesOneOrbit : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (Λ₁ Λ₂ : Submodule M.L.O V),
      IsSelfDual H Λ₁ → IsSelfDual H Λ₂ →
      ∃ g : V ≃ₗ[E] V, IsUnitary H g ∧ img g Λ₁ = Λ₂

end PI.SelfDualHermitianLattices
end
end

section
noncomputable section

open scoped Classical
open ValuativeRel

namespace PI.SelfDualHermitianLattices

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict

namespace Hg

section TupDefs

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

def UGrp (H : HermSp M V) : Subgroup (V ≃ₗ[E] V) where
  carrier := {g | IsUnitary H g}
  mul_mem' {a b} ha hb x y := by
    change H.h (a (b x)) (a (b y)) = H.h x y
    rw [ha (b x) (b y), hb x y]
  one_mem' x y := rfl
  inv_mem' {a} ha x y := by
    have h1 : ∀ v, a (a⁻¹ v) = v := fun v => by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
    change H.h (a⁻¹ x) (a⁻¹ y) = H.h x y
    rw [← ha (a⁻¹ x) (a⁻¹ y), h1, h1]

def FixT {m : ℕ} (x : Fin m → V) : Subgroup (V ≃ₗ[E] V) where
  carrier := {g | ∀ a, g (x a) = x a}
  mul_mem' {a b} ha hb i := by
    change a (b (x i)) = x i
    rw [hb i, ha i]
  one_mem' _ := rfl
  inv_mem' {a} ha i := by
    change a⁻¹ (x i) = x i
    conv_lhs => rw [← ha i]
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl

def StabT (H : HermSp M V) {m : ℕ} (x : Fin m → V) : Subgroup (V ≃ₗ[E] V) := UGrp H ⊓ FixT x

def KsOf (H : HermSp M V) (Λs : Submodule M.L.O V) : Subgroup (V ≃ₗ[E] V) := UGrp H ⊓ Aut Λs

def actT {m : ℕ} (g : V ≃ₗ[E] V) (x : Fin m → V) : Fin m → V := fun a => g (x a)

def KsRel (H : HermSp M V) (Λs : Submodule M.L.O V) {m : ℕ} (x x' : Fin m → V) : Prop :=
  ∃ k ∈ KsOf H Λs, actT k x = x'

def XS (H : HermSp M V) (Λs : Submodule M.L.O V) {m : ℕ} (ff : Fin m → V)
    (A : Matrix (Fin m) (Fin m) M.L.O) : Set (Fin m → V) :=
  {x | H.gram x = H.gram ff ∧ ∃ y : Fin m → Λs, PrimTup H Λs y ∧ x = tupMul (fun i => (y i : V)) A}

def conjSub (g : V ≃ₗ[E] V) (K : Subgroup (V ≃ₗ[E] V)) : Subgroup (V ≃ₗ[E] V) :=
  K.comap (MulAut.conj g).toMonoidHom

end TupDefs

end Hg

open Hg

def WittT : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (m : ℕ) (x x' : Fin m → V),
      IsUnit (H.gram x).det → H.gram x = H.gram x' →
      ∃ g : V ≃ₗ[E] V, IsUnitary H g ∧ ∀ a, g (x a) = x' a

def SatPrim : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (Λ : Submodule M.L.O V), IsSelfDual H Λ →
      ∀ (m : ℕ) (y : Fin m → Λ), IsUnit (H.gram (fun a => (y a : V))).det →
        Λ ⊓ (Submodule.span E (Set.range (fun a => (y a : V)))).restrictScalars M.L.O =
          Submodule.span M.L.O (Set.range (fun a => (y a : V))) →
        PrimTup H Λ y

def LVX : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (m : ℕ) (ff : Fin m → V),
      IsUnit (H.gram ff).det →
      ∀ (Λs : Submodule M.L.O V), IsSelfDual H Λs → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ K : Subgroup (V ≃ₗ[E] V), K ≤ fixZ H (Submodule.span E (Set.range ff)) →
        Commens K (fixZ H (Submodule.span E (Set.range ff)) ⊓ Aut Λs) →
      ∃ κ : ℝ, 0 < κ ∧
        ∀ (b : Fin m → V) (A : Matrix (Fin m) (Fin m) M.L.O), (∀ a, b a ∈ Submodule.span E (Set.range ff)) →
          ff = tupMul b A →
          ∀ Xs : Set (Fin m → V), IsTransv (KsRel H Λs) (XS H Λs ff A) Xs →
          ∀ gx : (Fin m → V) → (V ≃ₗ[E] V), (∀ x ∈ Xs, IsUnitary H (gx x) ∧ actT (gx x) x = ff) →
            ∃ J0 : ℕ, ∀ J, J0 ≤ J →
              (∑' x : Xs, ENNReal.ofReal (1 / volRel (StabT H (x : Fin m → V) ⊓ KsOf H Λs)
                  (conjSub (gx x) K))) =
                ENNReal.ofReal (κ * ler H Λs ϖ J A (H.gram ff))

end PI.SelfDualHermitianLattices
end
end
