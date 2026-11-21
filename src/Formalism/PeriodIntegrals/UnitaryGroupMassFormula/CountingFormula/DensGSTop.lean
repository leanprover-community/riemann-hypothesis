import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGS

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Classical ValuativeRel

section Dvr

variable (F : Type) [Field F] [ValuativeRel F]

def resF (x : F) : 𝓀[F] := if h : x ∈ 𝒪[F] then IsLocalRing.residue 𝒪[F] ⟨x, h⟩ else 0

def liftF (c : 𝓀[F]) : F := ((IsLocalRing.residue_surjective c).choose : 𝒪[F])

theorem resF_coe (o : 𝒪[F]) : resF F (o : F) = IsLocalRing.residue 𝒪[F] o := by
  rw [resF, dif_pos o.2]

theorem liftF_mem (c : 𝓀[F]) : liftF F c ∈ 𝒪[F] :=
  (IsLocalRing.residue_surjective c).choose.2

theorem resF_liftF (c : 𝓀[F]) : resF F (liftF F c) = c := by
  rw [liftF, resF_coe]
  exact (IsLocalRing.residue_surjective c).choose_spec

theorem resF_one : resF F 1 = 1 := by
  simpa using resF_coe F 1

theorem resF_mul {x y : F} (hx : x ∈ 𝒪[F]) (hy : y ∈ 𝒪[F]) : resF F (x * y) = resF F x * resF F y := by
  have h := resF_coe F (⟨x, hx⟩ * ⟨y, hy⟩)
  rw [map_mul, ← resF_coe F ⟨x, hx⟩, ← resF_coe F ⟨y, hy⟩] at h
  exact h

theorem resF_sum_mul {ι : Type} [Fintype ι] (c x : ι → F) (hc : ∀ i, c i ∈ 𝒪[F]) (hx : ∀ i, x i ∈ 𝒪[F]) :
    resF F (∑ i, c i * x i) = ∑ i, resF F (c i) * resF F (x i) := by
  have hs : ((∑ i, (⟨c i, hc i⟩ : 𝒪[F]) * ⟨x i, hx i⟩ : 𝒪[F]) : F) = ∑ i, c i * x i := by
    simp
  rw [← hs, resF_coe, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← resF_coe F ⟨c i, hc i⟩, ← resF_coe F ⟨x i, hx i⟩]

theorem resF_eq_zero_of_lt {x : F} (hx : valuation F x < 1) : resF F x = 0 := by
  have hx1 : x ∈ 𝒪[F] := (Valuation.mem_integer_iff _ _).2 hx.le
  rw [show x = ((⟨x, hx1⟩ : 𝒪[F]) : F) from rfl, resF_coe, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers _).isUnit_iff_valuation_eq_one]
  exact hx.ne

theorem dvd_of_resF_eq_zero [IsDiscreteValuationRing 𝒪[F]] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {x : F}
    (hx : x ∈ 𝒪[F]) (h0 : resF F x = 0) : ∃ o : 𝒪[F], x = (ϖ : F) * o := by
  rw [show x = ((⟨x, hx⟩ : 𝒪[F]) : F) from rfl, resF_coe, IsLocalRing.residue_eq_zero_iff,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton'] at h0
  obtain ⟨a, ha⟩ := h0
  refine ⟨a, ?_⟩
  rw [show x = ((⟨x, hx⟩ : 𝒪[F]) : F) from rfl, ← ha]
  push_cast
  ring

theorem resF_irr {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) : resF F (ϖ : F) = 0 := by
  rw [resF_coe, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact hϖ.not_isUnit

def SatF {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) : Prop :=
  ∀ u : Fin n → F, (∀ k, u k ∈ 𝒪[F]) → (∃ c : ι → F, ∑ i, c i • X i = u) →
    ∃ c : ι → F, (∀ i, c i ∈ 𝒪[F]) ∧ ∑ i, c i • X i = u

def redM {ι : Type} {n : ℕ} (X : ι → Fin n → F) : ι → Fin n → 𝓀[F] := fun i k => resF F (X i k)

variable {F}

theorem key_norm {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) (hX : ∀ i k, X i k ∈ 𝒪[F])
    (hred : LinearIndependent 𝓀[F] (redM F X)) (c : ι → F) (u : Fin n → F) (hu : ∑ i, c i • X i = u)
    (j : ι) (hj : ∀ i, valuation F (c i) ≤ valuation F (c j)) (hcj : c j ≠ 0)
    (hlt : ∀ k, valuation F (u k) < valuation F (c j)) : False := by
  have hvj : 0 < valuation F (c j) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hcj)
  have hd : ∀ i, c i / c j ∈ 𝒪[F] := fun i =>
    (Valuation.mem_integer_iff _ _).2 (by rw [map_div₀]; exact (div_le_one₀ hvj).2 (hj i))
  have hz : ∑ i, resF F (c i / c j) • redM F X i = 0 := by
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, redM, Pi.zero_apply]
    have h := resF_sum_mul F (fun i => c i / c j) (fun i => X i k) hd (fun i => hX i k)
    rw [← h]
    apply resF_eq_zero_of_lt F
    have hs : ∑ i, c i / c j * X i k = u k / c j := by
      rw [← hu, Finset.sum_apply, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hs, map_div₀]
    exact (div_lt_one₀ hvj).2 (hlt k)
  have h1 := (Fintype.linearIndependent_iff.1 hred) _ hz j
  rw [div_self hcj, resF_one] at h1
  exact one_ne_zero h1

theorem indep_of_red {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) (hX : ∀ i k, X i k ∈ 𝒪[F])
    (hred : LinearIndependent 𝓀[F] (redM F X)) : LinearIndependent F X := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push_neg at hne
  obtain ⟨i0, hi0⟩ := hne
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => valuation F (g i))
    ⟨i0, Finset.mem_univ _⟩
  have hcj : g j ≠ 0 := by
    intro h
    have h2 := hj i0 (Finset.mem_univ _)
    rw [h, map_zero] at h2
    exact hi0 ((Valuation.zero_iff _).1 (le_antisymm h2 zero_le'))
  refine key_norm X hX hred g 0 hg j (fun i => hj i (Finset.mem_univ _)) hcj (fun k => ?_)
  rw [Pi.zero_apply, map_zero]
  exact zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hcj)

theorem sat_of_red {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) (hX : ∀ i k, X i k ∈ 𝒪[F])
    (hred : LinearIndependent 𝓀[F] (redM F X)) : SatF F X := by
  intro u hu hex
  obtain ⟨c, hc⟩ := hex
  refine ⟨c, fun i => ?_, hc⟩
  by_contra hci
  rw [Valuation.mem_integer_iff, not_le] at hci
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => valuation F (c i))
    ⟨i, Finset.mem_univ _⟩
  have hj1 : 1 < valuation F (c j) := lt_of_lt_of_le hci (hj i (Finset.mem_univ _))
  have hcj : c j ≠ 0 := by
    intro h
    rw [h, map_zero] at hj1
    exact not_lt.2 zero_le' hj1
  exact key_norm X hX hred c u hc j (fun i => hj i (Finset.mem_univ _)) hcj
    (fun k => lt_of_le_of_lt ((Valuation.mem_integer_iff _ _).1 (hu k)) hj1)

theorem red_of_indep_sat [IsDiscreteValuationRing 𝒪[F]] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) (hX : ∀ i k, X i k ∈ 𝒪[F])
    (hind : LinearIndependent F X) (hsat : SatF F X) : LinearIndependent 𝓀[F] (redM F X) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  obtain ⟨d, hdm, hres⟩ : ∃ d : ι → F, (∀ i, d i ∈ 𝒪[F]) ∧ ∀ i, resF F (d i) = a i :=
    ⟨fun i => liftF F (a i), fun i => liftF_mem F _, fun i => resF_liftF F _⟩
  have hcomp : ∀ k, (∑ i, d i • X i) k = ∑ i, d i * X i k := fun k => by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hmem : ∀ k, (∑ i, d i • X i) k ∈ 𝒪[F] := fun k => by
    rw [hcomp]
    exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (hdm i) (hX i k)
  have hr0 : ∀ k, resF F ((∑ i, d i • X i) k) = 0 := fun k => by
    have h := resF_sum_mul F d (fun i => X i k) hdm (fun i => hX i k)
    rw [hcomp, h]
    simp only [hres]
    have h2 := congrFun ha k
    simpa [Finset.sum_apply, redM] using h2
  choose w hw using fun k => dvd_of_resF_eq_zero F hϖ (hmem k) (hr0 k)
  have hϖ0 : (ϖ : F) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  obtain ⟨c', hc'm, hc'⟩ := hsat (fun k => (w k : F)) (fun k => (w k).2)
    ⟨fun i => d i / ϖ, by
      funext k
      have e := hw k
      rw [hcomp] at e
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      simp_rw [div_mul_eq_mul_div]
      rw [← Finset.sum_div, e]
      field_simp⟩
  have hzero : ∑ i, (d i - ϖ * c' i) • X i = 0 := by
    funext k
    have e1 := congrFun hc' k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at e1
    have e2 := hw k
    rw [hcomp] at e2
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
      Pi.zero_apply]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, e1, e2, sub_self]
  have hdi := (Fintype.linearIndependent_iff.1 hind) _ hzero i
  rw [← hres i, sub_eq_zero.1 hdi, resF_mul F ϖ.2 (hc'm i), resF_irr F hϖ, zero_mul]

theorem dvr_prim_iff [IsDiscreteValuationRing 𝒪[F]] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) (hX : ∀ i k, X i k ∈ 𝒪[F]) :
    (LinearIndependent F X ∧ SatF F X) ↔ LinearIndependent 𝓀[F] (redM F X) :=
  ⟨fun h => red_of_indep_sat hϖ X hX h.1 h.2, fun h => ⟨indep_of_red X hX h, sat_of_red X hX h⟩⟩

end Dvr

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S
open Classical ValuativeRel

section Coord

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]

def InP (ϖ : 𝒪[F]) (u : F) : Prop := ∃ o : 𝒪[F], u = (ϖ : F) * o

theorem e_alg (e : E ≃ₐ[F] F × F) (c : F) : e (algebraMap F E c) = (c, c) := by
  first
  | (rw [e.commutes]; rfl)
  | simp [e.commutes]

theorem pi_smulF (e : E ≃ₐ[F] F × F) {n : ℕ} (π : V ≃+ (Fin n → F) × (Fin n → F))
    (hπ : ∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2)) (c : F) (x : V) :
    π (algebraMap F E c • x) = (c • (π x).1, c • (π x).2) := by
  rw [hπ, e_alg]

theorem mem_smulLat_iff' (H : Loc.HermSp M V) (Λ : Submodule M.L.O V) (c : E) (x : V) :
    x ∈ H.smulLat c Λ ↔ ∃ y ∈ Λ, x = c • y := by
  unfold Loc.HermSp.smulLat
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      exact ⟨y, hy, rfl⟩
    | zero => exact ⟨0, Λ.zero_mem, (smul_zero c).symm⟩
    | add z w _ _ hz hw =>
      obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨y', hy', rfl⟩ := hw
      exact ⟨y + y', Λ.add_mem hy hy', (smul_add c y y').symm⟩
    | smul a z _ hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      refine ⟨a • y, Λ.smul_mem a hy, ?_⟩
      first
      | exact smul_comm a c y
      | exact (smul_comm c a y).symm
      | (show ((a : E)) • c • y = c • ((a : E) • y); exact smul_comm _ _ _)
  · rintro ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨y, hy, rfl⟩

theorem mem_smulLat_coord (e : E ≃ₐ[F] F × F) (H : Loc.HermSp M V) (Λ : Submodule M.L.O V) {n : ℕ}
    (π : V ≃+ (Fin n → F) × (Fin n → F))
    (hπa : ∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2))
    (hπL : ∀ x : V, x ∈ Λ ↔ (∀ k, (π x).1 k ∈ 𝒪[F]) ∧ ∀ k, (π x).2 k ∈ 𝒪[F]) (ϖ : 𝒪[F]) (x : V) :
    x ∈ H.smulLat (algebraMap F E ϖ) Λ ↔ (∀ k, InP ϖ ((π x).1 k)) ∧ ∀ k, InP ϖ ((π x).2 k) := by
  rw [mem_smulLat_iff']
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [pi_smulF e π hπa]
    obtain ⟨h1, h2⟩ := (hπL y).1 hy
    exact ⟨fun k => ⟨⟨_, h1 k⟩, by simp [Pi.smul_apply, smul_eq_mul]⟩,
      fun k => ⟨⟨_, h2 k⟩, by simp [Pi.smul_apply, smul_eq_mul]⟩⟩
  · rintro ⟨h1, h2⟩
    choose o1 ho1 using h1
    choose o2 ho2 using h2
    refine ⟨π.symm ((fun k => (o1 k : F)), (fun k => (o2 k : F))), ?_, ?_⟩
    · rw [hπL, AddEquiv.apply_symm_apply]
      exact ⟨fun k => (o1 k).2, fun k => (o2 k).2⟩
    · apply π.injective
      rw [pi_smulF e π hπa, AddEquiv.apply_symm_apply]
      ext k <;> simp [ho1, ho2, Pi.smul_apply, smul_eq_mul]

theorem inP_sub_iff [IsDiscreteValuationRing 𝒪[F]] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {u w : F}
    (hu : u ∈ 𝒪[F]) (hw : w ∈ 𝒪[F]) : InP ϖ (u - w) ↔ resF F u = resF F w := by
  have key : ∀ d : 𝒪[F], InP ϖ (d : F) ↔ ϖ ∣ d := by
    intro d
    constructor
    · rintro ⟨o, ho⟩
      exact ⟨o, Subtype.ext (by simp [ho])⟩
    · rintro ⟨o, rfl⟩
      exact ⟨o, by simp⟩
  have e1 : resF F u = IsLocalRing.residue 𝒪[F] ⟨u, hu⟩ := by
    first
    | simp [resF, hu]
    | (unfold resF; rw [dif_pos hu])
  have e2 : resF F w = IsLocalRing.residue 𝒪[F] ⟨w, hw⟩ := by
    first
    | simp [resF, hw]
    | (unfold resF; rw [dif_pos hw])
  have hs : (u - w : F) = ((⟨u, hu⟩ - ⟨w, hw⟩ : 𝒪[F]) : F) := rfl
  have hm : IsLocalRing.maximalIdeal 𝒪[F] = Ideal.span {ϖ} := by
    first
    | exact hϖ.maximalIdeal_eq
    | exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hϖ
  rw [e1, e2, hs, key, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hm, Ideal.mem_span_singleton]

theorem mk_eq_iff [IsDiscreteValuationRing 𝒪[F]] (e : E ≃ₐ[F] F × F) (H : Loc.HermSp M V)
    (Λ : Submodule M.L.O V) {n : ℕ} (π : V ≃+ (Fin n → F) × (Fin n → F))
    (hπa : ∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2))
    (hπL : ∀ x : V, x ∈ Λ ↔ (∀ k, (π x).1 k ∈ 𝒪[F]) ∧ ∀ k, (π x).2 k ∈ 𝒪[F]) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    Submodule.Quotient.mk (p := H.smulLat (algebraMap F E ϖ) Λ) x =
        Submodule.Quotient.mk (p := H.smulLat (algebraMap F E ϖ) Λ) y ↔
      (∀ k, resF F ((π x).1 k) = resF F ((π y).1 k)) ∧ ∀ k, resF F ((π x).2 k) = resF F ((π y).2 k) := by
  rw [Submodule.Quotient.eq, mem_smulLat_coord e H Λ π hπa hπL ϖ]
  obtain ⟨hx1, hx2⟩ := (hπL x).1 hx
  obtain ⟨hy1, hy2⟩ := (hπL y).1 hy
  simp only [map_sub, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply]
  exact and_congr (forall_congr' fun k => inP_sub_iff hϖ (hx1 k) (hy1 k))
    (forall_congr' fun k => inP_sub_iff hϖ (hx2 k) (hy2 k))

theorem mem_span_irr_iff (e : E ≃ₐ[F] F × F)
    (hO : ∀ x : E, x ∈ M.L.O ↔ (e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F]) (ϖ : 𝒪[F]) (z : E) :
    z ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)} ↔ InP ϖ (e z).1 ∧ InP ϖ (e z).2 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    have ha := (hO a).1 a.2
    refine ⟨⟨⟨(e a).1, ha.1⟩, ?_⟩, ⟨⟨(e a).2, ha.2⟩, ?_⟩⟩ <;>
      simp [Subring.smul_def, Submonoid.smul_def, Subalgebra.smul_def, map_mul, e_alg, mul_comm]
  · rintro ⟨⟨o1, h1⟩, ⟨o2, h2⟩⟩
    have hmem : e.symm ((o1 : F), (o2 : F)) ∈ M.L.O := by
      rw [hO, AlgEquiv.apply_symm_apply]
      exact ⟨o1.2, o2.2⟩
    refine ⟨⟨_, hmem⟩, ?_⟩
    apply e.injective
    ext <;> simp [Subring.smul_def, Submonoid.smul_def, Subalgebra.smul_def, map_mul, e_alg, h1, h2, mul_comm]

theorem resF_bil {n : ℕ} (x y : Fin n → F) (hx : ∀ k, x k ∈ 𝒪[F]) (hy : ∀ k, y k ∈ 𝒪[F])
    (Ph : Matrix (Fin n) (Fin n) 𝒪[F]) :
    resF F (∑ k, ∑ l, x k * (Ph k l : F) * y l) =
      ∑ k, ∑ l, resF F (x k) * IsLocalRing.residue 𝒪[F] (Ph k l) * resF F (y l) := by
  have hc : ∀ (a : F) (ha : a ∈ 𝒪[F]), resF F a = IsLocalRing.residue 𝒪[F] ⟨a, ha⟩ := by
    intro a ha
    first
    | simp [resF, ha]
    | (unfold resF; rw [dif_pos ha])
  have hsum : (∑ k, ∑ l, x k * (Ph k l : F) * y l) =
      ((∑ k, ∑ l, (⟨x k, hx k⟩ : 𝒪[F]) * Ph k l * (⟨y l, hy l⟩ : 𝒪[F]) : 𝒪[F]) : F) := by
    first
    | (push_cast; rfl)
    | (simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul]; rfl)
    | (simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul])
    | (push_cast; simp)
    | simp
  have hxk : ∀ k, resF F (x k) = IsLocalRing.residue 𝒪[F] ⟨x k, hx k⟩ := fun k => hc _ (hx k)
  have hyl : ∀ l, resF F (y l) = IsLocalRing.residue 𝒪[F] ⟨y l, hy l⟩ := fun l => hc _ (hy l)
  have hc' : ∀ z : 𝒪[F], resF F (z : F) = IsLocalRing.residue 𝒪[F] z := fun z => hc z z.2
  rw [hsum, hc']
  simp only [map_sum, map_mul, hxk, hyl]

theorem bil_mem {n : ℕ} (x y : Fin n → F) (hx : ∀ k, x k ∈ 𝒪[F]) (hy : ∀ k, y k ∈ 𝒪[F])
    (Ph : Matrix (Fin n) (Fin n) 𝒪[F]) : (∑ k, ∑ l, x k * (Ph k l : F) * y l) ∈ 𝒪[F] := by
  exact sum_mem fun k _ => sum_mem fun l _ => mul_mem (mul_mem (hx k) (Ph k l).2) (hy l)

end Coord

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S
open Classical ValuativeRel

section Coord2

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]

theorem gram_iff [IsDiscreteValuationRing 𝒪[F]] (e : E ≃ₐ[F] F × F)
    (hes : ∀ x, e (M.L.cj x) = (e x).swap)
    (hO : ∀ x : E, x ∈ M.L.O ↔ (e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F]) (H : Loc.HermSp M V)
    (Λ : Submodule M.L.O V) {n : ℕ} (π : V ≃+ (Fin n → F) × (Fin n → F)) (Ph : Matrix (Fin n) (Fin n) 𝒪[F])
    (hπ : IsSplitCoord e H Λ π Ph) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {ι : Type} [Fintype ι] (G₀ : Matrix ι ι E)
    (h1 : ∀ a b, G₀ a b ∈ M.L.O) (h2 : ∀ a b, G₀ b a = M.L.cj (G₀ a b)) (v : ι → V) (hv : ∀ a, v a ∈ Λ) :
    (∀ a b, H.h (v b) (v a) - G₀ a b ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)}) ↔
      ∀ a b, resF F (∑ k, ∑ l, (π (v b)).1 k * (Ph k l : F) * (π (v a)).2 l) = resF F ((e (G₀ a b)).1) := by
  have hform := hπ.2.2.2
  have hL := fun a => (hπ.2.1 (v a)).1 (hv a)
  have hc : ∀ a b, InP ϖ (e (H.h (v b) (v a) - G₀ a b)).1 ↔
      resF F (∑ k, ∑ l, (π (v b)).1 k * (Ph k l : F) * (π (v a)).2 l) = resF F ((e (G₀ a b)).1) := by
    intro a b
    rw [map_sub, Prod.fst_sub, hform]
    exact inP_sub_iff hϖ (bil_mem _ _ (hL b).1 (hL a).2 Ph) ((hO _).1 (h1 a b)).1
  have hc2 : ∀ a b, (e (H.h (v b) (v a) - G₀ a b)).2 = (e (H.h (v a) (v b) - G₀ b a)).1 := by
    intro a b
    have hg : e (G₀ a b) = (e (G₀ b a)).swap := by rw [h2 b a, hes]
    rw [map_sub, map_sub, Prod.snd_sub, Prod.fst_sub, hform, hform, hg]
    rfl
  constructor
  · intro h a b
    exact (hc a b).1 ((mem_span_irr_iff e hO ϖ _).1 (h a b)).1
  · intro h a b
    rw [mem_span_irr_iff e hO ϖ]
    exact ⟨(hc a b).2 (h a b), by rw [hc2]; exact (hc b a).2 (h b a)⟩

theorem pi_sum (e : E ≃ₐ[F] F × F) {n : ℕ} (π : V ≃+ (Fin n → F) × (Fin n → F))
    (hπa : ∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2))
    {ι : Type} [Fintype ι] (v : ι → V) (c : ι → E) :
    π (∑ i, c i • v i) = (∑ i, (e (c i)).1 • (π (v i)).1, ∑ i, (e (c i)).2 • (π (v i)).2) := by
  rw [map_sum]
  simp only [hπa]
  exact Prod.ext (by simp [Prod.fst_sum]) (by simp [Prod.snd_sum])

theorem prim_iff [IsDiscreteValuationRing 𝒪[F]] (e : E ≃ₐ[F] F × F)
    (hO : ∀ x : E, x ∈ M.L.O ↔ (e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F]) (H : Loc.HermSp M V)
    (Λ : Submodule M.L.O V) {n : ℕ} (π : V ≃+ (Fin n → F) × (Fin n → F))
    (hπa : ∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2))
    (hπL : ∀ x : V, x ∈ Λ ↔ (∀ k, (π x).1 k ∈ 𝒪[F]) ∧ ∀ k, (π x).2 k ∈ 𝒪[F]) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    {ι : Type} [Fintype ι] (v : ι → V) (hv : ∀ a, v a ∈ Λ) :
    H.Prim Λ v ↔ LinearIndependent 𝓀[F] (redM F fun a => (π (v a)).1) ∧
      LinearIndependent 𝓀[F] (redM F fun a => (π (v a)).2) := by
  set X : ι → Fin n → F := fun a => (π (v a)).1 with hXd
  set Y : ι → Fin n → F := fun a => (π (v a)).2 with hYd
  have hX : ∀ a k, X a k ∈ 𝒪[F] := fun a k => ((hπL (v a)).1 (hv a)).1 k
  have hY : ∀ a k, Y a k ∈ 𝒪[F] := fun a k => ((hπL (v a)).1 (hv a)).2 k
  have hsum := pi_sum e π hπa v
  have hpiS : ∀ u w : Fin n → F, π (π.symm (u, w)) = (u, w) := fun u w => AddEquiv.apply_symm_apply _ _

  have hLI : LinearIndependent E v ↔ LinearIndependent F X ∧ LinearIndependent F Y := by
    constructor
    · intro hind
      constructor
      · rw [Fintype.linearIndependent_iff]
        intro c hc i
        have h0 := Fintype.linearIndependent_iff.1 hind (fun i => e.symm (c i, 0)) (by
          apply π.injective
          rw [hsum, map_zero]
          simp only [AlgEquiv.apply_symm_apply, zero_smul, Finset.sum_const_zero]
          ext k
          · simpa [hXd] using congrFun hc k
          · simp) i
        have := congrArg (fun z => (e z).1) h0
        simpa using this
      · rw [Fintype.linearIndependent_iff]
        intro c hc i
        have h0 := Fintype.linearIndependent_iff.1 hind (fun i => e.symm (0, c i)) (by
          apply π.injective
          rw [hsum, map_zero]
          simp only [AlgEquiv.apply_symm_apply, zero_smul, Finset.sum_const_zero]
          ext k
          · simp
          · simpa [hYd] using congrFun hc k) i
        have := congrArg (fun z => (e z).2) h0
        simpa using this
    · rintro ⟨hXi, hYi⟩
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have h0 := congrArg π hc
      rw [hsum, map_zero] at h0
      have a1 := Fintype.linearIndependent_iff.1 hXi (fun i => (e (c i)).1) (congrArg Prod.fst h0) i
      have a2 := Fintype.linearIndependent_iff.1 hYi (fun i => (e (c i)).2) (congrArg Prod.snd h0) i
      apply e.injective
      rw [map_zero]
      exact Prod.ext a1 a2

  have hSat : (∀ x ∈ Λ, x ∈ Submodule.span E (Set.range v) → x ∈ Submodule.span M.L.O (Set.range v)) ↔
      SatF F X ∧ SatF F Y := by
    have hOsum : ∀ d : ι → M.L.O, ∑ i, d i • v i = ∑ i, (d i : E) • v i := fun d => rfl
    constructor
    · intro hs
      constructor
      · rintro u hu ⟨c, hc⟩
        have hxL : π.symm (u, 0) ∈ Λ := (hπL _).2 (by rw [hpiS]; exact ⟨hu, fun k => Subring.zero_mem _⟩)
        have hxs : π.symm (u, 0) ∈ Submodule.span E (Set.range v) := by
          rw [Submodule.mem_span_range_iff_exists_fun]
          refine ⟨fun i => e.symm (c i, 0), ?_⟩
          apply π.injective
          rw [hsum, hpiS]
          simp only [AlgEquiv.apply_symm_apply, zero_smul, Finset.sum_const_zero]
          rw [← hc]
        obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 (hs _ hxL hxs)
        refine ⟨fun i => (e (d i)).1, fun i => ((hO _).1 (d i).2).1, ?_⟩
        have h0 := congrArg (fun z => (π z).1) hd
        simp only [hOsum, hsum, hpiS] at h0
        exact h0
      · rintro u hu ⟨c, hc⟩
        have hxL : π.symm (0, u) ∈ Λ := (hπL _).2 (by rw [hpiS]; exact ⟨fun k => Subring.zero_mem _, hu⟩)
        have hxs : π.symm (0, u) ∈ Submodule.span E (Set.range v) := by
          rw [Submodule.mem_span_range_iff_exists_fun]
          refine ⟨fun i => e.symm (0, c i), ?_⟩
          apply π.injective
          rw [hsum, hpiS]
          simp only [AlgEquiv.apply_symm_apply, zero_smul, Finset.sum_const_zero]
          rw [← hc]
        obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 (hs _ hxL hxs)
        refine ⟨fun i => (e (d i)).2, fun i => ((hO _).1 (d i).2).2, ?_⟩
        have h0 := congrArg (fun z => (π z).2) hd
        simp only [hOsum, hsum, hpiS] at h0
        exact h0
    · rintro ⟨sX, sY⟩ x hx hxs
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hxs
      have hπx := hsum c
      rw [hc] at hπx
      have hxc := (hπL x).1 hx
      obtain ⟨c1, hc1, hs1⟩ := sX (π x).1 hxc.1 ⟨_, (congrArg Prod.fst hπx).symm⟩
      obtain ⟨c2, hc2, hs2⟩ := sY (π x).2 hxc.2 ⟨_, (congrArg Prod.snd hπx).symm⟩
      have hmem : ∀ i, e.symm (c1 i, c2 i) ∈ M.L.O := fun i => by
        rw [hO, AlgEquiv.apply_symm_apply]; exact ⟨hc1 i, hc2 i⟩
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨fun i => ⟨_, hmem i⟩, ?_⟩
      rw [hOsum]
      apply π.injective
      rw [hsum]
      simp only [AlgEquiv.apply_symm_apply]
      exact Prod.ext hs1 hs2
  have hP : H.Prim Λ v ↔ (LinearIndependent F X ∧ LinearIndependent F Y) ∧ (SatF F X ∧ SatF F Y) := by
    unfold Loc.HermSp.Prim
    rw [← hLI, ← hSat]
    exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hv, h.1, h.2⟩⟩
  rw [hP, ← dvr_prim_iff hϖ X hX, ← dvr_prim_iff hϖ Y hY]
  tauto

end Coord2

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S
open Classical ValuativeRel


end PI.UnitaryGroupMassFormula.CntFormula
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S
open Classical ValuativeRel

theorem isIntegral_iff_mem_integer (F : Type) [Field F] [ValuativeRel F] (a : F) :
    IsIntegral 𝒪[F] a ↔ a ∈ 𝒪[F] := by
  constructor
  · intro h
    exact (Valuation.integer.integers _).mem_of_integral h
  · intro h
    have e : a = algebraMap 𝒪[F] F ⟨a, h⟩ := rfl
    rw [e]
    exact isIntegral_algebraMap

theorem integral_split_count : OSplit := by
  intro F E _ _ _ _ _ _ L _ e x
  rw [L.O_def]
  have key : IsIntegral 𝒪[F] x ↔ IsIntegral 𝒪[F] (e x) := by
    constructor
    · intro h
      exact h.map ((e : E →ₐ[F] F × F).restrictScalars 𝒪[F])
    · intro h
      have h' := h.map ((e.symm : F × F →ₐ[F] E).restrictScalars 𝒪[F])
      simpa using h'
  rw [key]
  constructor
  · intro h
    exact ⟨(isIntegral_iff_mem_integer F _).1 (h.map (AlgHom.fst 𝒪[F] F F)),
      (isIntegral_iff_mem_integer F _).1 (h.map (AlgHom.snd 𝒪[F] F F))⟩
  · rintro ⟨h1, h2⟩
    exact IsIntegral.pair ((isIntegral_iff_mem_integer F _).2 h1) ((isIntegral_iff_mem_integer F _).2 h2)

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S ValuativeRel

theorem latBasis_exists (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ) (S : Submodule 𝒪[F] (Fin n → F))
    (hfg : S.FG) (hsp : Submodule.span F (S : Set (Fin n → F)) = ⊤) :
    ∃ b : Module.Basis (Fin n) F (Fin n → F), (∀ k, b k ∈ S) ∧
      ∀ v, v ∈ S ↔ ∀ k, b.repr v k ∈ 𝒪[F] := by
  have : S.IsLattice F := ⟨hfg, hsp⟩
  have hr : Module.finrank 𝒪[F] S = n := by
    simpa using Submodule.IsLattice.finrank_of_pi F S
  let b0 : Module.Basis (Fin n) 𝒪[F] S := Module.finBasisOfFinrankEq 𝒪[F] S hr
  let b := b0.extendOfIsLattice F
  have hb : ∀ k, b k = (b0 k : Fin n → F) := fun k => by simp [b]
  refine ⟨b, fun k => by rw [hb]; exact (b0 k).2, fun v => ⟨fun hv k => ?_, fun h => ?_⟩⟩
  · have key : v = b.equivFun.symm (fun k => ((b0.repr ⟨v, hv⟩ k : 𝒪[F]) : F)) := by
      rw [Module.Basis.equivFun_symm_apply]
      have h1 : ∑ i, ((b0.repr ⟨v, hv⟩ i • b0 i : S) : Fin n → F) = v := by
        rw [← Submodule.coe_sum, b0.sum_repr]
      conv_lhs => rw [← h1]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hb, Submodule.coe_smul]
      rfl
    have h2 := congrArg b.equivFun key
    rw [LinearEquiv.apply_symm_apply, Module.Basis.equivFun_apply] at h2
    rw [h2]
    exact (b0.repr ⟨v, hv⟩ k).2
  · rw [← b.sum_repr v]
    refine Submodule.sum_mem _ fun k _ => ?_
    have := S.smul_mem (⟨b.repr v k, h k⟩ : 𝒪[F]) (show b k ∈ S by rw [hb]; exact (b0 k).2)
    exact this

section Herm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

end Herm

section Coord

variable {F : Type} [Field F] {E : Type} [CommRing E] [Algebra F E]
variable {V : Type} [AddCommGroup V] [Module E V]

def sig (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (x : V) : (Fin n → F) × (Fin n → F) :=
  (fun k => (e (β.repr x k)).1, fun k => (e (β.repr x k)).2)

def tau (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (p : (Fin n → F) × (Fin n → F)) : V :=
  ∑ k, e.symm (p.1 k, p.2 k) • β k

theorem sig_tau (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (p : (Fin n → F) × (Fin n → F)) :
    sig e β (tau e β p) = p := by
  unfold sig tau
  first
  | simp only [Basis.repr_sum_self, AlgEquiv.apply_symm_apply]
  | simp [map_sum, Finsupp.single_apply]

theorem tau_sig (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (x : V) :
    tau e β (sig e β x) = x := by
  unfold sig tau
  simp only [Prod.mk.eta, AlgEquiv.symm_apply_apply]
  exact β.sum_repr x

theorem sig_add (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (x y : V) :
    sig e β (x + y) = sig e β x + sig e β y := by
  refine Prod.ext ?_ ?_ <;> funext k <;> simp [sig, map_add]

theorem sig_smul (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (a : E) (x : V) :
    sig e β (a • x) = ((e a).1 • (sig e β x).1, (e a).2 • (sig e β x).2) := by
  refine Prod.ext ?_ ?_ <;> funext k <;> simp [sig, map_mul]

theorem tau_add (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (p q : (Fin n → F) × (Fin n → F)) :
    tau e β (p + q) = tau e β p + tau e β q := by
  unfold tau
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← add_smul, ← map_add]
  rfl

theorem tau_smul (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (a : E)
    (p : (Fin n → F) × (Fin n → F)) :
    tau e β ((e a).1 • p.1, (e a).2 • p.2) = a • tau e β p := by
  unfold tau
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [smul_smul]
  congr 1
  have h1 : (((e a).1 • p.1) k, ((e a).2 • p.2) k) = e a * (p.1 k, p.2 k) :=
    Prod.ext (by simp) (by simp)
  rw [h1, map_mul, AlgEquiv.symm_apply_apply]

theorem sig_zero (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) : sig e β 0 = 0 := by
  refine Prod.ext ?_ ?_ <;> funext k <;> simp [sig]

end Coord

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S ValuativeRel Matrix

section Alg

variable {F : Type} [Field F]

def qmat {n : ℕ} (b : Module.Basis (Fin n) F (Fin n → F)) (A : Matrix (Fin n) (Fin n) F) :
    Matrix (Fin n) (Fin n) F :=
  Matrix.of (fun k i => b k i) * A

theorem pair_basis {n : ℕ} (b : Module.Basis (Fin n) F (Fin n → F)) (A : Matrix (Fin n) (Fin n) F)
    (u w : Fin n → F) : u ⬝ᵥ (A *ᵥ w) = b.equivFun u ⬝ᵥ (qmat b A *ᵥ w) := by
  rw [qmat, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (b.equivFun u)]
  congr 1
  funext i
  have h := congrFun (b.sum_equivFun u) i
  rw [Finset.sum_apply] at h
  simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
  exact h.symm

end Alg

section Main

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def amat {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)
    (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) : Matrix (Fin n) (Fin n) F :=
  fun k l => (e (H.h (β k) (β l))).1

private theorem hermSp_h_sum_left {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) {ι : Type} (s : Finset ι) (f : ι → V) (y : V) :
    H.h (∑ i ∈ s, f i) y = ∑ i ∈ s, H.h (f i) y :=
  map_sum (AddMonoidHom.mk' (fun x => H.h x y) (fun x x' => H.h_add_left x x' y)) f s

private theorem hermSp_h_sum_right' {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) {ι : Type} (s : Finset ι) (f : ι → V) (x : V) :
    H.h x (∑ i ∈ s, f i) = ∑ i ∈ s, H.h x (f i) := by
  rw [H.h_herm, hermSp_h_sum_left, map_sum]
  exact Finset.sum_congr rfl (fun i _ => (H.h_herm (f i) x).symm)

private theorem hermSp_h_smul_right {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm, H.h_smul_left, map_mul, ← H.h_herm]

theorem form_fst {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)
    (e : E ≃ₐ[F] F × F) (he : ∀ x, e (M.L.cj x) = (e x).swap) {n : ℕ} (β : Module.Basis (Fin n) E V)
    (x y : V) : (e (H.h x y)).1 = (sig e β x).1 ⬝ᵥ (amat H e β *ᵥ (sig e β y).2) := by
  conv_lhs => rw [← β.sum_repr x, ← β.sum_repr y]
  simp only [hermSp_h_sum_left, hermSp_h_sum_right', H.h_smul_left, hermSp_h_smul_right, map_sum, map_mul, Prod.fst_sum, Prod.fst_mul, he,
    Prod.fst_swap]
  simp only [amat, sig, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  ring

theorem form_snd {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)
    (e : E ≃ₐ[F] F × F) (he : ∀ x, e (M.L.cj x) = (e x).swap) {n : ℕ} (β : Module.Basis (Fin n) E V)
    (x y : V) : (e (H.h x y)).2 = (sig e β y).1 ⬝ᵥ (amat H e β *ᵥ (sig e β x).2) := by
  have hs : ∀ k l, (e (H.h (β k) (β l))).2 = (e (H.h (β l) (β k))).1 := fun k l => by
    rw [H.h_herm (β l) (β k), he]; rfl
  conv_lhs => rw [← β.sum_repr x, ← β.sum_repr y]
  simp only [hermSp_h_sum_left, hermSp_h_sum_right', H.h_smul_left, hermSp_h_smul_right, map_sum, map_mul, Prod.snd_sum, Prod.snd_mul, he,
    Prod.snd_swap, hs]
  simp only [amat, sig, dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  ring

theorem tau_zero (e : E ≃ₐ[F] F × F) {V : Type} [AddCommGroup V] [Module E V] {n : ℕ}
    (β : Module.Basis (Fin n) E V) : tau e β 0 = 0 := by
  simp only [tau, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, Prod.mk_zero_zero, map_zero, zero_smul,
    Finset.sum_const_zero]

theorem one_sum {n : ℕ} (u w : Fin n → F) :
    ∑ k, ∑ l, u k * (((1 : Matrix (Fin n) (Fin n) 𝒪[F]) k l : 𝒪[F]) : F) * w l = u ⬝ᵥ w := by
  simp only [Matrix.one_apply, apply_ite (fun z : 𝒪[F] => (z : F)), OneMemClass.coe_one, ZeroMemClass.coe_zero,
    mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, dotProduct]

theorem coord_of_basis (M : Loc.Model F E) (hl : IsNonarchimedeanLocalField F)
    (e : E ≃ₐ[F] F × F) (he : ∀ x, e (M.L.cj x) = (e x).swap)
    (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V)
    (hΛ : H.IsSelfDual Λ) {n : ℕ} (β : Module.Basis (Fin n) E V) :
    ∃ (π : V ≃+ (Fin n → F) × (Fin n → F)) (Ph : Matrix (Fin n) (Fin n) 𝒪[F]), IsSplitCoord e H Λ π Ph := by
  classical
  have hO : ∀ x : E, x ∈ M.L.O ↔ (e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F] := fun x => integral_split_count F E M.L hl e x
  set A := amat H e β with hA
  set ε₁ : E := e.symm (1, 0) with hε₁
  set ε₂ : E := e.symm (0, 1) with hε₂
  have he₁ : e ε₁ = (1, 0) := by simp [ε₁]
  have he₂ : e ε₂ = (0, 1) := by simp [ε₂]
  have hε₁O : ε₁ ∈ M.L.O := (hO _).2 (by rw [he₁]; exact ⟨one_mem _, zero_mem _⟩)
  have hε₂O : ε₂ ∈ M.L.O := (hO _).2 (by rw [he₂]; exact ⟨zero_mem _, one_mem _⟩)
  have h1 : ∀ x, tau e β ((sig e β x).1, 0) = ε₁ • x := by
    intro x
    have := tau_smul e β ε₁ (sig e β x)
    rw [he₁, tau_sig] at this
    simpa using this
  have h2 : ∀ x, tau e β (0, (sig e β x).2) = ε₂ • x := by
    intro x
    have := tau_smul e β ε₂ (sig e β x)
    rw [he₂, tau_sig] at this
    simpa using this
  have memΛ : ∀ x, x ∈ Λ ↔ tau e β ((sig e β x).1, 0) ∈ Λ ∧ tau e β (0, (sig e β x).2) ∈ Λ := by
    intro x
    constructor
    · intro hx
      rw [h1, h2]
      exact ⟨Λ.smul_mem (⟨ε₁, hε₁O⟩ : M.L.O) hx, Λ.smul_mem (⟨ε₂, hε₂O⟩ : M.L.O) hx⟩
    · rintro ⟨ha, hb⟩
      have : x = tau e β ((sig e β x).1, 0) + tau e β (0, (sig e β x).2) := by
        rw [← tau_add, Prod.mk_add_mk, add_zero, zero_add]
        exact (tau_sig e β x).symm
      rw [this]
      exact Λ.add_mem ha hb

  let S₁ : Submodule 𝒪[F] (Fin n → F) :=
    { carrier := {u | tau e β (u, 0) ∈ Λ}
      add_mem' := by
        intro u v hu hv
        simp only [Set.mem_ofPred_eq] at hu hv ⊢
        have : ((u + v, 0) : (Fin n → F) × (Fin n → F)) = (u, 0) + (v, 0) := by simp
        rw [this, tau_add]
        exact Λ.add_mem hu hv
      zero_mem' := by
        simp only [Set.mem_ofPred_eq]
        have : ((0, 0) : (Fin n → F) × (Fin n → F)) = 0 := rfl
        rw [this, tau_zero]
        exact Λ.zero_mem
      smul_mem' := by
        intro c u hu
        simp only [Set.mem_ofPred_eq] at hu ⊢
        set a : E := algebraMap F E (c : F) with ha
        have hea : e a = ((c : F), (c : F)) := by simp [a]
        have haO : a ∈ M.L.O := (hO a).2 (by rw [hea]; exact ⟨c.2, c.2⟩)
        have := tau_smul e β a (u, 0)
        rw [hea] at this
        have hcu : ((c • u, 0) : (Fin n → F) × (Fin n → F)) = ((c : F) • u, (c : F) • (0 : Fin n → F)) := by
          rw [smul_zero]
          rfl
        rw [hcu, this]
        exact Λ.smul_mem (⟨a, haO⟩ : M.L.O) hu }
  have hS₁ : ∀ u, u ∈ S₁ ↔ tau e β (u, 0) ∈ Λ := fun u => Iff.rfl
  have hsigS : ∀ y ∈ Λ, (sig e β y).1 ∈ S₁ := by
    intro y hy
    rw [hS₁, h1]
    exact Λ.smul_mem (⟨ε₁, hε₁O⟩ : M.L.O) hy
  have hfg : S₁.FG := by
    obtain ⟨s, hs⟩ := hΛ.1
    refine ⟨s.image (fun g => (sig e β g).1), le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le, Finset.coe_image]
      rintro _ ⟨g, hg, rfl⟩
      exact hsigS g (hs ▸ Submodule.subset_span hg)
    · intro u hu
      rw [Finset.coe_image]
      have hu' : tau e β (u, 0) ∈ Submodule.span M.L.O (s : Set V) := by rw [hs]; exact hu
      have key : ∀ y ∈ Submodule.span M.L.O (s : Set V),
          (sig e β y).1 ∈ Submodule.span 𝒪[F] ((fun g => (sig e β g).1) '' (s : Set V)) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem g hg => exact Submodule.subset_span ⟨g, hg, rfl⟩
        | zero => rw [sig_zero]; exact Submodule.zero_mem _
        | add x y _ _ hx hy => rw [sig_add]; exact Submodule.add_mem _ hx hy
        | smul a x _ hx =>
          have hs' : (sig e β (a • x)).1 = (e (a : E)).1 • (sig e β x).1 := by
            rw [show a • x = (a : E) • x from rfl, sig_smul]
          rw [hs']
          exact Submodule.smul_mem _ (⟨(e (a : E)).1, ((hO a).1 a.2).1⟩ : 𝒪[F]) hx
      have := key _ hu'
      rwa [sig_tau] at this
  have hsp : Submodule.span F (S₁ : Set (Fin n → F)) = ⊤ := by
    rw [eq_top_iff]
    intro u _
    have key : ∀ y ∈ Submodule.span E (Λ : Set V),
        (sig e β y).1 ∈ Submodule.span F (S₁ : Set (Fin n → F)) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem g hg => exact Submodule.subset_span (hsigS g hg)
      | zero => rw [sig_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [sig_add]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx =>
        rw [sig_smul]
        exact Submodule.smul_mem _ _ hx
    have := key (tau e β (u, 0)) (by rw [hΛ.2.1]; trivial)
    rwa [sig_tau] at this
  obtain ⟨bF, hbS, hbmem⟩ := latBasis_exists F n S₁ hfg hsp
  set Qm := qmat bF A with hQm

  have hpair : ∀ (x : V) (w : Fin n → F), e (H.h x (tau e β (0, w))) =
      (bF.equivFun (sig e β x).1 ⬝ᵥ (Qm *ᵥ w), 0) := by
    intro x w
    ext
    · rw [form_fst H e he, sig_tau, pair_basis bF]
    · rw [form_snd H e he, sig_tau]
      simp
  have hpair' : ∀ (y : V) (w : Fin n → F), e (H.h (tau e β (0, w)) y) =
      (0, bF.equivFun (sig e β y).1 ⬝ᵥ (Qm *ᵥ w)) := by
    intro y w
    rw [H.h_herm y (tau e β (0, w)), he, hpair]
    rfl
  have hinj : Function.Injective (Matrix.mulVecLin Qm) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    rw [Matrix.mulVecLin_apply] at hw
    have hz : ∀ x, H.h x (tau e β (0, w)) = 0 := by
      intro x
      apply e.injective
      rw [hpair, hw, dotProduct_zero, map_zero]
      rfl
    have hy : tau e β (0, w) = 0 := by
      apply H.nondeg
      intro z
      rw [H.h_herm z, hz, map_zero]
    have := congrArg (fun v => (sig e β v).2) hy
    simpa [sig_tau, sig_zero] using this
  let Qe : (Fin n → F) ≃ₗ[F] (Fin n → F) := LinearEquiv.ofInjectiveEndo (Matrix.mulVecLin Qm) hinj
  let σ : V ≃+ (Fin n → F) × (Fin n → F) :=
    { toFun := sig e β
      invFun := tau e β
      left_inv := tau_sig e β
      right_inv := sig_tau e β
      map_add' := sig_add e β }
  let π : V ≃+ (Fin n → F) × (Fin n → F) :=
    σ.trans (AddEquiv.prodCongr bF.equivFun.toAddEquiv Qe.toAddEquiv)
  have hπ : ∀ x, π x = (bF.equivFun (sig e β x).1, Qm *ᵥ (sig e β x).2) := fun x => rfl

  have hdual : ∀ w, tau e β (0, w) ∈ Λ ↔ ∀ k, (Qm *ᵥ w) k ∈ 𝒪[F] := by
    intro w
    rw [hΛ.2.2]
    constructor
    · intro hall k
      have hy : tau e β (bF k, 0) ∈ Λ := hbS k
      have := ((hO _).1 (hall _ hy)).2
      rw [hpair', sig_tau] at this
      have hsingle : bF.equivFun (bF k) = Pi.single k 1 := by
        ext j
        rw [Module.Basis.equivFun_self]
        simp [Pi.single_apply, eq_comm]
      simpa [hsingle, single_dotProduct] using this
    · intro hq y hy
      rw [hO, hpair']
      refine ⟨zero_mem _, ?_⟩
      have hc := (hbmem _).1 (hsigS y hy)
      simp only [dotProduct, Module.Basis.equivFun_apply]
      exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hc k) (hq k)
  refine ⟨π, 1, ?_, ?_, by simp, ?_⟩
  · intro a x
    rw [hπ, hπ, sig_smul]
    simp only [map_smul, Matrix.mulVec_smul]
  · intro x
    rw [memΛ, ← hS₁, hbmem, hdual, hπ]
    simp only [Module.Basis.equivFun_apply]
  · intro x y
    rw [hπ, hπ, one_sum, one_sum]
    ext
    · rw [form_fst H e he, pair_basis bF]
    · rw [form_snd H e he, pair_basis bF]

theorem adapted_coords_self_dual : CoordData := by
  intro F E _ _ _ _ _ _ _ M hl _ e he V _ _ H Λ hΛ
  haveI := H.free
  haveI := H.fin
  haveI : Nontrivial E := e.toEquiv.nontrivial
  exact coord_of_basis M hl e he V H Λ hΛ (Module.finBasis E V)

end Main

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section
namespace PI.UnitaryGroupMassFormula.CntFormula


end PI.UnitaryGroupMassFormula.CntFormula
end
