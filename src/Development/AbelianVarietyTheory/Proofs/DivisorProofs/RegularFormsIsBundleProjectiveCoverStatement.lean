import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureProjectiveOverStandardOpenRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraClosurePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraEqRangeExteriorPower
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraStandardOpenIffPowSmulStatement

section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kahlerFormsOverSubalgebra_eq_range_exteriorPower : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K] [Algebra.Smooth k B] (q : ℕ), ∃ e : (⋀[B]^q Ω[B⁄k]) →ₗ[B] DR k K, Function.Injective e ∧ (∀ y, y ∈ omB k K B q ↔ ∃ z, e z = y) ∧ ∀ v : Fin q → B, e (exteriorPower.ιMulti B q fun j => D k B (v j)) = ExteriorAlgebra.ιMulti K q fun j => D k K (v j : K) := by
  first | (exact @GlobalTheory.PD.omB_eq_range_exteriorPower) | (exact GlobalTheory.PD.omB_eq_range_exteriorPower) | (intros; apply GlobalTheory.PD.omB_eq_range_exteriorPower  <;> assumption)
end

section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem projective_exteriorPower_of_projective (R V : Type) [CommRing R] [AddCommGroup V] [Module R V]
    [Module.Projective R V] (n : ℕ) : Module.Projective R (⋀[R]^n V) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective R V)
  haveI : Module.Free R (⋀[R]^n (V →₀ R)) := exteriorPower.instFree R n
  refine Module.Projective.of_split (exteriorPower.map n s)
    (exteriorPower.map n (Finsupp.linearCombination R id)) ?_
  rw [← exteriorPower.map_comp, hs, exteriorPower.map_id]

theorem span_omB_comap_finite_projective : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K] [Algebra.Smooth k B] (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module k W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K), Function.Injective e → LinearMap.range e = ⋀[K]^p Ω[K⁄k] → Module.Finite B (Submodule.span B ((omB k K B p).comap (e.restrictScalars k) : Set W)) ∧ Module.Projective B (Submodule.span B ((omB k K B p).comap (e.restrictScalars k) : Set W)) := by
  intro k K _ _ _ B _ _ p W _ _ _ _ e he hr
  obtain ⟨e', he', hre', -⟩ := GlobalTheory.T.kahlerFormsOverSubalgebra_eq_range_exteriorPower k K B p
  have hom := fun a ha => ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K B p p).2.1 a ha)
  let S : Submodule k W := (omB k K B p).comap (e.restrictScalars k)
  let T : Submodule B W :=
    { carrier := (S : Set W)
      add_mem' := S.add_mem
      zero_mem' := S.zero_mem
      smul_mem' := fun c w hw => by
        change e ((c : K) • w) ∈ omB k K B p
        rw [map_smul]
        exact (hom _ hw).2.2.2 c c.2 }
  have hST : Submodule.span B (S : Set W) = T := Submodule.span_eq T
  change Module.Finite B (Submodule.span B (S : Set W)) ∧ Module.Projective B (Submodule.span B (S : Set W))
  rw [hST]
  let g : T →ₗ[B] DR k K :=
    { toFun := fun w => e w
      map_add' := fun w w' => by simp
      map_smul' := fun c w => by
        change e ((c : K) • (w : W)) = (c : K) • e w
        exact e.map_smul (c : K) w }
  have hg : Function.Injective g := fun w w' h => Subtype.ext (he h)
  have hrg : LinearMap.range g = LinearMap.range e' := by
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨z, hz⟩ := (hre' _).1 w.2
      exact ⟨z, hz⟩
    · rintro ⟨z, rfl⟩
      have hy : e' z ∈ omB k K B p := (hre' _).2 ⟨z, rfl⟩
      have hy' : e' z ∈ LinearMap.range e := by rw [hr]; exact (hom _ hy).2.2.1
      obtain ⟨w, hw⟩ := hy'
      have hwT : w ∈ T := by
        change e w ∈ omB k K B p
        rw [hw]; exact hy
      exact ⟨⟨w, hwT⟩, hw⟩
  let E : T ≃ₗ[B] ⋀[B]^p Ω[B⁄k] :=
    (LinearEquiv.ofInjective g hg).trans ((LinearEquiv.ofEq _ _ hrg).trans (LinearEquiv.ofInjective e' he').symm)
  haveI : Module.Projective B (⋀[B]^p Ω[B⁄k]) := projective_exteriorPower_of_projective B _ p
  exact ⟨Module.Finite.equiv E.symm, Module.Projective.of_equiv E.symm⟩

end GlobalTheory.PD
end

section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_regularForms_finite_projective_smooth : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K] [Algebra.Smooth k B] (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module k W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K), Function.Injective e → LinearMap.range e = ⋀[K]^p Ω[K⁄k] → Module.Finite B (Submodule.span B ((omB k K B p).comap (e.restrictScalars k) : Set W)) ∧ Module.Projective B (Submodule.span B ((omB k K B p).comap (e.restrictScalars k) : Set W)) := by
  first | (exact @GlobalTheory.PD.span_omB_comap_finite_projective) | (exact GlobalTheory.PD.span_omB_comap_finite_projective) | (intros; apply GlobalTheory.PD.span_omB_comap_finite_projective  <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD.KSpan

theorem alt_mem_of_span {K M N : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    {n : ℕ} (f : M [⋀^Fin n]→ₗ[K] N) (s : Set M) (hs : Submodule.span K s = ⊤) (T : Submodule K N)
    (hT : ∀ v : Fin n → M, (∀ i, v i ∈ s) → f v ∈ T) (v : Fin n → M) : f v ∈ T := by
  have key : ∀ j : ℕ, ∀ v : Fin n → M, (∀ i : Fin n, j ≤ i.val → v i ∈ s) → f v ∈ T := by
    intro j
    induction j with
    | zero => intro v hv; exact hT v fun i => hv i (Nat.zero_le _)
    | succ j ih =>
      intro v hv
      by_cases hj : j < n
      · have hmem : v ⟨j, hj⟩ ∈ Submodule.span K s := hs ▸ Submodule.mem_top
        have hall : ∀ x ∈ Submodule.span K s, f (Function.update v ⟨j, hj⟩ x) ∈ T := by
          intro x hx
          induction hx using Submodule.span_induction with
          | mem x hx =>
            apply ih
            intro i hi
            by_cases h : i = ⟨j, hj⟩
            · rw [h, Function.update_self]; exact hx
            · rw [Function.update_of_ne h]
              apply hv
              have : i.val ≠ j := fun h' => h (Fin.ext h')
              omega
          | zero => rw [AlternatingMap.map_update_zero]; exact T.zero_mem
          | add a b _ _ ha hb => rw [AlternatingMap.map_update_add]; exact T.add_mem ha hb
          | smul r a _ ha => rw [AlternatingMap.map_update_smul]; exact T.smul_mem r ha
        simpa using hall _ hmem
      · exact ih v fun i hi => hv i (by have := i.isLt; omega)
  exact key n v fun i hi => absurd i.isLt (by omega)

end GlobalTheory.PD.KSpan

namespace GlobalTheory.PD

open KSpan in

theorem omB_comap_span_eq_top : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K] (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module k W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K), Function.Injective e → LinearMap.range e = ⋀[K]^p Ω[K⁄k] → Submodule.span K ((omB k K B p).comap (e.restrictScalars k) : Set W) = ⊤ := by
  intro k K _ _ _ B _ p W _ _ _ _ e he hr
  have hD : Submodule.span K (D k K '' (B : Set K)) = ⊤ := by
    rw [eq_top_iff, ← span_range_derivation k K, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    obtain ⟨b1, b2, hb2, rfl⟩ := IsFractionRing.div_surjective (A := B) y
    have h2 : algebraMap B K b2 ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb2
    set q := algebraMap B K b1 / algebraMap B K b2 with hqdef
    have e1 : algebraMap B K b1 = q * algebraMap B K b2 := by rw [hqdef, div_mul_cancel₀ _ h2]
    have hq : D k K q = (algebraMap B K b2)⁻¹ • (D k K (algebraMap B K b1) - q • D k K (algebraMap B K b2)) := by
      rw [e1, Derivation.leibniz, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ h2, one_smul]
    have m1 : D k K (algebraMap B K b1) ∈ Submodule.span K (D k K '' (B : Set K)) :=
      Submodule.subset_span ⟨(b1 : K), b1.2, rfl⟩
    have m2 : D k K (algebraMap B K b2) ∈ Submodule.span K (D k K '' (B : Set K)) :=
      Submodule.subset_span ⟨(b2 : K), b2.2, rfl⟩
    rw [SetLike.mem_coe, hq]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ m1 (Submodule.smul_mem _ _ m2))
  have hS : (omB k K B p : Set (DR k K)) ⊆ ⋀[K]^p Ω[K⁄k] := by
    intro y hy
    change y ∈ Submodule.span k _ at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, -, v, -, rfl⟩ := hy
      exact Submodule.smul_mem _ b (ExteriorAlgebra.ιMulti_range K p ⟨_, rfl⟩)
    | zero => exact Submodule.zero_mem _
    | add a c _ _ ha hc => exact Submodule.add_mem _ ha hc
    | smul r a _ ha => rw [← algebraMap_smul K r a]; exact Submodule.smul_mem _ _ ha
  have hP : ⋀[K]^p Ω[K⁄k] ≤ Submodule.span K (omB k K B p : Set (DR k K)) := by
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    refine alt_mem_of_span (ExteriorAlgebra.ιMulti K p) _ hD _ ?_ v
    intro v hv
    choose b hb hbv using hv
    apply Submodule.subset_span
    apply Submodule.subset_span
    refine ⟨1, B.one_mem, b, hb, ?_⟩
    rw [one_smul]
    simp only [hbv]
  have hSC : (omB k K B p : Set (DR k K)) ⊆ e '' ((omB k K B p).comap (e.restrictScalars k) : Set W) := by
    intro y hy
    obtain ⟨w, rfl⟩ : y ∈ LinearMap.range e := hr ▸ hS hy
    exact ⟨w, hy, rfl⟩
  rw [eq_top_iff, ← Submodule.map_le_map_iff_of_injective he, ← LinearMap.range_eq_map, hr, Submodule.map_span]
  exact hP.trans (Submodule.span_mono hSC)

end GlobalTheory.PD
end
end

section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kahlerFormsOverSubalgebra_comap_span_eq_top : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K] (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module k W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K), Function.Injective e → LinearMap.range e = ⋀[K]^p Ω[K⁄k] → Submodule.span K ((omB k K B p).comap (e.restrictScalars k) : Set W) = ⊤ := by
  first | (exact @GlobalTheory.PD.omB_comap_span_eq_top) | (exact GlobalTheory.PD.omB_comap_span_eq_top) | (intros; apply GlobalTheory.PD.omB_comap_span_eq_top  <;> assumption)
end

section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

open KaehlerDifferential in

theorem _root_.GlobalTheory.span_eq_top_of_stable_of_isFractionRing :
    ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k K] [Algebra F K] [FiniteDimensional F K] (B : Subalgebra k K) [IsFractionRing B K] (W : Type) [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W] (S : Set W), (∀ c ∈ B, ∀ w ∈ S, (c : K) • w ∈ S) → Submodule.span K S = ⊤ → Submodule.span F S = ⊤ := by
  intro k F K _ _ _ _ _ _ B _ W _ _ _ _ S hS hspan
  set M := Submodule.span F S with hM
  let T : Subalgebra F K :=
    { carrier := {y | ∀ m ∈ M, y • m ∈ M}
      mul_mem' := fun {a b} ha hb m hm => by rw [mul_smul]; exact ha _ (hb m hm)
      one_mem' := fun m hm => by rwa [one_smul]
      add_mem' := fun {a b} ha hb m hm => by rw [add_smul]; exact M.add_mem (ha m hm) (hb m hm)
      zero_mem' := fun m _ => by rw [zero_smul]; exact M.zero_mem
      algebraMap_mem' := fun f m hm => by rw [algebraMap_smul]; exact M.smul_mem f hm }
  have hmemT : ∀ y : K, y ∈ T ↔ ∀ m ∈ M, y • m ∈ M := fun y => Iff.rfl
  have hB : ∀ c ∈ B, (c : K) ∈ T := by
    intro c hc m hm
    induction hm using Submodule.span_induction with
    | mem s hs => exact Submodule.subset_span (hS c hc s hs)
    | zero => rw [smul_zero]; exact M.zero_mem
    | add v w _ _ hv hw => rw [smul_add]; exact M.add_mem hv hw
    | smul f v _ hv => rw [smul_comm]; exact M.smul_mem f hv
  have hinv : ∀ y : K, y ∈ T → y⁻¹ ∈ T := by
    intro y hy
    exact T.inv_mem_of_algebraic (x := ⟨y, hy⟩) (Algebra.IsAlgebraic.isAlgebraic y)
  have hall : ∀ y : K, y ∈ T := by
    intro y
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := B) y
    rw [div_eq_mul_inv]
    exact T.mul_mem (hB _ a.2) (hinv _ (hB _ b.2))
  let MK : Submodule K W :=
    { carrier := M
      add_mem' := M.add_mem
      zero_mem' := M.zero_mem
      smul_mem' := fun c m hm => hall c m hm }
  have hle : Submodule.span K S ≤ MK := Submodule.span_le.mpr fun s hs => Submodule.subset_span hs
  rw [hspan] at hle
  exact eq_top_iff.mpr fun w _ => hle Submodule.mem_top

end GlobalTheory
end

section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_eq_top_of_stable_of_isFractionRing' : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k K] [Algebra F K] [FiniteDimensional F K] (B : Subalgebra k K) [IsFractionRing B K] (W : Type) [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W] (S : Set W), (∀ c ∈ B, ∀ w ∈ S, (c : K) • w ∈ S) → Submodule.span K S = ⊤ → Submodule.span F S = ⊤ := by
  first | (exact @GlobalTheory.span_eq_top_of_stable_of_isFractionRing) | (exact GlobalTheory.span_eq_top_of_stable_of_isFractionRing) | (intros; apply GlobalTheory.span_eq_top_of_stable_of_isFractionRing  <;> assumption)
end

section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

open KaehlerDifferential in
private theorem projective_of_isScalarTower_projective (R A M : Type) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Projective R A]
    [Module.Projective A M] : Module.Projective R M := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective A M)
  have : Module.Projective R (M →₀ A) :=
    Module.Projective.of_equiv (finsuppLequivDFinsupp R : (M →₀ A) ≃ₗ[R] Π₀ _ : M, A).symm
  exact Module.Projective.of_split ((s.restrictScalars R))
    ((Finsupp.linearCombination A id).restrictScalars R)
    (LinearMap.ext fun m => LinearMap.congr_fun hs m)

open KaehlerDifferential in

theorem _root_.GlobalTheory.finite_projective_span_of_integralClosure :
    ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (A : Subalgebra k F) (B : Subalgebra k K), (∀ y : K, y ∈ B ↔ y ∈ integralClosure A K) → Module.Finite A (integralClosure A K) → Module.Projective A (integralClosure A K) → ∀ (W : Type) [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W] (S : Set W), (∀ c ∈ B, ∀ w ∈ S, (c : K) • w ∈ S) → Module.Finite B (Submodule.span B S) → Module.Projective B (Submodule.span B S) → Module.Finite A (Submodule.span A S) ∧ Module.Projective A (Submodule.span A S) := by
  intro k F K _ _ _ _ _ _ _ A B hB hfin hproj W _ _ _ _ S hS hfinB hprojB
  have hAB : ∀ a : A, algebraMap A K a ∈ B := fun a =>
    (hB _).2 ((integralClosure A K).algebraMap_mem a)
  letI : Algebra A B := ((algebraMap A K).codRestrict B hAB).toAlgebra
  have hcoe : ∀ (a : A) (b : B), ((a • b : B) : K) = algebraMap F K (a : F) * (b : K) := by
    intro a b
    rw [Algebra.smul_def]
    rfl
  haveI : IsScalarTower A B W := ⟨fun a b w => by
    rw [Subalgebra.smul_def, hcoe, mul_smul, algebraMap_smul, Subalgebra.smul_def,
      Subalgebra.smul_def]⟩
  let ψ : B ≃ₗ[A] integralClosure A K :=
    { toFun := fun b => ⟨b, (hB b).1 b.2⟩
      invFun := fun c => ⟨c, (hB c).2 c.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun a b => Subtype.ext <| by
        rw [hcoe, RingHom.id_apply, SetLike.val_smul, Algebra.smul_def]
        rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : Module.Finite A B := Module.Finite.equiv ψ.symm
  haveI : Module.Projective A B := Module.Projective.of_equiv ψ.symm
  haveI : Module.Finite A (Submodule.span B S) := Module.Finite.trans B _
  haveI : Module.Projective A (Submodule.span B S) := projective_of_isScalarTower_projective A B _
  have hclosed : ∀ c : B, ∀ w ∈ Submodule.span A S, c • w ∈ Submodule.span A S := by
    intro c w hw
    induction hw using Submodule.span_induction with
    | mem s hs =>
      rw [Subalgebra.smul_def]
      exact Submodule.subset_span (hS c c.2 s hs)
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add v w _ _ hv hw => rw [smul_add]; exact Submodule.add_mem _ hv hw
    | smul a v _ hv => rw [smul_comm]; exact Submodule.smul_mem _ a hv
  let SB : Submodule B W :=
    { carrier := Submodule.span A S
      add_mem' := Submodule.add_mem _
      zero_mem' := Submodule.zero_mem _
      smul_mem' := fun c w hw => hclosed c w hw }
  have hsets : ∀ w, w ∈ Submodule.span A S ↔ w ∈ Submodule.span B S := by
    intro w
    constructor
    · intro hw
      have hle : Submodule.span A S ≤ (Submodule.span B S).restrictScalars A :=
        Submodule.span_le.mpr fun s hs => Submodule.subset_span hs
      exact hle hw
    · intro hw
      have hle : Submodule.span B S ≤ SB :=
        Submodule.span_le.mpr fun s hs => (Submodule.subset_span hs : s ∈ Submodule.span A S)
      exact hle hw
  let χ : Submodule.span A S ≃ₗ[A] Submodule.span B S :=
    { toFun := fun w => ⟨w, (hsets w).1 w.2⟩
      invFun := fun w => ⟨w, (hsets w).2 w.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact ⟨Module.Finite.equiv χ.symm, Module.Projective.of_equiv χ.symm⟩

end GlobalTheory
end

section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_projective_span_of_integralClosure' : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (A : Subalgebra k F) (B : Subalgebra k K), (∀ y : K, y ∈ B ↔ y ∈ integralClosure A K) → Module.Finite A (integralClosure A K) → Module.Projective A (integralClosure A K) → ∀ (W : Type) [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W] (S : Set W), (∀ c ∈ B, ∀ w ∈ S, (c : K) • w ∈ S) → Module.Finite B (Submodule.span B S) → Module.Projective B (Submodule.span B S) → Module.Finite A (Submodule.span A S) ∧ Module.Projective A (Submodule.span A S) := by
  first | (exact @GlobalTheory.finite_projective_span_of_integralClosure) | (exact GlobalTheory.finite_projective_span_of_integralClosure) | (intros; apply GlobalTheory.finite_projective_span_of_integralClosure  <;> assumption)
end

section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem omB_comap_loc : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module F W] [Module k W] [IsScalarTower F K W] [IsScalarTower k F W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K) (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I → (omB k K (rB k K x I) p).comap (e.restrictScalars k) = (Submodule.span (rA k x I) ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W)).restrictScalars k := by
  intro k _ _ F K _ _ _ _ _ _ d x hx p W _ _ _ _ _ _ _ e I i hi
  have hloc := GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul k F K d x hx I i hi p
  ext w
  rw [Submodule.restrictScalars_mem, Submodule.mem_comap, LinearMap.restrictScalars_apply]
  constructor
  · intro hw
    obtain ⟨N, hN⟩ := (hloc _).1 hw
    have hg : (∏ j ∈ I, x i / x j) ^ N ∈ rA k x I :=
      Subalgebra.pow_mem _ (Subalgebra.prod_mem _ fun j hj =>
        Algebra.subset_adjoin (s := {y | ∃ i ∈ I, ∃ j, y = x j / x i}) ⟨j, hj, i, rfl⟩) N
    have hfg : (∏ j ∈ I, x i / x j) ^ N * (∏ j ∈ I, x j / x i) ^ N = 1 := by
      rw [← mul_pow, ← Finset.prod_mul_distrib, Finset.prod_eq_one, one_pow]
      intro j _
      have h1 := hx.pd.ne i
      have h2 := hx.pd.ne j
      field_simp
    have hm : (∏ j ∈ I, x j / x i) ^ N • w ∈
        ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W) := by
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply,
        ← algebraMap_smul K, map_smul, map_pow]
      exact hN
    have := (Submodule.span (rA k x I) _).smul_mem ⟨_, hg⟩ (Submodule.subset_span hm)
    rwa [Subalgebra.smul_def, smul_smul, hfg, one_smul] at this
  · intro hw
    induction hw using Submodule.span_induction with
    | mem z hz =>
      refine (hloc _).2 ⟨0, ?_⟩
      rw [pow_zero, one_smul]
      exact hz
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha =>
      rw [Subalgebra.smul_def, ← algebraMap_smul K, map_smul]
      refine ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) p p).2.1 _ ha).2.2.2 _ ?_
      exact (integralClosure (rA k x I) K).algebraMap_mem r

end GlobalTheory.PD
end

section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pulledBackForms_intersection_eq_chart_localization : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module F W] [Module k W] [IsScalarTower F K W] [IsScalarTower k F W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K) (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I → (omB k K (rB k K x I) p).comap (e.restrictScalars k) = (Submodule.span (rA k x I) ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W)).restrictScalars k := by
  first | (exact @GlobalTheory.PD.omB_comap_loc) | (exact GlobalTheory.PD.omB_comap_loc) | (intros; apply GlobalTheory.PD.omB_comap_loc  <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem omB_isBundle : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module F W] [Module k W] [IsScalarTower F K W] [IsScalarTower k F W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K), Function.Injective e → LinearMap.range e = ⋀[K]^p Ω[K⁄k] → IsBundle k x fun I => (omB k K (rB k K x I) p).comap (e.restrictScalars k) := by
  intro k _ _ F K _ _ _ _ _ _ d x hx p W _ _ _ _ _ _ _ e he hr
  have hstab : ∀ I, ∀ c ∈ rB k K x I, ∀ w ∈ ((omB k K (rB k K x I) p).comap (e.restrictScalars k) : Set W),
      (c : K) • w ∈ ((omB k K (rB k K x I) p).comap (e.restrictScalars k) : Set W) := by
    intro I c hc w hw
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply] at hw ⊢
    rw [map_smul]
    exact ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K _ p p).2.1 _ hw).2.2.2 c hc
  have key : ∀ i, Module.Finite (rA k x {i}) (Submodule.span (rA k x {i})
        ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W)) ∧
      Module.Projective (rA k x {i}) (Submodule.span (rA k x {i})
        ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W)) := by
    intro i
    obtain ⟨hf1, hf2, hf3⟩ := GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x hx {i} (Finset.singleton_nonempty i)
    haveI := hf2
    haveI := hf3
    obtain ⟨hB1, hB2⟩ := GlobalTheory.T.span_regularForms_finite_projective_smooth k K (rB k K x {i}) p W e he hr
    exact GlobalTheory.T.finite_projective_span_of_integralClosure' k F K (rA k x {i}) (rB k K x {i}) (fun y => Iff.rfl) hf1 (GlobalTheory.T.integralClosure_projective_over_standardOpenRing k F K d x hx i) W _
      (hstab {i}) hB1 hB2
  refine ⟨fun i => ?_, fun i => (key i).2, fun I i hi => GlobalTheory.T.pulledBackForms_intersection_eq_chart_localization k F K d x hx p W e I i hi⟩
  obtain ⟨hfin, -⟩ := key i
  obtain ⟨-, hf2, -⟩ := GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x hx {i} (Finset.singleton_nonempty i)
  haveI := hf2
  haveI : FiniteDimensional F K := hx.fin
  set S : Set W := ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W) with hSdef
  obtain ⟨s, hs⟩ := Module.Finite.iff_fg.1 hfin
  have hA : ∀ a : rA k x {i}, ∀ w ∈ S, a • w ∈ S := by
    intro a w hw
    rw [Subalgebra.smul_def, ← algebraMap_smul K (a : F) w]
    exact hstab {i} _ (Subalgebra.algebraMap_mem (integralClosure (rA k x {i}) K) a) w hw
  have hspan : (Submodule.span (rA k x {i}) S).restrictScalars k =
      (omB k K (rB k K x {i}) p).comap (e.restrictScalars k) := by
    apply le_antisymm
    · intro y hy
      change y ∈ Submodule.span (rA k x {i}) S at hy
      change y ∈ S
      induction hy using Submodule.span_induction with
      | mem z hz => exact hz
      | zero => exact Submodule.zero_mem _
      | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
      | smul a z _ hz => exact hA a z hz
    · exact fun y hy => Submodule.subset_span hy
  refine ⟨s, by rw [hs, hspan], ?_⟩
  have hK := GlobalTheory.T.kahlerFormsOverSubalgebra_comap_span_eq_top k K (rB k K x {i}) p W e he hr
  have hF := GlobalTheory.T.span_eq_top_of_stable_of_isFractionRing' k F K (rB k K x {i}) W S (hstab {i}) hK
  rw [eq_top_iff, ← hF, Submodule.span_le]
  intro w hw
  have : w ∈ Submodule.span (rA k x {i}) (s : Set W) := by rw [hs]; exact Submodule.subset_span hw
  exact Submodule.span_le_restrictScalars (rA k x {i}) F (s : Set W) this

end GlobalTheory.PD
end
end

section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularForms_isBundle_projectiveCover : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module F W] [Module k W] [IsScalarTower F K W] [IsScalarTower k F W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K), Function.Injective e → LinearMap.range e = ⋀[K]^p Ω[K⁄k] → IsBundle k x fun I => (omB k K (rB k K x I) p).comap (e.restrictScalars k) := by
  first | (exact @GlobalTheory.PD.omB_isBundle) | (exact GlobalTheory.PD.omB_isBundle) | (intros; apply GlobalTheory.PD.omB_isBundle  <;> assumption)
end
