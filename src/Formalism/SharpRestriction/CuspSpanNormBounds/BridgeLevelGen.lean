import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLevelGenB
import Formalism.FlagUnipotentLattices.FlagUnipotentLatticeOfRel

section
noncomputable section

namespace Formalism.MainNotions.BridgeLevelIdx

open MeasureTheory Formalism.MainNotions.S Matrix
open scoped ENNReal TensorProduct

variable (I : AutInst)

def LevelGen (g : ℕ) : Prop :=
  ∃ (m : ℕ) (l : Fin m → (Fin I.n → I.E ⊗[I.F] Af I.F)) (S : Finset (Fin I.n → I.E ⊗[I.F] Af I.F)),
    m ≤ I.n ∧ S.card ≤ g ^ (2 * I.f * I.n) ∧ (∀ j, l j ∈ I.Lf) ∧
    (∀ y ∈ I.Lf, ∃ (a : Fin m → IntAf I.F I.E) (z : Fin I.n → I.E ⊗[I.F] Af I.F), z ∈ I.Lf ∧
      y = ∑ j, (a j : I.E ⊗[I.F] Af I.F) • l j + (g : I.E ⊗[I.F] Af I.F) • z) ∧
    ∀ y ∈ I.Lf, ∃ s ∈ S, ∃ z ∈ I.Lf, y = s + (g : I.E ⊗[I.F] Af I.F) • z

variable {I}

theorem lf_csmul (a : IntAf I.F I.E) {z : Fin I.n → I.E ⊗[I.F] Af I.F} (hz : z ∈ I.Lf) :
    (a : I.E ⊗[I.F] Af I.F) • z ∈ I.Lf :=
  I.Lf.smul_mem a hz

theorem kset_mulVec {x : I.Gf} (hx : x ∈ I.Kset) {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    I.fmat x *ᵥ y ∈ I.Lf :=
  (hx y).1 hy

theorem kset_inv_mulVec {x : I.Gf} (hx : x ∈ I.Kset) {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    I.fmat x⁻¹ *ᵥ y ∈ I.Lf := by
  have h : x⁻¹ ∈ I.Kset := by
    show ((x⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
    rw [Subgroup.coe_inv]
    exact (Formalism.UG.stabGL I.Lf).inv_mem hx
  exact (h y).1 hy

theorem kset_mul {x x' : I.Gf} (hx : x ∈ I.Kset) (hx' : x' ∈ I.Kset) : x⁻¹ * x' ∈ I.Kset := by
  show ((x⁻¹ * x' : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
  rw [Subgroup.coe_mul, Subgroup.coe_inv]
  exact (Formalism.UG.stabGL I.Lf).mul_mem ((Formalism.UG.stabGL I.Lf).inv_mem hx) hx'

theorem kg_of_gen {g : ℕ} {m : ℕ} {l : Fin m → (Fin I.n → I.E ⊗[I.F] Af I.F)}
    (hgen : ∀ y ∈ I.Lf, ∃ (a : Fin m → IntAf I.F I.E) (z : Fin I.n → I.E ⊗[I.F] Af I.F), z ∈ I.Lf ∧
      y = ∑ j, (a j : I.E ⊗[I.F] Af I.F) • l j + (g : I.E ⊗[I.F] Af I.F) • z)
    {x x' : I.Gf} (hx : x ∈ I.Kset) (hx' : x' ∈ I.Kset)
    (hd : ∀ j, ∃ w ∈ I.Lf, (I.fmat x' - I.fmat x) *ᵥ l j = (g : I.E ⊗[I.F] Af I.F) • w) :
    x⁻¹ * x' ∈ I.Kg g := by
  refine ⟨kset_mul hx hx', fun y hy => ?_⟩
  set D := I.fmat x' - I.fmat x with hD

  have hDy : ∃ w ∈ I.Lf, D *ᵥ y = (g : I.E ⊗[I.F] Af I.F) • w := by
    obtain ⟨a, z, hz, rfl⟩ := hgen y hy
    have hsum : ∀ s : Finset (Fin m), ∃ w ∈ I.Lf,
        D *ᵥ (∑ j ∈ s, (a j : I.E ⊗[I.F] Af I.F) • l j) = (g : I.E ⊗[I.F] Af I.F) • w := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact ⟨0, I.Lf.zero_mem, by simp⟩
      | insert j s hj ih =>
        obtain ⟨w, hw, e⟩ := ih
        obtain ⟨w', hw', e'⟩ := hd j
        refine ⟨(a j : I.E ⊗[I.F] Af I.F) • w' + w, I.Lf.add_mem (lf_csmul _ hw') hw, ?_⟩
        rw [Finset.sum_insert hj, Matrix.mulVec_add, Matrix.mulVec_smul, e, e', smul_add, smul_comm]
    obtain ⟨w, hw, e⟩ := hsum Finset.univ
    refine ⟨w + D *ᵥ z, I.Lf.add_mem hw ?_, ?_⟩
    · rw [hD, Matrix.sub_mulVec]
      exact I.Lf.sub_mem (kset_mulVec hx' hz) (kset_mulVec hx hz)
    · rw [Matrix.mulVec_add, e, Matrix.mulVec_smul, smul_add]
  obtain ⟨w, hw, e⟩ := hDy
  refine ⟨I.fmat x⁻¹ *ᵥ w, kset_inv_mulVec hx hw, ?_⟩
  have hm : I.fmat (x⁻¹ * x') - 1 = I.fmat x⁻¹ * D := by
    have h1 : I.fmat (x⁻¹ * x') = I.fmat x⁻¹ * I.fmat x' := by
      simp only [AutInst.fmat, Subgroup.coe_mul, Units.val_mul]
    have h2 : I.fmat x⁻¹ * I.fmat x = 1 := by
      simp only [AutInst.fmat, Subgroup.coe_inv, Units.inv_mul]
    rw [hD, Matrix.mul_sub, h1, h2]
  rw [hm, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_smul]

theorem card_reduction {g : ℕ} (hg : 1 ≤ g) (hG : LevelGen I g) :
    ∃ (α : Type) (_ : Fintype α) (ρ : I.Gf → α), Fintype.card α ≤ g ^ (2 * I.n ^ 2 * I.f) ∧
      ∀ x ∈ I.Kset, ∀ x' ∈ I.Kset, ρ x = ρ x' → x⁻¹ * x' ∈ I.Kg g := by
  classical
  obtain ⟨m, l, S, hm, hS, hl, hgen, hrep⟩ := hG
  obtain ⟨s0, hs0, -⟩ := hrep 0 I.Lf.zero_mem
  let r : (Fin I.n → I.E ⊗[I.F] Af I.F) → S := fun v =>
    if h : v ∈ I.Lf then ⟨(hrep v h).choose, (hrep v h).choose_spec.1⟩ else ⟨s0, hs0⟩
  have hr : ∀ v ∈ I.Lf, ∃ z ∈ I.Lf, v = (r v : Fin I.n → I.E ⊗[I.F] Af I.F) + (g : I.E ⊗[I.F] Af I.F) • z := by
    intro v hv
    simp only [r, dif_pos hv]
    exact (hrep v hv).choose_spec.2
  refine ⟨Fin m → S, inferInstance, fun x j => r (I.fmat x *ᵥ l j), ?_, ?_⟩
  · rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
    calc S.card ^ m ≤ (g ^ (2 * I.f * I.n)) ^ m := Nat.pow_le_pow_left hS m
      _ ≤ (g ^ (2 * I.f * I.n)) ^ I.n := Nat.pow_le_pow_right (pow_pos (by omega) _) hm
      _ = g ^ (2 * I.n ^ 2 * I.f) := by rw [← pow_mul]; congr 1; ring
  · intro x hx x' hx' hρ
    refine kg_of_gen hgen hx hx' fun j => ?_
    have e : r (I.fmat x *ᵥ l j) = r (I.fmat x' *ᵥ l j) := congrFun hρ j
    obtain ⟨z, hz, ez⟩ := hr _ (kset_mulVec hx (hl j))
    obtain ⟨z', hz', ez'⟩ := hr _ (kset_mulVec hx' (hl j))
    refine ⟨z' - z, I.Lf.sub_mem hz' hz, ?_⟩
    rw [Matrix.sub_mulVec, ez, ez', e, smul_sub]
    abel

theorem levelIdx_holds (μf : Measure I.Gf) [μf.IsMulLeftInvariant] {g : ℕ} (hg : 1 ≤ g) (hG : LevelGen I g) :
    μf I.Kset ≤ ((g ^ (2 * I.n ^ 2 * I.f) : ℕ) : ℝ≥0∞) * μf (I.Kg g) := by
  classical
  obtain ⟨α, _, ρ, hcard, hρ⟩ := card_reduction hg hG
  let rp : α → I.Gf := fun a => if h : ∃ x ∈ I.Kset, ρ x = a then h.choose else 1
  have hcov : I.Kset ⊆ ⋃ a, (fun h => rp a * h) '' I.Kg g := by
    intro x hx
    have hex : ∃ x₀ ∈ I.Kset, ρ x₀ = ρ x := ⟨x, hx, rfl⟩
    refine Set.mem_iUnion.2 ⟨ρ x, (rp (ρ x))⁻¹ * x, ?_, by simp⟩
    have e : rp (ρ x) = hex.choose := by simp only [rp, dif_pos hex]
    rw [e]
    exact hρ _ hex.choose_spec.1 x hx hex.choose_spec.2
  have hone : ∀ a, μf ((fun h => rp a * h) '' I.Kg g) = μf (I.Kg g) := by
    intro a
    rw [Set.image_mul_left]
    exact measure_preimage_mul μf _ _
  calc μf I.Kset ≤ μf (⋃ a, (fun h => rp a * h) '' I.Kg g) := measure_mono hcov
    _ ≤ ∑ a, μf ((fun h => rp a * h) '' I.Kg g) := measure_iUnion_fintype_le _ _
    _ = (Fintype.card α : ℝ≥0∞) * μf (I.Kg g) := by
        simp only [hone, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := by gcongr

end Formalism.MainNotions.BridgeLevelIdx

end
end

section
noncomputable section

namespace Formalism.MainNotions.BridgeLevelGenA

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

def coprS (g : R) : Submonoid R where
  carrier := {s | IsCoprime s g ∧ s ≠ 0}
  one_mem' := ⟨isCoprime_one_left, one_ne_zero⟩
  mul_mem' := fun {_ _} ha hb => ⟨IsCoprime.mul_left ha.1 hb.1, mul_ne_zero ha.2 hb.2⟩

theorem coprS_le (g : R) : coprS g ≤ R⁰ := fun _ hs => mem_nonZeroDivisors_of_ne_zero hs.2

theorem mem_of_disjoint (g : R) {P : Ideal R} (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hd : Disjoint (coprS g : Set R) (P : Set R)) : g ∈ P := by
  by_contra hgP
  have hmax : P.IsMaximal := hP.isMaximal hP0
  have htop : P ⊔ Ideal.span {g} = ⊤ := by
    by_contra h
    have e := hmax.eq_of_le h le_sup_left
    apply hgP
    rw [e]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self g)
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : (1 : R) ∈ P ⊔ Ideal.span {g})
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hc
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  by_cases ha0 : a = 0
  · subst ha0
    have hco : IsCoprime p g := ⟨0, d, by simpa using hac⟩
    exact Set.disjoint_left.1 hd ⟨hco, hp0⟩ hp
  · have hco : IsCoprime a g := ⟨1, d, by rw [one_mul]; exact hac⟩
    exact Set.disjoint_left.1 hd ⟨hco, ha0⟩ ha

theorem primes_finite (g : R) (hg : g ≠ 0) :
    {P : Ideal R | P.IsPrime ∧ Disjoint (coprS g : Set R) (P : Set R)}.Finite := by
  have hI : Ideal.span {g} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hg
  refine ((Ideal.finite_factors hI).image (fun v => v.asIdeal)).insert ⊥ |>.subset ?_
  rintro P ⟨hP, hd⟩
  by_cases hP0 : P = ⊥
  · exact Or.inl hP0
  · refine Or.inr ⟨⟨P, hP, hP0⟩, ?_, rfl⟩
    show P ∣ Ideal.span {g}
    rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
    exact mem_of_disjoint g hP hP0 hd

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

theorem gen_mod (g : R) (hg : g ≠ 0) {n : ℕ} (L : Submodule R (Fin n → K)) (hL : L.FG) :
    ∃ (m : ℕ) (ℓ : Fin m → (Fin n → K)), m ≤ n ∧ (∀ j, ℓ j ∈ L) ∧
      ∀ x ∈ L, ∃ (a : Fin m → R) (w : Fin n → K), w ∈ L ∧ x = ∑ j, a j • ℓ j + g • w := by
  classical
  set S := coprS g with hSdef
  let A := Localization.subalgebra.ofField K S (coprS_le g)
  have : IsDedekindDomain A := IsLocalization.isDedekindDomain R (coprS_le g) A
  have : IsFractionRing A K := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization S A K
  have : IsPrincipalIdealRing A := by
    refine IsPrincipalIdealRing.of_finite_primes ?_
    refine ((primes_finite g hg).preimage (IsLocalization.orderEmbedding S A).injective.injOn).subset ?_
    intro J hJ
    exact (IsLocalization.isPrime_iff_isPrime_disjoint S A J).1 hJ
  let M : Submodule A (Fin n → K) := Submodule.span A (L : Set (Fin n → K))
  have : Module.Finite A M := by
    obtain ⟨s, hs⟩ := hL
    have e : M = Submodule.span A (s : Set (Fin n → K)) := by
      show Submodule.span A (L : Set (Fin n → K)) = _
      rw [← hs, Submodule.span_span_of_tower]
    rw [Module.Finite.iff_fg, e]
    exact ⟨s, rfl⟩
  have : Module.IsTorsionFree A M := by
    refine ⟨fun r hr x y hxy => Subtype.ext ?_⟩
    have hr0 : (r : K) ≠ 0 := by
      intro h
      exact hr.ne_zero (Subtype.ext (by simpa using h))
    have h := congrArg (fun z : M => (z : Fin n → K)) hxy
    simp only [Submodule.coe_smul, Subalgebra.smul_def] at h
    exact smul_right_injective _ hr0 h
  have : Module.Free A M := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex A M
  let b : Module.Basis ι A M := Module.Free.chooseBasis A M

  have hcard : Fintype.card ι ≤ n := by
    have hli : LinearIndependent A (fun i => (b i : Fin n → K)) :=
      b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
    have hK := (LinearIndependent.iff_fractionRing A K).1 hli
    simpa using hK.fintype_card_le_finrank

  have hden : ∀ v ∈ M, ∃ s ∈ S, algebraMap R K s • v ∈ L := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, S.one_mem, by simpa using hx⟩
    | zero => exact ⟨1, S.one_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨t, ht, hty⟩ := hy
      refine ⟨s * t, S.mul_mem hs ht, ?_⟩
      have e : algebraMap R K (s * t) • (x + y) = t • (algebraMap R K s • x) + s • (algebraMap R K t • y) := by
        rw [smul_add, ← algebraMap_smul K t (algebraMap R K s • x), ← algebraMap_smul K s (algebraMap R K t • y),
          smul_smul, smul_smul, ← map_mul, ← map_mul, mul_comm t s]
      rw [e]
      exact L.add_mem (L.smul_mem t hsx) (L.smul_mem s hty)
    | smul a x _ hx =>
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨⟨r, t⟩, hrt⟩ := IsLocalization.mk'_surjective S a
      refine ⟨t * s, S.mul_mem t.2 hs, ?_⟩
      have ha : (a : K) * algebraMap R K t = algebraMap R K r := by
        rw [← hrt]
        have h2 : ((IsLocalization.mk' A r t * algebraMap R A t : A) : K) = ((algebraMap R A r : A) : K) :=
          congrArg Subtype.val (IsLocalization.mk'_spec A r t)
        rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap] at h2
        exact h2
      have e : algebraMap R K (t * s) • (a • x) = r • (algebraMap R K s • x) := by
        rw [Subalgebra.smul_def, smul_smul, ← algebraMap_smul K r, smul_smul, map_mul, ← ha]
        congr 1; ring
      rw [e]
      exact L.smul_mem r hsx
  choose sd hsd hsdL using fun i => hden (b i : Fin n → K) (b i).2
  set s : R := ∏ i, sd i with hs
  have hsS : s ∈ S := S.prod_mem fun i _ => hsd i
  let ℓ : ι → (Fin n → K) := fun i => algebraMap R K s • (b i : Fin n → K)
  have hℓ : ∀ i, ℓ i ∈ L := by
    intro i
    obtain ⟨c, hc⟩ : sd i ∣ s := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have e : ℓ i = c • (algebraMap R K (sd i) • (b i : Fin n → K)) := by
      show algebraMap R K s • (b i : Fin n → K) = _
      rw [hc, ← algebraMap_smul K c, smul_smul, ← map_mul, mul_comm c (sd i)]
    rw [e]
    exact L.smul_mem c (hsdL i)

  have hx : ∀ x ∈ L, ∃ (a : ι → R) (w : Fin n → K), w ∈ L ∧ x = ∑ i, a i • ℓ i + g • w := by
    intro x hxL
    have hxM : x ∈ M := Submodule.subset_span hxL
    set c := b.repr ⟨x, hxM⟩ with hc
    obtain ⟨t, ht⟩ := IsLocalization.exist_integer_multiples S Finset.univ (fun i => c i)
    choose r hr using fun i => ht i (Finset.mem_univ i)
    have hsum : x = ∑ i, (c i : K) • (b i : Fin n → K) := by
      have := congrArg (fun z : M => (z : Fin n → K)) (b.sum_repr ⟨x, hxM⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul, Subalgebra.smul_def] at this
      rw [← hc] at this
      exact this.symm
    have hri : ∀ i, algebraMap R K (r i) = algebraMap R K (t : R) * (c i : K) := by
      intro i
      have h2 : ((algebraMap R A (r i) : A) : K) = (((t : R) • c i : A) : K) := congrArg Subtype.val (hr i)
      rw [Subalgebra.coe_algebraMap, Algebra.smul_def, Subalgebra.coe_mul, Subalgebra.coe_algebraMap] at h2
      exact h2
    set u : R := (t : R) * s with hu_def
    have hux : algebraMap R K u • x = ∑ i, r i • ℓ i := by
      rw [hsum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      show _ = r i • (algebraMap R K s • (b i : Fin n → K))
      rw [← algebraMap_smul K (r i), smul_smul, smul_smul, hri, hu_def, map_mul]
      congr 1; ring
    have hu : u ∈ S := S.mul_mem t.2 hsS
    obtain ⟨α, β, hαβ⟩ := hu.1
    refine ⟨fun i => α * r i, β • x, L.smul_mem β hxL, ?_⟩
    have h1 : algebraMap R K α * algebraMap R K u + algebraMap R K g * algebraMap R K β = 1 := by
      rw [← map_mul, ← map_mul, ← map_add, mul_comm g β, hαβ, map_one]
    calc x = (algebraMap R K α * algebraMap R K u + algebraMap R K g * algebraMap R K β) • x := by
          rw [h1, one_smul]
      _ = α • (algebraMap R K u • x) + g • (β • x) := by
          rw [add_smul, ← smul_smul, ← smul_smul, algebraMap_smul K α, algebraMap_smul K g, algebraMap_smul K β]
      _ = _ := by
          rw [hux, Finset.smul_sum]
          simp only [smul_smul]

  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun j => ℓ (e.symm j), hcard, fun j => hℓ _, fun x hxL => ?_⟩
  obtain ⟨a, w, hw, hxw⟩ := hx x hxL
  refine ⟨fun j => a (e.symm j), w, hw, ?_⟩
  rw [hxw]
  congr 1
  exact (Equiv.sum_comp e.symm (fun i => a i • ℓ i)).symm

end Formalism.MainNotions.BridgeLevelGenA

end
end

section
noncomputable section

namespace Formalism.MainNotions.BridgeLevelGen

open MeasureTheory NumberField Formalism.MainNotions.S Formalism.MainNotions.BridgeLevelIdx
open scoped ENNReal TensorProduct

theorem finrank_E (I : AutInst) : Module.finrank ℚ I.E = 2 * I.f := by
  rw [← Module.finrank_mul_finrank ℚ I.F I.E, I.cm.deg2]
  show _ = 2 * Module.finrank ℚ I.F
  ring

theorem incl_mem (I : AutInst) (b : 𝓞 I.E) :
    Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E b) ∈ IntAf I.F I.E :=
  Subring.subset_closure (Or.inl ⟨⟨_, ⟨b, rfl⟩⟩, rfl⟩)

theorem levelGen_holds (I : AutInst) (g : ℕ) (hg : 1 ≤ g) : LevelGen I g := by
  classical
  have hg0 : ((g : 𝓞 I.E)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨m, ℓ, hm, hℓ, hgen⟩ :=
    Formalism.MainNotions.BridgeLevelGenA.gen_mod (R := 𝓞 I.E) (K := I.E) (g : 𝓞 I.E) hg0 I.L I.L_fg
  set ι : (Fin I.n → I.E) → (Fin I.n → I.E ⊗[I.F] Af I.F) :=
    fun x i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i) with hι
  have hιL : ∀ x ∈ I.L, ι x ∈ I.Lf := fun x hx => Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩

  have hgenA : ∀ y ∈ I.Lf, ∃ (a : Fin m → IntAf I.F I.E) (z : Fin I.n → I.E ⊗[I.F] Af I.F), z ∈ I.Lf ∧
      y = ∑ j, (a j : I.E ⊗[I.F] Af I.F) • ι (ℓ j) + (g : I.E ⊗[I.F] Af I.F) • z := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨x, hx⟩, rfl⟩ := hy
      obtain ⟨a, w, hw, hxw⟩ := hgen x hx
      refine ⟨fun j => ⟨_, incl_mem I (a j)⟩, ι w, hιL w hw, ?_⟩
      show ι x = _
      rw [hxw]
      funext i
      simp only [hι, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def, map_add, map_sum, map_mul, map_natCast]
    | zero => exact ⟨0, 0, I.Lf.zero_mem, by simp⟩
    | add y y' _ _ hy hy' =>
      obtain ⟨a, z, hz, rfl⟩ := hy
      obtain ⟨a', z', hz', rfl⟩ := hy'
      refine ⟨a + a', z + z', I.Lf.add_mem hz hz', ?_⟩
      simp only [Pi.add_apply, Subring.coe_add, add_smul, Finset.sum_add_distrib, smul_add]
      abel
    | smul c y _ hy =>
      obtain ⟨a, z, hz, rfl⟩ := hy
      refine ⟨fun j => c * a j, (c : I.E ⊗[I.F] Af I.F) • z, lf_csmul c hz, ?_⟩
      rw [Subring.smul_def]
      simp only [smul_add, Finset.smul_sum, smul_smul, Subring.coe_mul]
      rw [mul_comm (c : I.E ⊗[I.F] Af I.F) (g : I.E ⊗[I.F] Af I.F)]

  let Q := 𝓞 I.E ⧸ Ideal.span {(g : 𝓞 I.E)}
  have hQ : Nat.card Q = g ^ (2 * I.f) := by
    rw [← finrank_E]; exact Formalism.HermitianLatticeCounting.Final.FlagKernelVanishing.residueRingCard I.E g
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; positivity)
  letI : Fintype Q := Fintype.ofFinite Q
  let R' : Finset (𝓞 I.E) := Finset.univ.image (fun q : Q => q.out)
  have hR' : R'.card ≤ g ^ (2 * I.f) := by
    calc R'.card ≤ (Finset.univ : Finset Q).card := Finset.card_image_le
      _ = g ^ (2 * I.f) := by rw [Finset.card_univ, Fintype.card_eq_nat_card, hQ]
  let S : Finset (Fin I.n → I.E ⊗[I.F] Af I.F) := Finset.univ.image (fun b : Fin m → R' =>
    ∑ j, Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E (b j : 𝓞 I.E)) • ι (ℓ j))
  have hS : S.card ≤ g ^ (2 * I.f * I.n) := by
    calc S.card ≤ (Finset.univ : Finset (Fin m → R')).card := Finset.card_image_le
      _ = R'.card ^ m := by simp
      _ ≤ (g ^ (2 * I.f)) ^ m := Nat.pow_le_pow_left hR' m
      _ ≤ (g ^ (2 * I.f)) ^ I.n := Nat.pow_le_pow_right (pow_pos (by omega) _) hm
      _ = g ^ (2 * I.f * I.n) := by rw [← pow_mul]
  refine ⟨m, fun j => ι (ℓ j), S, hm, hS, fun j => hιL _ (hℓ j), hgenA, fun y hy => ?_⟩
  obtain ⟨a, z, hz, rfl⟩ := hgenA y hy
  have hloc : ∀ j, ∃ β : 𝓞 I.E, β ∈ R' ∧ ∃ c ∈ IntAf I.F I.E, (a j : I.E ⊗[I.F] Af I.F) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E β) + (g : I.E ⊗[I.F] Af I.F) * c := by
    intro j
    obtain ⟨b, ⟨β, rfl⟩, c, hc, e⟩ := Formalism.MainNotions.BridgeLevelGenB.dense_modE g hg (a j : I.E ⊗[I.F] Af I.F) (a j).2
    set β' : 𝓞 I.E := (Ideal.Quotient.mk (Ideal.span {(g : 𝓞 I.E)}) β).out with hβ'
    have hmem : β' - β ∈ Ideal.span {(g : 𝓞 I.E)} :=
      Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out _)
    obtain ⟨δ, hδ⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨β', Finset.mem_image_of_mem _ (Finset.mem_univ _),
      c - Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E δ),
      sub_mem hc (incl_mem I δ), ?_⟩
    have hβ : β = β' - δ * (g : 𝓞 I.E) := by rw [hδ]; ring
    rw [e, hβ]
    simp only [map_sub, map_mul, map_natCast, Formalism.UG.inclE, Algebra.TensorProduct.includeLeftRingHom_apply]
    rw [TensorProduct.sub_tmul, show (algebraMap (𝓞 I.E) I.E δ * (g : I.E)) ⊗ₜ[I.F] (1 : Af I.F) =
      (algebraMap (𝓞 I.E) I.E δ) ⊗ₜ[I.F] (1 : Af I.F) * (g : I.E ⊗[I.F] Af I.F) by
        rw [← map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := I.F) (B := Af I.F)) g,
          Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]]
    ring
  choose β hβR c hc hac using hloc
  refine ⟨∑ j, Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E (β j)) • ι (ℓ j),
    Finset.mem_image.2 ⟨fun j => ⟨β j, hβR j⟩, Finset.mem_univ _, rfl⟩,
    ∑ j, (c j : I.E ⊗[I.F] Af I.F) • ι (ℓ j) + z, ?_, ?_⟩
  · refine I.Lf.add_mem (Submodule.sum_mem _ fun j _ => ?_) hz
    exact lf_csmul ⟨c j, hc j⟩ (hιL _ (hℓ j))
  · simp only [hac, add_smul, Finset.sum_add_distrib, smul_add, Finset.smul_sum, smul_smul]
    abel

theorem levelIdx (I : AutInst) (μf : Measure I.Gf) [μf.IsMulLeftInvariant] {g : ℕ} (hg : 1 ≤ g) :
    μf I.Kset ≤ ((g ^ (2 * I.n ^ 2 * I.f) : ℕ) : ℝ≥0∞) * μf (I.Kg g) :=
  levelIdx_holds μf hg (levelGen_holds I g hg)

end Formalism.MainNotions.BridgeLevelGen

end
end
