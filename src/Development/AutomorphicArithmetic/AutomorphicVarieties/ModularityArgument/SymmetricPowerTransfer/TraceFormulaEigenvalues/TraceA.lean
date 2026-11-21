import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.IsGenEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.RepIndep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.FormsFin

section
open MulAction

namespace UpperTheory.V.Z.Sym.Tf

variable {Γ Y V : Type} [Group Γ] [MulAction Γ Y] [AddCommGroup V] [Module ℂ V]

theorem sum_fib {A B : Type} (m : A → B) (F : A → V) (F' : B → V) (c : B → ℕ) (hB : (Function.support F').Finite)
    (hc : ∀ b, F' b ≠ 0 → c b ≠ 0 ∧ Nat.card {a // m a = b} = c b) (hF : ∀ a, F a = (c (m a) : ℂ)⁻¹ • F' (m a)) :
    (Function.support F).Finite ∧ ∑ᶠ a, F a = ∑ᶠ b, F' b := by
  classical
  have hfibfin : ∀ b, F' b ≠ 0 → {a | m a = b}.Finite := by
    intro b hb
    have h1 := hc b hb
    have hne : Nat.card {a // m a = b} ≠ 0 := by rw [h1.2]; exact h1.1
    exact Set.finite_coe_iff.mp (Nat.finite_of_card_ne_zero hne)
  have hsuppF : Function.support F ⊆ ⋃ b ∈ Function.support F', {a | m a = b} := by
    intro a ha
    refine Set.mem_iUnion₂.mpr ⟨m a, fun h0 => ha ?_, rfl⟩
    rw [hF, h0, smul_zero]
  have hfin : (Function.support F).Finite :=
    (hB.biUnion fun b hb => hfibfin b hb).subset hsuppF
  refine ⟨hfin, ?_⟩
  set s := hfin.toFinset with hs
  set T := hB.toFinset with hT
  rw [finsum_eq_sum_of_support_subset F (s := s) (by simp [s]),
    finsum_eq_sum_of_support_subset F' (s := T) (by simp [T])]
  have hmaps : ∀ a ∈ s, m a ∈ T := by
    intro a ha
    have ha' : F a ≠ 0 := by simpa [s] using ha
    have : F' (m a) ≠ 0 := fun h0 => ha' (by rw [hF, h0, smul_zero])
    simpa [T] using this
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun b hbT => ?_
  have hb' : F' b ≠ 0 := by simpa [T] using hbT
  obtain ⟨hcb, hcard⟩ := hc b hb'
  have hset : (↑(s.filter (fun a => m a = b)) : Set A) = {a | m a = b} := by
    ext a
    simp only [Finset.coe_filter, Set.mem_setOf_eq, s, Set.Finite.mem_toFinset, Function.mem_support]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rw [hF, h]
      exact smul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr hcb)) hb'
  have hcard' : (s.filter (fun a => m a = b)).card = c b := by
    rw [← Set.ncard_coe_finset, hset, ← Nat.card_coe_set_eq]
    exact hcard
  rw [Finset.sum_congr rfl (g := fun _ => (c b : ℂ)⁻¹ • F' b)]
  · rw [Finset.sum_const, hcard', ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hcb), one_smul]
  · intro a ha
    rw [Finset.mem_filter] at ha
    rw [hF, ha.2]

theorem rel_smul (Γ₀ : Subgroup Γ) [Γ₀.Normal] (g : Γ) (y : Y) :
    Γ₀.relIndex (stabilizer Γ (g • y)) = Γ₀.relIndex (stabilizer Γ y) := by
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  conv_lhs => rw [← Subgroup.Normal.map_conj_eq Γ₀ g]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective

theorem card_fib (H : Subgroup Γ) (b : orbitRel.Quotient H Y) :
    Nat.card {a : orbitRel.Quotient Γ Y × (Γ ⧸ H) // (Quotient.mk'' (a.2.out⁻¹ • a.1.out) : orbitRel.Quotient H Y) = b} =
      H.relIndex (stabilizer Γ b.out) := by
  classical
  set y0 := b.out with hy0
  set O0 : orbitRel.Quotient Γ Y := Quotient.mk'' y0 with hO0
  obtain ⟨t, ht⟩ : ∃ t : Γ, t • y0 = O0.out := by
    have h1 : (orbitRel Γ Y) O0.out y0 := Quotient.exact' (Quotient.out_eq' O0)
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h1
    exact h1
  have hbq : (Quotient.mk'' y0 : orbitRel.Quotient H Y) = b := Quotient.out_eq' b
  have hinv : ∀ s : stabilizer Γ y0, (s : Γ)⁻¹ • y0 = y0 := fun s =>
    inv_smul_eq_iff.mpr (MulAction.mem_stabilizer_iff.mp s.2).symm
  have hmem : ∀ s : stabilizer Γ y0,
      (Quotient.mk'' ((((t * (s : Γ) : Γ) : Γ ⧸ H)).out⁻¹ • O0.out) : orbitRel.Quotient H Y) = b := by
    intro s
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H (t * (s : Γ))
    rw [hh, ← ht, smul_smul]
    have e1 : (t * (s : Γ) * (h : Γ))⁻¹ * t = (h : Γ)⁻¹ * (s : Γ)⁻¹ := by group
    rw [e1, mul_smul, hinv s, ← hbq]
    exact Quotient.sound' (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨h⁻¹, rfl⟩))
  let Fib := {a : orbitRel.Quotient Γ Y × (Γ ⧸ H) //
    (Quotient.mk'' (a.2.out⁻¹ • a.1.out) : orbitRel.Quotient H Y) = b}
  let F : stabilizer Γ y0 → Fib := fun s => ⟨(O0, ((t * (s : Γ) : Γ) : Γ ⧸ H)), hmem s⟩
  have hF : ∀ s1 s2 : stabilizer Γ y0, F s1 = F s2 ↔ s1⁻¹ * s2 ∈ H.subgroupOf (stabilizer Γ y0) := by
    intro s1 s2
    rw [Subgroup.mem_subgroupOf]
    have e2 : (t * (s1 : Γ))⁻¹ * (t * (s2 : Γ)) = ((s1⁻¹ * s2 : stabilizer Γ y0) : Γ) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    constructor
    · intro h12
      have h3 : ((t * (s1 : Γ) : Γ) : Γ ⧸ H) = ((t * (s2 : Γ) : Γ) : Γ ⧸ H) :=
        congrArg (fun z : Fib => z.1.2) h12
      have h4 := QuotientGroup.eq.mp h3
      rw [e2] at h4
      exact h4
    · intro h12
      apply Subtype.ext
      refine Prod.ext rfl (QuotientGroup.eq.mpr ?_)
      show (t * (s1 : Γ))⁻¹ * (t * (s2 : Γ)) ∈ H
      rw [e2]
      exact h12
  have hsurj : Function.Surjective F := by
    rintro ⟨⟨O, q⟩, hq⟩
    obtain ⟨h, hh⟩ : ∃ h : H, (h : Γ) • y0 = q.out⁻¹ • O.out := by
      have h1 : (orbitRel H Y) (q.out⁻¹ • O.out) y0 := Quotient.exact' (hq.trans hbq.symm)
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h1
      exact h1
    have hO : O = O0 := by
      rw [← Quotient.out_eq' O]
      exact Quotient.sound' (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr
        ⟨q.out * h, by rw [mul_smul, hh, smul_inv_smul]⟩))
    subst hO
    refine ⟨⟨t⁻¹ * q.out * h, ?_⟩, ?_⟩
    · rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hh, smul_inv_smul, ← ht, inv_smul_smul]
    · apply Subtype.ext
      refine Prod.ext rfl ?_
      show ((t * (t⁻¹ * q.out * (h : Γ)) : Γ) : Γ ⧸ H) = q
      rw [show t * (t⁻¹ * q.out * (h : Γ)) = q.out * (h : Γ) by group,
        QuotientGroup.mk_mul_of_mem _ h.2, QuotientGroup.out_eq']
  rw [Subgroup.relIndex, Subgroup.index]
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.lift F fun a b hab => (hF a b).mpr (QuotientGroup.leftRel_apply.mp hab)) ⟨?_, ?_⟩).symm
  · intro x y hxy
    induction x using Quotient.inductionOn'
    induction y using Quotient.inductionOn'
    exact Quotient.sound' (QuotientGroup.leftRel_apply.mpr ((hF _ _).mp hxy))
  · intro z
    obtain ⟨s, rfl⟩ := hsurj z
    exact ⟨Quotient.mk'' s, rfl⟩

theorem countC (Γ₀ H : Subgroup Γ) [Γ₀.Normal] (h0 : ∀ z ∈ Γ₀, ∀ y : Y, z • y = y) (hH : Γ₀ ≤ H)
    (hs : ∀ y : Y, Γ₀.relIndex (stabilizer Γ y) ≠ 0) (k : Y → V) (hk : ∀ h ∈ H, ∀ y, k (h • y) = k y)
    (fin : {b : orbitRel.Quotient H Y | k b.out ≠ 0}.Finite) :
    (Function.support fun a : orbitRel.Quotient Γ Y × (Γ ⧸ H) =>
      (Γ₀.relIndex (stabilizer Γ a.1.out) : ℂ)⁻¹ • k (a.2.out⁻¹ • a.1.out)).Finite ∧
    ∑ᶠ a : orbitRel.Quotient Γ Y × (Γ ⧸ H), (Γ₀.relIndex (stabilizer Γ a.1.out) : ℂ)⁻¹ • k (a.2.out⁻¹ • a.1.out) =
      ∑ᶠ b : orbitRel.Quotient H Y, (Γ₀.relIndex (H ⊓ stabilizer Γ b.out) : ℂ)⁻¹ • k b.out := by
  have hmul : ∀ y : Y, Γ₀.relIndex (H ⊓ stabilizer Γ y) * H.relIndex (stabilizer Γ y) =
      Γ₀.relIndex (stabilizer Γ y) := by
    intro y
    rw [Subgroup.relIndex_inf_mul_relIndex, inf_eq_left.mpr hH]
  have hcne : ∀ y : Y, H.relIndex (stabilizer Γ y) ≠ 0 := fun y h => hs y (by rw [← hmul y, h, mul_zero])
  let m : orbitRel.Quotient Γ Y × (Γ ⧸ H) → orbitRel.Quotient H Y :=
    fun a => Quotient.mk'' (a.2.out⁻¹ • a.1.out)
  have key : ∀ a : orbitRel.Quotient Γ Y × (Γ ⧸ H),
      (Γ₀.relIndex (stabilizer Γ a.1.out) : ℂ)⁻¹ • k (a.2.out⁻¹ • a.1.out) =
      ((H.relIndex (stabilizer Γ (m a).out) : ℕ) : ℂ)⁻¹ •
        ((Γ₀.relIndex (H ⊓ stabilizer Γ (m a).out) : ℂ)⁻¹ • k (m a).out) := by
    intro a
    obtain ⟨h, hh⟩ : ∃ h : H, (h : Γ) • (a.2.out⁻¹ • a.1.out) = (m a).out := by
      have h1 : (orbitRel H Y) (m a).out (a.2.out⁻¹ • a.1.out) := Quotient.exact' (Quotient.out_eq' (m a))
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h1
      exact h1
    have hk' : k (m a).out = k (a.2.out⁻¹ • a.1.out) := by
      rw [← hh]
      exact hk h h.2 _
    have hidx : Γ₀.relIndex (stabilizer Γ (m a).out) = Γ₀.relIndex (stabilizer Γ a.1.out) := by
      rw [← hh, rel_smul, rel_smul]
    rw [smul_smul, ← mul_inv, ← Nat.cast_mul, mul_comm, hmul, hidx, hk']
  have hF'fin : (Function.support fun b : orbitRel.Quotient H Y =>
      (Γ₀.relIndex (H ⊓ stabilizer Γ b.out) : ℂ)⁻¹ • k b.out).Finite := by
    refine fin.subset ?_
    intro b hb hkb
    exact hb (by simp only [hkb, smul_zero])
  exact sum_fib m
    (fun a => (Γ₀.relIndex (stabilizer Γ a.1.out) : ℂ)⁻¹ • k (a.2.out⁻¹ • a.1.out))
    (fun b => (Γ₀.relIndex (H ⊓ stabilizer Γ b.out) : ℂ)⁻¹ • k b.out)
    (fun b => H.relIndex (stabilizer Γ b.out)) hF'fin (fun b _ => ⟨hcne _, card_fib H b⟩) key

theorem finsum_sig {I : Type} {A : I → Type} (F : (Σ i, A i) → ℂ) (h : (Function.support F).Finite) :
    ∑ᶠ a, F a = ∑ᶠ i, ∑ᶠ x, F ⟨i, x⟩ := by
  classical
  set s := h.toFinset with hs
  let t := s.image Sigma.fst
  let u : ∀ i, Finset (A i) := fun i => s.preimage (Sigma.mk i) sigma_mk_injective.injOn
  have hsub : Function.support F ⊆ ↑(t.sigma u) := by
    intro a ha
    have ha' : a ∈ s := by simpa [s] using ha
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, t, u, Finset.mem_image,
      Finset.mem_preimage]
    exact ⟨⟨a, ha', rfl⟩, ha'⟩
  rw [finsum_eq_sum_of_support_subset F hsub, Finset.sum_sigma]
  rw [finsum_eq_sum_of_support_subset (s := t)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    refine (finsum_eq_sum_of_support_subset _ ?_).symm
    intro x hx
    simpa [u, s] using hx
  · intro i hi
    obtain ⟨x, hx⟩ : ∃ x, F ⟨i, x⟩ ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hi (by simp [hc])
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨i, x⟩, by simpa [s] using hx, rfl⟩)

theorem trace_blocks {Q : Type} [Fintype Q] [FiniteDimensional ℂ V] (E : Q → Q → Module.End ℂ V) (L : Module.End ℂ (Q → V))
    (h : ∀ w o', L w o' = ∑ o, E o' o (w o)) : LinearMap.trace ℂ _ L = ∑ o, LinearMap.trace ℂ V (E o o) := by
  classical
  have hL : L = ∑ o', ∑ o, LinearMap.single ℂ (fun _ : Q => V) o' ∘ₗ (E o' o ∘ₗ LinearMap.proj o) := by
    refine LinearMap.ext fun w => funext fun p => ?_
    simp only [h, LinearMap.sum_apply, Finset.sum_apply, LinearMap.comp_apply, LinearMap.coe_proj,
      Function.eval, LinearMap.coe_single, Pi.single_apply]
    rw [Finset.sum_comm]
    simp
  rw [hL, map_sum]
  refine Finset.sum_congr rfl fun o' _ => ?_
  rw [map_sum]
  have hterm : ∀ o, LinearMap.trace ℂ (Q → V)
      (LinearMap.single ℂ (fun _ : Q => V) o' ∘ₗ (E o' o ∘ₗ LinearMap.proj o)) =
      if o = o' then LinearMap.trace ℂ V (E o' o) else 0 := by
    intro o
    rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc]
    split_ifs with hoo
    · subst hoo
      rw [LinearMap.proj_comp_single_same, LinearMap.comp_id]
    · rw [LinearMap.proj_comp_single_ne ℂ _ _ _ hoo, LinearMap.comp_zero, map_zero]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem finsum_triv (Γ₀ : Subgroup Γ) (h0 : ∀ z ∈ Γ₀, ∀ y : Y, z • y = y) (k : Y → V) (hk : (Function.support k).Finite) :
    {b : orbitRel.Quotient Γ₀ Y | k b.out ≠ 0}.Finite ∧
    ∑ᶠ b : orbitRel.Quotient Γ₀ Y, (Γ₀.relIndex (Γ₀ ⊓ stabilizer Γ b.out) : ℂ)⁻¹ • k b.out = ∑ᶠ y, k y := by
  have hrel : ∀ y y' : Y, (orbitRel Γ₀ Y) y y' → y = y' := by
    intro y y' h
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
    obtain ⟨g, hg⟩ := h
    rw [← hg, Subgroup.smul_def]
    exact h0 g g.2 y'
  let e : Y ≃ orbitRel.Quotient Γ₀ Y :=
    { toFun := fun y => Quotient.mk'' y
      invFun := fun b => b.out
      left_inv := fun y => hrel _ _ (Quotient.exact' (Quotient.out_eq' (Quotient.mk'' y : orbitRel.Quotient Γ₀ Y)))
      right_inv := fun b => Quotient.out_eq' b }
  refine ⟨?_, ?_⟩
  · refine (hk.image e).subset ?_
    intro b hb
    exact ⟨b.out, hb, Quotient.out_eq' b⟩
  · have hcoef : ∀ b : orbitRel.Quotient Γ₀ Y, Γ₀.relIndex (Γ₀ ⊓ stabilizer Γ b.out) = 1 :=
      fun b => Subgroup.relIndex_eq_one.mpr inf_le_left
    simp only [hcoef, Nat.cast_one, inv_one, one_smul]
    exact finsum_comp_equiv e.symm (f := k)

end UpperTheory.V.Z.Sym.Tf
end

section
open MulAction

namespace UpperTheory.V.Z.Sym.Tf

variable {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (B : Base Γ G V)

@[reducible] def act : MulAction Γ (G ⧸ B.U) := MulAction.compHom _ B.ι

theorem normal0 : B.Γ₀.Normal := ⟨fun z hz g => by rwa [Subgroup.mem_center_iff.1 (B.cenΓ hz) g, mul_inv_cancel_right]⟩

theorem triv0 : letI := act B; ∀ z ∈ B.Γ₀, ∀ y : G ⧸ B.U, z • y = y := by
  intro z hz y
  induction y using QuotientGroup.induction_on with
  | H g =>
    show ((B.ι z * g : G) : G ⧸ B.U) = g
    rw [← Subgroup.mem_center_iff.1 (B.cenG z hz) g]
    exact QuotientGroup.mk_mul_of_mem _ (B.memU z hz)

theorem stab0 (hB : B.Fin) : letI := act B; ∀ y : G ⧸ B.U, B.Γ₀.relIndex (stabilizer Γ y) ≠ 0 := by
  letI := act B
  intro y
  induction y using QuotientGroup.induction_on with
  | H g =>
    convert hB.stab g
    ext γ
    rw [mem_stabilizer_iff, Subgroup.mem_comap, Subgroup.mem_map_equiv]
    show ((B.ι γ * g : G) : G ⧸ B.U) = g ↔ _
    rw [eq_comm, QuotientGroup.eq]; simp [mul_assoc]

theorem finQ (hB : B.Fin) : letI := act B; Finite (orbitRel.Quotient Γ (G ⧸ B.U)) := by
  letI := act B
  obtain ⟨S, hS⟩ := hB.cls
  refine Finite.of_surjective (fun s : S => (Quotient.mk'' ((s : G) : G ⧸ B.U) : orbitRel.Quotient Γ (G ⧸ B.U))) ?_
  rintro ⟨y⟩
  induction y using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨γ, s, hs, u, hu, rfl⟩ := hS g
    refine ⟨⟨s, hs⟩, Eq.symm (Quotient.sound ?_)⟩
    exact ⟨γ, (QuotientGroup.mk_mul_of_mem _ hu).symm⟩

variable {B} (s : B.Tw) (f : G → ℂ)

noncomputable def Tk (g y : G) (γ : Γ) : Module.End ℂ V := f (g⁻¹ * s.θ (B.ι γ * y)) • (s.Θ ∘ₗ B.W γ)

variable {s f}

theorem twistedKernelSummand_mul_trivialActing (hf : s.IsTest f) (g y : G) (γ : Γ) {z : Γ} (hz : z ∈ B.Γ₀) : Tk s f g y (γ * z) = Tk s f g y γ := by
  ext v
  have := hf.right ⟨_, B.memU z hz⟩ (g⁻¹ * s.θ (B.ι γ * y))
  simp only [Tk, LinearMap.smul_apply, LinearMap.comp_apply]
  rw [map_mul B.ι, mul_assoc (B.ι γ), ← Subgroup.mem_center_iff.1 (B.cenG z hz) y, ← mul_assoc (B.ι γ), map_mul s.θ _ (B.ι z), ← mul_assoc,
    this, map_mul B.W, Module.End.mul_apply, B.scal z hz, map_smul, map_smul, smul_smul, mul_right_comm, ← Units.val_mul]
  simp

theorem Tk_out (hf : s.IsTest f) (g y : G) (γ : Γ) : Tk s f g y ((γ : Γ ⧸ B.Γ₀).out)⁻¹ = Tk s f g y γ⁻¹ := by
  obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul B.Γ₀ γ
  rw [hz, mul_inv_rev, ← Subgroup.mem_center_iff.1 (B.cenΓ (inv_mem z.2)), twistedKernelSummand_mul_trivialActing hf _ _ _ (inv_mem z.2)]

def HD (s : B.Tw) (f : G → ℂ) : Prop :=
  ∀ g g' : G, ∃ D : Finset Γ, ∀ δ, f (g⁻¹ * B.ι δ * s.θ g') ≠ 0 → ∃ d ∈ D, ∃ z ∈ B.Γ₀, δ = d * z

theorem f_fin (hD : HD s f) (g y : G) : {x : Γ ⧸ B.Γ₀ | f (g⁻¹ * s.θ (B.ι x.out⁻¹ * y)) ≠ 0}.Finite := by
  obtain ⟨D, hD⟩ := hD g y
  refine (D.finite_toSet.image fun d => (((s.θΓ.symm d)⁻¹ : Γ) : Γ ⧸ B.Γ₀)).subset fun x hx => ?_
  obtain ⟨d, hd, z, hz, h⟩ := hD (s.θΓ x.out⁻¹) (by rwa [← s.comm, mul_assoc, ← map_mul])
  refine ⟨d, hd, ?_⟩
  have : s.θΓ.symm d = x.out⁻¹ * z⁻¹ := by
    rw [MulEquiv.symm_apply_eq, map_mul, h, s.fix _ (inv_mem hz), mul_inv_cancel_right]
  show (((s.θΓ.symm d)⁻¹ : Γ) : Γ ⧸ B.Γ₀) = x
  rw [this, mul_inv_rev, inv_inv, inv_inv, ← Subgroup.mem_center_iff.1 (B.cenΓ hz), QuotientGroup.mk_mul_of_mem _ hz, QuotientGroup.out_eq']

theorem Tk_fin (hD : HD s f) (g y : G) : (Function.support fun x : Γ ⧸ B.Γ₀ => Tk s f g y x.out⁻¹).Finite :=
  (f_fin hD g y).subset fun x hx h => hx (by simp only [Tk, h, zero_smul])

variable (s f) in

noncomputable def Ek (g y : G) : Module.End ℂ V := ∑ᶠ x : Γ ⧸ B.Γ₀, Tk s f g y x.out⁻¹

theorem Ek_left (hf : s.IsTest f) (hD : HD s f) (γ : Γ) (g y : G) : Ek s f (B.ι γ * g) y = B.W γ * Ek s f g y := by
  haveI := normal0 B
  unfold Ek
  rw [mul_finsum' _ _ (Tk_fin hD g y), ← finsum_comp_equiv (Equiv.mulRight ((s.θΓ.symm γ : Γ) : Γ ⧸ B.Γ₀)) (f := fun x => B.W γ * Tk s f g y x.out⁻¹)]
  refine finsum_congr fun x => ?_
  have e : (Equiv.mulRight ((s.θΓ.symm γ : Γ) : Γ ⧸ B.Γ₀)) x = ((x.out * s.θΓ.symm γ : Γ) : Γ ⧸ B.Γ₀) := by simp
  rw [e, Tk_out hf]
  obtain ⟨γ, rfl⟩ := s.θΓ.surjective γ
  ext v
  simp only [Tk, LinearMap.smul_apply, LinearMap.comp_apply, Module.End.mul_apply, MulEquiv.symm_apply_apply, map_smul, ← s.int, ← s.comm]
  rw [← Module.End.mul_apply (B.W γ), ← map_mul]
  simp [mul_assoc]

theorem Ek_right (hf : s.IsTest f) (hD : HD s f) (u : B.U) (g y : G) : Ek s f (g * u) y = (B.ω u : ℂ) • Ek s f g y := by
  unfold Ek
  rw [smul_finsum' _ (Tk_fin hD g y)]
  refine finsum_congr fun x => ?_
  have := hf.left u⁻¹ (g⁻¹ * s.θ (B.ι x.out⁻¹ * y))
  simp only [map_inv B.ω, inv_inv, InvMemClass.coe_inv] at this
  simp only [Tk]
  rw [mul_inv_rev, mul_assoc, this, smul_smul]

theorem traceA [FiniteDimensional ℂ V] (hB : B.Fin) (hf : s.IsTest f) (hD : HD s f) : letI := act B
    LinearMap.trace ℂ B.Forms (s.R f) = ∑ᶠ o : orbitRel.Quotient Γ (G ⧸ B.U), ∑ᶠ x : Γ ⧸ B.Γ₀,
      (B.Γ₀.relIndex (stabilizer Γ o.out) : ℂ)⁻¹ * LinearMap.trace ℂ V (Tk s f o.out.out o.out.out x.out⁻¹) := by
  letI := act B
  haveI := normal0 B
  haveI := finQ B hB
  haveI := formsFin _ _ _ B hB
  letI := Fintype.ofFinite (orbitRel.Quotient Γ (G ⧸ B.U))
  let n : orbitRel.Quotient Γ (G ⧸ B.U) → ℂ := fun o => (B.Γ₀.relIndex (stabilizer Γ o.out) : ℂ)⁻¹
  let A : (orbitRel.Quotient Γ (G ⧸ B.U) → V) →ₗ[ℂ] B.Forms :=
    { toFun := fun w => ⟨fun g => ∑ o, n o • Ek s f g o.out.out (w o), fun γ g => by simp [Ek_left hf hD], fun g u => by
        simp only [Ek_right hf hD, Finset.smul_sum, LinearMap.smul_apply]; exact Finset.sum_congr rfl fun _ _ => smul_comm _ _ _⟩
      map_add' := fun a b => Subtype.ext (funext fun g => by simp [Finset.sum_add_distrib])
      map_smul' := fun c a => Subtype.ext (funext fun g => by
        simp only [Pi.smul_apply, map_smul, RingHom.id_apply, Submodule.coe_smul, Finset.smul_sum]
        exact Finset.sum_congr rfl fun _ _ => smul_comm _ _ _) }
  let ev : B.Forms →ₗ[ℂ] (orbitRel.Quotient Γ (G ⧸ B.U) → V) := (LinearMap.funLeft ℂ V fun o => o.out.out).comp B.Forms.subtype
  have hR : s.R f = A ∘ₗ ev := by
    ext φ g
    rw [rSpec _ _ _ B s f hf]
    let k : G ⧸ B.U → V := fun y => f (g⁻¹ * s.θ y.out) • s.Θ (φ.1 y.out)
    have wd : ∀ y : G, k y = f (g⁻¹ * s.θ y) • s.Θ (φ.1 y) := fun y => by
      obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul B.U y
      simp only [k]
      rw [hu, map_mul, ← mul_assoc, hf.right, φ.2.2, map_smul, smul_smul, mul_right_comm, ← Units.val_mul]; simp
    have e : ∀ x : G ⧸ B.U, k (MulAction.toPerm (s.θ.symm g) x) = f (s.θ x.out) • s.Θ (φ.1 (s.θ.symm g * x.out)) := fun x => by
      have : (MulAction.toPerm (s.θ.symm g) x : G ⧸ B.U) = ((s.θ.symm g * x.out : G) : G ⧸ B.U) := by
        conv_lhs => rw [← x.out_eq]
        rfl
      rw [this, wd]; simp
    have kf : (Function.support k).Finite := by
      refine Set.Finite.of_preimage (f := MulAction.toPerm (s.θ.symm g)) (hf.fin.subset fun x hx h => hx ?_) (Equiv.surjective _)
      rw [e, h, zero_smul]
    obtain ⟨t1, t2⟩ := finsum_triv B.Γ₀ (triv0 B) k kf
    obtain ⟨c1, c2⟩ := countC B.Γ₀ B.Γ₀ (triv0 B) le_rfl (stab0 B hB) k (fun z hz y => by rw [triv0 B z hz]) t1
    rw [t2, finsum_curry _ c1, finsum_eq_sum_of_fintype, ← finsum_comp_equiv (MulAction.toPerm (s.θ.symm g))] at c2
    simp only [e] at c2
    refine c2.symm.trans (Finset.sum_congr rfl fun o _ => ?_)
    show _ = n o • Ek s f g o.out.out (φ.1 o.out.out)
    have := map_finsum (n o • LinearMap.applyₗ (R := ℂ) (M₂ := V) (φ.1 o.out.out)) (Tk_fin hD g o.out.out)
    refine Eq.trans (finsum_congr fun x => ?_) this.symm
    have e2 : x.out⁻¹ • o.out = ((B.ι x.out⁻¹ * o.out.out : G) : G ⧸ B.U) := by
      conv_lhs => rw [← o.out.out_eq]
      rfl
    rw [e2, wd, φ.2.1]
    rfl
  rw [hR, LinearMap.trace_comp_comm', trace_blocks (fun o' o => n o • Ek s f o'.out.out o.out.out) _ fun w o' => rfl, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun o _ => ?_
  exact map_finsum (LinearMap.trace ℂ V ∘ₗ LinearMap.lsmul ℂ _ (n o)) (Tk_fin hD _ _) |>.trans (finsum_congr fun x => by simp [n])

end UpperTheory.V.Z.Sym.Tf
end
