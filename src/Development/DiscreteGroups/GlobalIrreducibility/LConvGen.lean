import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WhittakerFunctionalTorusValuationBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LongElementConjUnipotentRadical
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipRadStdBlocksTwoNeBot

section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.SplitWeil ValuativeRel

namespace DiscreteGroups.sglob.LConvGenF

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ball (s : kˣ) : AddSubgroup k where
  carrier := cball s
  zero_mem' := by simp [cball]
  add_mem' := by
    intro a b ha hb
    simp only [cball, Set.mem_setOf_eq] at ha hb ⊢
    exact Valuation.map_add_le _ ha hb
  neg_mem' := by
    intro a ha
    simp only [cball, Set.mem_setOf_eq] at ha ⊢
    rwa [Valuation.map_neg]

theorem mem_ball {s : kˣ} {a : k} : a ∈ ball s ↔ valuation k a ≤ valuation k (s : k) := Iff.rfl

theorem ball_mono {s t : kˣ} (h : valuation k (s : k) ≤ valuation k (t : k)) {a : k} (ha : a ∈ ball s) :
    a ∈ ball t := mem_ball.2 (le_trans (mem_ball.1 ha) h)

theorem mul_mem_ball {s t : kˣ} {a b : k} (ha : a ∈ ball s) (hb : b ∈ ball t) : a * b ∈ ball (s * t) := by
  rw [mem_ball, map_mul, Units.val_mul, map_mul]
  exact mul_le_mul' ha hb

theorem isOpen_ball (s : kˣ) : IsOpen ((ball s : AddSubgroup k) : Set k) := isOpen_cball s

abbrev Q (s t : kˣ) : Type := ↥(ball t) ⧸ (ball s).addSubgroupOf (ball t)

instance finite_Q (s t : kˣ) : Finite (Q (k := k) s t) := by
  haveI : CompactSpace ↥(ball t) := isCompact_iff_compactSpace.mp (isCompact_cball t)
  refine AddSubgroup.quotient_finite_of_isOpen _ ?_
  rw [AddSubgroup.coe_addSubgroupOf]
  exact (isOpen_ball s).preimage continuous_subtype_val

noncomputable instance (s t : kˣ) : Fintype (Q (k := k) s t) := Fintype.ofFinite _

theorem out_eq_add {s t : kˣ} (x : ↥(ball t)) (q : Q s t) (hq : q = QuotientAddGroup.mk x) :
    ∃ h ∈ ball s, ((Quotient.out q : ↥(ball t)) : k) = (x : k) + h := by
  have h1 : (QuotientAddGroup.mk (Quotient.out q) : Q s t) = QuotientAddGroup.mk x := by
    rw [← hq]; exact QuotientAddGroup.out_eq' q
  rw [QuotientAddGroup.eq] at h1
  refine ⟨((Quotient.out q : ↥(ball t)) : k) - x, ?_, by ring⟩
  have h2 := AddSubgroup.mem_addSubgroupOf.1 (neg_mem h1)
  convert h2 using 1
  push_cast
  ring

theorem apply_out {M : Type} {s t : kˣ} (g : k → M) (hg : ∀ b, ∀ h ∈ ball s, g (b + h) = g b)
    (x : ↥(ball t)) (q : Q s t) (hq : q = QuotientAddGroup.mk x) :
    g ((Quotient.out q : ↥(ball t)) : k) = g x := by
  obtain ⟨h, hh, he⟩ := out_eq_add x q hq
  rw [he, hg _ _ hh]

theorem out_mem {s t : kˣ} (q : Q s t) : ((Quotient.out q : ↥(ball t)) : k) ∈ ball t := (Quotient.out q).2

theorem out_zero_mem {s t : kˣ} : ((Quotient.out (0 : Q s t) : ↥(ball t)) : k) ∈ ball s := by
  obtain ⟨h, hh, he⟩ := out_eq_add (s := s) (0 : ↥(ball t)) 0 rfl
  rw [he]; simpa using hh

theorem out_mem_iff {s t : kˣ} (q : Q s t) : ((Quotient.out q : ↥(ball t)) : k) ∈ ball s ↔ q = 0 := by
  constructor
  · intro h
    rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_zero_iff]
    exact AddSubgroup.mem_addSubgroupOf.2 h
  · rintro rfl; exact out_zero_mem

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def avg (ψ : AddChar k Circle) (σ : k → V →ₗ[ℂ] V) (s t : kˣ) (ξ : k) : V →ₗ[ℂ] V :=
  ∑ q : Q s t, ((ψ (-(ξ * ((Quotient.out q : ↥(ball t)) : k))) : Circle) : ℂ) • σ ((Quotient.out q : ↥(ball t)) : k)

theorem ch_add (ψ : AddChar k Circle) (a b : k) : ((ψ (a + b) : Circle) : ℂ) = (ψ a : ℂ) * (ψ b : ℂ) := by
  rw [AddChar.map_add_eq_mul, Circle.coe_mul]

theorem ch_neg_mul (ψ : AddChar k Circle) (a : k) : ((ψ (-a) : Circle) : ℂ) * (ψ a : ℂ) = 1 := by
  rw [← ch_add ψ, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]

section Avg

variable (ψ : AddChar k Circle) (σ : k → V →ₗ[ℂ] V) (hadd : ∀ a b, σ (a + b) = σ a * σ b)
include hadd

theorem comm (a b : k) : σ a * σ b = σ b * σ a := by rw [← hadd, ← hadd, add_comm]

theorem avg_comm (s t : kˣ) (ξ : k) (b : k) : avg ψ σ s t ξ * σ b = σ b * avg ψ σ s t ξ := by
  simp only [avg, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, comm σ hadd]

theorem avg_comm_avg (s t s' t' : kˣ) (ξ ξ' : k) :
    avg ψ σ s t ξ * avg ψ σ s' t' ξ' = avg ψ σ s' t' ξ' * avg ψ σ s t ξ := by
  rw [avg, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, avg_comm ψ σ hadd]

omit hadd in
theorem avg_mem (W : Submodule ℂ V) (hW : ∀ a, ∀ w ∈ W, σ a w ∈ W) (s t : kˣ) (ξ : k) {w : V} (hw : w ∈ W) :
    avg ψ σ s t ξ w ∈ W := by
  simp only [avg, LinearMap.sum_apply, LinearMap.smul_apply]
  exact W.sum_mem fun q _ => W.smul_mem _ (hW _ _ hw)

theorem avg_eigen {s t : kˣ} {ξ : k} (hξ : ∀ h ∈ ball s, ψ (ξ * h) = 1) {y : V} (hy : ∀ h ∈ ball s, σ h y = y)
    {a : k} (ha : a ∈ ball t) : σ a (avg ψ σ s t ξ y) = ((ψ (ξ * a) : Circle) : ℂ) • avg ψ σ s t ξ y := by
  rw [← Module.End.mul_apply, ← avg_comm ψ σ hadd, Module.End.mul_apply]
  let g : k → V := fun b => ((ψ (-(ξ * b)) : Circle) : ℂ) • σ b y
  have hg : ∀ b, ∀ h ∈ ball s, g (b + h) = g b := by
    intro b h hh
    simp only [g, hadd, Module.End.mul_apply, hy h hh, mul_add, neg_add, ch_add ψ, hξ h hh]
    have : ((ψ (-(ξ * h)) : Circle) : ℂ) = 1 := by
      have := ch_neg_mul ψ (ξ * h); rwa [hξ h hh, Circle.coe_one, mul_one] at this
    rw [this, mul_one]
  let a' : ↥(ball t) := ⟨a, ha⟩
  have key : ∀ q : Q s t, ((ψ (-(ξ * ((Quotient.out q : ↥(ball t)) : k))) : Circle) : ℂ) •
      σ ((Quotient.out q : ↥(ball t)) : k) (σ a y) =
      ((ψ (ξ * a) : Circle) : ℂ) • g ((Quotient.out (q + QuotientAddGroup.mk a') : ↥(ball t)) : k) := by
    intro q
    rw [apply_out g hg (Quotient.out q + a') _ (by rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq'])]
    simp only [g, AddSubgroup.coe_add, a', ← Module.End.mul_apply, ← hadd, smul_smul]
    congr 1
    rw [mul_add, neg_add, ch_add ψ, ← mul_assoc, mul_comm ((ψ (ξ * a) : Circle) : ℂ), mul_assoc]
    rw [mul_comm ((ψ (ξ * a) : Circle) : ℂ), ch_neg_mul, mul_one]
  simp only [avg, LinearMap.sum_apply, LinearMap.smul_apply, key, ← Finset.smul_sum]
  congr 1
  exact (Equiv.sum_comp (Equiv.addRight (QuotientAddGroup.mk a' : Q s t)) (fun q => g ((Quotient.out q : ↥(ball t)) : k)))

end Avg

end DiscreteGroups.sglob.LConvGenF
end
end

section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.SplitWeil ValuativeRel

namespace DiscreteGroups.sglob.LConvGenF

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem psi_triv {ψ : AddChar k Circle} {c : kˣ} (hc : HasConductor ψ c) {s : kˣ} {ξ : k}
    (hξ : ξ ∈ ball (c * s⁻¹)) : ∀ h ∈ ball s, ψ (ξ * h) = 1 := by
  intro h hh
  have := mul_mem_ball hξ hh
  rw [inv_mul_cancel_right] at this
  exact hc.eq_one this

theorem psi_neg_triv {ψ : AddChar k Circle} {c : kˣ} (hc : HasConductor ψ c) {s : kˣ} {ξ : k}
    (hξ : ξ ∈ ball (c * s⁻¹)) {h : k} (hh : h ∈ ball s) : ψ (-(ξ * h)) = 1 := by
  have := mul_mem_ball hξ hh
  rw [inv_mul_cancel_right] at this
  exact hc.eq_one (neg_mem this)

theorem card_ne_zero (s t : kˣ) : ((Fintype.card (Q (k := k) s t) : ℕ) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.2 Fintype.card_ne_zero

theorem exists_ball_mem (a : k) : ∃ t : kˣ, a ∈ ball t := by
  by_cases h : a = 0
  · exact ⟨1, by rw [h]; exact (ball 1).zero_mem⟩
  · exact ⟨Units.mk0 a h, mem_ball.2 le_rfl⟩

theorem exists_min (s1 s2 : kˣ) : ∃ s : kˣ, valuation k (s : k) ≤ valuation k (s1 : k) ∧
    valuation k (s : k) ≤ valuation k (s2 : k) := by
  rcases le_total (valuation k (s1 : k)) (valuation k (s2 : k)) with h | h
  · exact ⟨s1, le_rfl, h⟩
  · exact ⟨s2, h, le_rfl⟩

theorem exists_max (s1 s2 : kˣ) : ∃ s : kˣ, valuation k (s1 : k) ≤ valuation k (s : k) ∧
    valuation k (s2 : k) ≤ valuation k (s : k) := by
  rcases le_total (valuation k (s1 : k)) (valuation k (s2 : k)) with h | h
  · exact ⟨s2, h, le_rfl⟩
  · exact ⟨s1, le_rfl, h⟩

section Fourier

variable (ψ : AddChar k Circle) (σ : k → V →ₗ[ℂ] V) (hadd : ∀ a b, σ (a + b) = σ a * σ b)

theorem avg_of_eigen {s t : kˣ} {ξ : k} {z : V}
    (hz : ∀ b ∈ ball t, σ b z = ((ψ (ξ * b) : Circle) : ℂ) • z) :
    avg ψ σ s t ξ z = ((Fintype.card (Q s t) : ℕ) : ℂ) • z := by
  have h1 : ∀ q : Q s t, ((ψ (-(ξ * ((Quotient.out q : ↥(ball t)) : k))) : Circle) : ℂ) •
      σ ((Quotient.out q : ↥(ball t)) : k) z = z := fun q => by
    rw [hz _ (out_mem q), smul_smul, ch_neg_mul, one_smul]
  simp only [avg, LinearMap.sum_apply, LinearMap.smul_apply, h1, Finset.sum_const, Finset.card_univ]
  exact (Nat.cast_smul_eq_nsmul ℂ _ _).symm

include hadd

theorem avg_level {s s0 t : kˣ} {ξ : k} (hss0 : valuation k (s : k) ≤ valuation k (s0 : k))
    (hξ : ∀ h ∈ ball s0, ψ (ξ * h) = 1) {x : V} (hx : ∀ h ∈ ball s0, σ h x = x) :
    ((Fintype.card (Q s0 t) : ℕ) : ℂ) • avg ψ σ s t ξ x = ((Fintype.card (Q s t) : ℕ) : ℂ) • avg ψ σ s0 t ξ x := by
  have hξs : ∀ h ∈ ball s, ψ (ξ * h) = 1 := fun h hh => hξ h (ball_mono hss0 hh)
  have hxs : ∀ h ∈ ball s, σ h x = x := fun h hh => hx h (ball_mono hss0 hh)
  have e1 : avg ψ σ s0 t ξ (avg ψ σ s t ξ x) = ((Fintype.card (Q s0 t) : ℕ) : ℂ) • avg ψ σ s t ξ x :=
    avg_of_eigen ψ σ (fun b hb => avg_eigen ψ σ hadd hξs hxs hb)
  have e2 : avg ψ σ s t ξ (avg ψ σ s0 t ξ x) = ((Fintype.card (Q s t) : ℕ) : ℂ) • avg ψ σ s0 t ξ x :=
    avg_of_eigen ψ σ (fun b hb => avg_eigen ψ σ hadd hξ hx hb)
  rw [← e1, ← e2, ← Module.End.mul_apply, avg_comm_avg ψ σ hadd, Module.End.mul_apply]

theorem avg_mono_mem (W : Submodule ℂ V) (hW : ∀ a, ∀ w ∈ W, σ a w ∈ W) {s t t' : kˣ}
    (htt' : valuation k (t : k) ≤ valuation k (t' : k)) {ξ : k} (hξ : ∀ h ∈ ball s, ψ (ξ * h) = 1)
    {x : V} (hx : ∀ h ∈ ball s, σ h x = x) (h : avg ψ σ s t ξ x ∈ W) : avg ψ σ s t' ξ x ∈ W := by
  have e : avg ψ σ s t ξ (avg ψ σ s t' ξ x) = ((Fintype.card (Q s t) : ℕ) : ℂ) • avg ψ σ s t' ξ x :=
    avg_of_eigen ψ σ (fun b hb => avg_eigen ψ σ hadd hξ hx (ball_mono htt' hb))
  have hm : avg ψ σ s t ξ (avg ψ σ s t' ξ x) ∈ W := by
    rw [← Module.End.mul_apply, avg_comm_avg ψ σ hadd, Module.End.mul_apply]
    exact avg_mem ψ σ W hW _ _ _ h
  rw [e] at hm
  exact (W.smul_mem_iff (card_ne_zero s t)).1 hm

end Fourier

end DiscreteGroups.sglob.LConvGenF
end
end

section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.SplitWeil ValuativeRel

namespace DiscreteGroups.sglob.LConvGenF

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ψ : AddChar k Circle) (σ : k → V →ₗ[ℂ] V) {c : kˣ} (hc : HasConductor ψ c)

include hc in

theorem dual_sum_eq_zero {s t : kˣ} {b : k} (hbt : b ∈ ball t) (hbs : b ∉ ball s) :
    ∑ f : Q (c * t⁻¹) (c * s⁻¹), ((ψ (-(((Quotient.out f : ↥(ball (c * s⁻¹))) : k) * b)) : Circle) : ℂ) = 0 := by
  obtain ⟨ξ0, hξ0, hne⟩ := hc.exists_ne_one (c * s⁻¹) (x := b)
    (by rw [show c * (c * s⁻¹)⁻¹ = s by rw [mul_inv_rev, inv_inv, mul_comm s, mul_inv_cancel_left]]; exact hbs)
  let φ : k → ℂ := fun ξ => ((ψ (-(ξ * b)) : Circle) : ℂ)
  have hφ : ∀ ξ, ∀ h ∈ ball (c * t⁻¹), φ (ξ + h) = φ ξ := by
    intro ξ h hh
    show ((ψ (-((ξ + h) * b)) : Circle) : ℂ) = ψ (-(ξ * b))
    rw [add_mul, neg_add, ch_add ψ, psi_neg_triv hc hh hbt, Circle.coe_one, mul_one]
  let ξ0' : ↥(ball (c * s⁻¹)) := ⟨ξ0, hξ0⟩
  have shift : ∑ f : Q (c * t⁻¹) (c * s⁻¹), φ ((Quotient.out f : ↥(ball (c * s⁻¹))) : k) =
      φ ξ0 * ∑ f : Q (c * t⁻¹) (c * s⁻¹), φ ((Quotient.out f : ↥(ball (c * s⁻¹))) : k) := by
    rw [Finset.mul_sum]
    rw [← Equiv.sum_comp (Equiv.addRight (QuotientAddGroup.mk ξ0' : Q (c * t⁻¹) (c * s⁻¹)))]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Equiv.coe_addRight, apply_out φ hφ (Quotient.out f + ξ0') _
      (by rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq'])]
    simp only [φ, AddSubgroup.coe_add, ξ0']
    rw [add_mul, neg_add, ch_add ψ, mul_comm]
  have hne' : φ ξ0 ≠ 1 := by
    intro h1
    apply hne
    have := ch_neg_mul ψ (ξ0 * b)
    simp only [φ] at h1
    rw [h1, one_mul] at this
    exact Circle.coe_eq_one.1 this
  have h2 : (1 - φ ξ0) * ∑ f : Q (c * t⁻¹) (c * s⁻¹), φ ((Quotient.out f : ↥(ball (c * s⁻¹))) : k) = 0 := by
    rw [sub_mul, one_mul, ← shift, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne'.symm)

include hc in

theorem sum_avg {s t : kˣ} {x : V} (hx : ∀ h ∈ ball s, σ h x = x) :
    ∑ f : Q (c * t⁻¹) (c * s⁻¹), avg ψ σ s t ((Quotient.out f : ↥(ball (c * s⁻¹))) : k) x =
      ((Fintype.card (Q (c * t⁻¹) (c * s⁻¹)) : ℕ) : ℂ) • x := by
  simp only [avg, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  rw [Finset.sum_eq_single (0 : Q s t)]
  · rw [hx _ out_zero_mem]
    congr 1
    have h1 : ∀ f : Q (c * t⁻¹) (c * s⁻¹), ((ψ (-(((Quotient.out f : ↥(ball (c * s⁻¹))) : k) *
        ((Quotient.out (0 : Q s t) : ↥(ball t)) : k))) : Circle) : ℂ) = 1 := fun f => by
      rw [psi_neg_triv hc (out_mem f) out_zero_mem, Circle.coe_one]
    simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  · intro q _ hq
    rw [dual_sum_eq_zero ψ hc (out_mem q) (fun h => hq ((out_mem_iff q).1 h)), zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

end DiscreteGroups.sglob.LConvGenF
end
end

section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.SplitWeil ValuativeRel

namespace DiscreteGroups.sglob.LConvGenF

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ψ : AddChar k Circle) (σ : k → V →ₗ[ℂ] V) {c : kˣ} (hc : HasConductor ψ c)

include hc in
theorem exists_avg_notMem (W : Submodule ℂ V) {s t : kˣ} {x : V} (hx : ∀ h ∈ ball s, σ h x = x)
    (hxW : x ∉ W) : ∃ ξ ∈ ball (c * s⁻¹), avg ψ σ s t ξ x ∉ W := by
  by_contra hall
  push Not at hall
  apply hxW
  have hsum := sum_avg ψ σ hc (t := t) hx
  have hm : ((Fintype.card (Q (c * t⁻¹) (c * s⁻¹)) : ℕ) : ℂ) • x ∈ W := by
    rw [← hsum]
    exact W.sum_mem fun f _ => hall _ (out_mem f)
  exact (W.smul_mem_iff (card_ne_zero _ _)).1 hm

include hc in
theorem avg_shift {s t : kˣ} {ξ h : k} (hh : h ∈ ball (c * t⁻¹)) : avg ψ σ s t (ξ + h) = avg ψ σ s t ξ := by
  simp only [avg]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [add_mul, neg_add, ch_add ψ, psi_neg_triv hc hh (out_mem q), Circle.coe_one, mul_one]

include hc in
theorem isClosed_notMem (W : Submodule ℂ V) (s t : kˣ) (x : V) :
    IsClosed {ξ : k | avg ψ σ s t ξ x ∉ W} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro ξ hξ
  have hU : (fun η => η - ξ) ⁻¹' ((ball (c * t⁻¹) : AddSubgroup k) : Set k) ∈ nhds ξ :=
    ((isOpen_ball _).preimage (continuous_sub_right ξ)).mem_nhds (by simp [(ball _).zero_mem])
  refine Filter.mem_of_superset hU fun η hη => ?_
  have : η = ξ + (η - ξ) := by ring
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hξ ⊢
  rw [this, avg_shift ψ σ hc hη]
  exact hξ

variable (hadd : ∀ a b, σ (a + b) = σ a * σ b)

include hadd in
theorem key_step (W : Submodule ℂ V) (hW : ∀ a, ∀ w ∈ W, σ a w ∈ W)
    (hsm : ∀ v : V, ∃ s : kˣ, ∀ h ∈ ball s, σ h v = v) {s : kˣ} {x : V} (hs : ∀ h ∈ ball s, σ h x = x) {ξ : k}
    (hξs : ∀ h ∈ ball s, ψ (ξ * h) = 1)
    (hx : x ∈ W ⊔ Submodule.span ℂ {z | ∃ (a : k) (y : V), z = σ a y - ((ψ (ξ * a) : Circle) : ℂ) • y}) :
    ∃ t' : kˣ, valuation k (s : k) ≤ valuation k (t' : k) ∧ avg ψ σ s t' ξ x ∈ W := by
  let P : V → Prop := fun z => ∃ s' t' : kˣ, valuation k (s' : k) ≤ valuation k (s : k) ∧
    valuation k (s : k) ≤ valuation k (t' : k) ∧ ∀ s'' t'' : kˣ, valuation k (s'' : k) ≤ valuation k (s' : k) →
      valuation k (t' : k) ≤ valuation k (t'' : k) → avg ψ σ s'' t'' ξ z ∈ W
  have Padd : ∀ z1 z2, P z1 → P z2 → P (z1 + z2) := by
    rintro z1 z2 ⟨s1, t1, hs1, ht1, h1⟩ ⟨s2, t2, hs2, ht2, h2⟩
    obtain ⟨s', a1, a2⟩ := exists_min s1 s2
    obtain ⟨t', b1, b2⟩ := exists_max t1 t2
    refine ⟨s', t', a1.trans hs1, ht1.trans b1, fun s'' t'' h1' h2' => ?_⟩
    rw [map_add]
    exact W.add_mem (h1 _ _ (h1'.trans a1) (b1.trans h2')) (h2 _ _ (h1'.trans a2) (b2.trans h2'))
  have PW : ∀ w ∈ W, P w := fun w hw => ⟨s, s, le_rfl, le_rfl, fun _ _ _ _ => avg_mem ψ σ W hW _ _ _ hw⟩
  have Pspan : ∀ z ∈ Submodule.span ℂ {z | ∃ (a : k) (y : V), z = σ a y - ((ψ (ξ * a) : Circle) : ℂ) • y},
      P z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, y, rfl⟩ := hz
      obtain ⟨sy, hsy⟩ := hsm y
      obtain ⟨ta, hta⟩ := exists_ball_mem a
      obtain ⟨s', a1, a2⟩ := exists_min s sy
      obtain ⟨t', b1, b2⟩ := exists_max s ta
      refine ⟨s', t', a1, b1, fun s'' t'' h1 h2 => ?_⟩
      have hy'' : ∀ h ∈ ball s'', σ h y = y := fun h hh => hsy h (ball_mono (h1.trans a2) hh)
      have hξ'' : ∀ h ∈ ball s'', ψ (ξ * h) = 1 := fun h hh => hξs h (ball_mono (h1.trans a1) hh)
      have ha : a ∈ ball t'' := ball_mono (b2.trans h2) hta
      rw [map_sub, map_smul, ← Module.End.mul_apply, avg_comm ψ σ hadd, Module.End.mul_apply,
        avg_eigen ψ σ hadd hξ'' hy'' ha, sub_self]
      exact W.zero_mem
    | zero => exact PW 0 W.zero_mem
    | add z1 z2 _ _ h1 h2 => exact Padd z1 z2 h1 h2
    | smul r z _ h =>
      obtain ⟨s', t', a1, b1, hz⟩ := h
      exact ⟨s', t', a1, b1, fun s'' t'' h1 h2 => by rw [map_smul]; exact W.smul_mem r (hz _ _ h1 h2)⟩
  obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨s', t', hs', ht', h⟩ := Padd w y (PW w hw) (Pspan y hy)
  refine ⟨t', ht', ?_⟩
  have h1 := h s' t' le_rfl le_rfl
  have e := avg_level ψ σ hadd (t := t') hs' hξs hs
  have hm : ((Fintype.card (Q s' t') : ℕ) : ℂ) • avg ψ σ s t' ξ (w + y) ∈ W := by
    rw [← e]; exact W.smul_mem _ h1
  exact (W.smul_mem_iff (card_ne_zero _ _)).1 hm

include hc hadd in

theorem exists_character_sup_ne_top (W : Submodule ℂ V) (hW : ∀ a, ∀ w ∈ W, σ a w ∈ W)
    (hsm : ∀ v : V, ∃ s : kˣ, ∀ h ∈ ball s, σ h v = v) (hne : W ≠ ⊤) :
    ∃ ξ : k, W ⊔ Submodule.span ℂ {z | ∃ (a : k) (y : V), z = σ a y - ((ψ (ξ * a) : Circle) : ℂ) • y} ≠ ⊤ := by
  obtain ⟨x, hxW⟩ : ∃ x, x ∉ W := by
    by_contra h
    push Not at h
    exact hne (eq_top_iff.2 fun x _ => h x)
  obtain ⟨s, hs⟩ := hsm x
  let ι := {t : kˣ // valuation k (s : k) ≤ valuation k (t : k)}
  haveI : Nonempty ι := ⟨⟨s, le_rfl⟩⟩
  let C : ι → Set k := fun t => ((ball (c * s⁻¹) : AddSubgroup k) : Set k) ∩ {ξ | avg ψ σ s t.1 ξ x ∉ W}
  have hdir : Directed (· ⊇ ·) C := by
    intro t1 t2
    rcases le_total (valuation k (t1.1 : k)) (valuation k (t2.1 : k)) with h | h
    · exact ⟨t2, fun ξ hξ => ⟨hξ.1, fun hm => hξ.2 (avg_mono_mem ψ σ hadd W hW h (psi_triv hc hξ.1) hs hm)⟩,
        le_rfl⟩
    · exact ⟨t1, le_rfl, fun ξ hξ => ⟨hξ.1, fun hm => hξ.2 (avg_mono_mem ψ σ hadd W hW h (psi_triv hc hξ.1) hs hm)⟩⟩
  have hnon : ∀ t, (C t).Nonempty := fun t => by
    obtain ⟨ξ, h1, h2⟩ := exists_avg_notMem ψ σ hc W (t := t.1) hs hxW
    exact ⟨ξ, h1, h2⟩
  have hcl : ∀ t, IsClosed (C t) := fun t =>
    ((ball _).isClosed_of_isOpen (isOpen_ball _)).inter (isClosed_notMem ψ σ hc W s t.1 x)
  have hcpt : ∀ t, IsCompact (C t) := fun t => (isCompact_cball _).inter_right (isClosed_notMem ψ σ hc W s t.1 x)
  obtain ⟨ξ, hξ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hnon hcpt hcl
  rw [Set.mem_iInter] at hξ
  have hξs := psi_triv hc (hξ ⟨s, le_rfl⟩).1
  refine ⟨ξ, fun htop => ?_⟩
  obtain ⟨t', ht', hm⟩ := key_step ψ σ hadd W hW hsm hs hξs (x := x) (by rw [htop]; exact Submodule.mem_top)
  exact (hξ ⟨t', ht'⟩).2 hm

end DiscreteGroups.sglob.LConvGenF
end
end

section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix

namespace DiscreteGroups.sglob.LConvGenM

variable {k : Type} [Field k] {n : ℕ}

def colM (j : ℕ) (c : Fin n → k) : Matrix (Fin n) (Fin n) k :=
  Matrix.of fun i l => if i.val < j ∧ l.val = j then c i else 0

theorem colM_apply (j : ℕ) (c : Fin n → k) (i l : Fin n) :
    colM j c i l = if i.val < j ∧ l.val = j then c i else 0 := rfl

theorem colM_mul (j : ℕ) (c d : Fin n → k) : colM j c * colM j d = 0 := by
  ext i l
  simp only [mul_apply, colM_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases h1 : i.val < j ∧ a.val = j
  · by_cases h2 : a.val < j ∧ l.val = j
    · exact absurd h2.1 (by omega)
    · simp [h2]
  · simp [h1]

theorem colM_add (j : ℕ) (c d : Fin n → k) : colM j (c + d) = colM j c + colM j d := by
  ext i l
  simp only [colM_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

def colU (j : ℕ) (c : Fin n → k) : GL (Fin n) k :=
  ⟨1 + colM j c, 1 - colM j c, by rw [add_mul, one_mul, mul_sub, mul_one, colM_mul]; abel,
    by rw [sub_mul, one_mul, mul_add, mul_one, colM_mul]; abel⟩

theorem val_colU (j : ℕ) (c : Fin n → k) : (colU j c : Matrix (Fin n) (Fin n) k) = 1 + colM j c := rfl

theorem colU_add (j : ℕ) (c d : Fin n → k) : colU j (c + d) = colU j c * colU j d := by
  ext : 1
  rw [Units.val_mul, val_colU, val_colU, val_colU, colM_add, add_mul, one_mul, mul_add, mul_one, colM_mul]
  abel

theorem colU_zero (j : ℕ) : colU j (0 : Fin n → k) = 1 := by
  ext : 1
  rw [val_colU, Units.val_one]
  have : colM j (0 : Fin n → k) = 0 := by ext i l; simp [colM_apply]
  rw [this, add_zero]

theorem colU_inv (j : ℕ) (c : Fin n → k) : (colU j c)⁻¹ = colU j (-c) := by
  refine (inv_eq_of_mul_eq_one_right ?_)
  rw [← colU_add, add_neg_cancel, colU_zero]

theorem colU_mul_apply (j : ℕ) (hj : j < n) (c : Fin n → k) (M : Matrix (Fin n) (Fin n) k) (i l : Fin n) :
    ((colU j c : Matrix (Fin n) (Fin n) k) * M) i l = M i l + (if i.val < j then c i * M ⟨j, hj⟩ l else 0) := by
  rw [val_colU, add_mul, one_mul, Matrix.add_apply, mul_apply]
  congr 1
  rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin n)]
  · simp only [colM_apply, and_true]
    split_ifs <;> simp
  · intro a _ ha
    have : ¬ (a.val = j) := fun h => ha (Fin.ext h)
    simp [colM_apply, this]
  · simp

theorem colU_single_of_lt (j : ℕ) (hj : j < n) {r : Fin n} (hr : r.val < j) (a : k) :
    colU j (Pi.single r a) = GlobalTheory.RootUp.elem (i := r) (j := ⟨j, hj⟩) (fun h => by
      have := congrArg Fin.val h; simp at this; omega) a := by
  ext i l
  rw [val_colU, GlobalTheory.RootUp.val_elem, Matrix.add_apply, Matrix.add_apply]
  congr 1
  rw [colM_apply, Matrix.single_apply]
  by_cases hi : i = r
  · subst hi
    by_cases hl : l.val = j
    · have : (⟨j, hj⟩ : Fin n) = l := Fin.ext hl.symm
      simp [hr, hl, this]
    · have : (⟨j, hj⟩ : Fin n) ≠ l := fun h => hl (by rw [← h])
      simp [hl, this]
  · have : r ≠ i := Ne.symm hi
    simp [Pi.single_apply, hi, this]

theorem colU_single_of_ge (j : ℕ) {r : Fin n} (hr : j ≤ r.val) (a : k) : colU j (Pi.single r a) = 1 := by
  ext i l
  rw [val_colU, Units.val_one, Matrix.add_apply, colM_apply]
  by_cases hi : i = r
  · subst hi; simp [show ¬ i.val < j by omega]
  · simp [Pi.single_apply, hi]

end DiscreteGroups.sglob.LConvGenM
end
end

section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix

namespace DiscreteGroups.sglob.LConvGenM

variable {k : Type} [Field k] {n : ℕ}

def Nset (m : ℕ) : Set (GL (Fin n) k) :=
  {g | ∀ i l : Fin n, (l ≤ i ∨ l.val < m) → (g : Matrix (Fin n) (Fin n) k) i l = (1 : Matrix (Fin n) (Fin n) k) i l}

def sdS (m : ℕ) (M : Matrix (Fin n) (Fin n) k) : k :=
  ∑ i : Fin n, ∑ l : Fin n, if l.val = i.val + 1 ∧ m ≤ l.val then M i l else 0

def Good (j : ℕ) (x : Matrix (Fin n) (Fin n) k) : Prop :=
  ∀ i l : Fin n, (j ≤ i.val ∨ j + 1 ≤ l.val) → x i l = (1 : Matrix (Fin n) (Fin n) k) i l

theorem mul_col_of_good {j : ℕ} {Y : Matrix (Fin n) (Fin n) k} (hY : Good j Y) (M : Matrix (Fin n) (Fin n) k)
    {i l : Fin n} (hl : j + 1 ≤ l.val) : (M * Y) i l = M i l := by
  rw [mul_apply, Finset.sum_eq_single l]
  · rw [hY l l (Or.inr hl), one_apply_eq, mul_one]
  · intro b _ hb; rw [hY b l (Or.inr hl), one_apply_ne hb, mul_zero]
  · simp

theorem mul_row_of_good {j : ℕ} {X : Matrix (Fin n) (Fin n) k} (hX : Good j X) (M : Matrix (Fin n) (Fin n) k)
    {i l : Fin n} (hi : j ≤ i.val) : (X * M) i l = M i l := by
  rw [mul_apply, Finset.sum_eq_single i]
  · rw [hX i i (Or.inl hi), one_apply_eq, one_mul]
  · intro b _ hb; rw [hX i b (Or.inl hi), one_apply_ne (Ne.symm hb), zero_mul]
  · simp

theorem good_conj {j : ℕ} (x : GL (Fin n) k) (hx : Good j (x : Matrix (Fin n) (Fin n) k))
    (hy : Good j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) {g : GL (Fin n) k} (hg : g ∈ Nset (j + 1)) :
    x * g * x⁻¹ ∈ Nset (j + 1) ∧ sdS (j + 1) ((x * g * x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      sdS (j + 1) (g : Matrix (Fin n) (Fin n) k) := by
  set X := (x : Matrix (Fin n) (Fin n) k)
  set Y := ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
  set G := (g : Matrix (Fin n) (Fin n) k)
  have hXY : X * Y = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hval : ((x * g * x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = X * G * Y := by
    simp only [Units.val_mul, X, Y, G]

  have hA : ∀ i l : Fin n, l.val < j + 1 → (X * G * Y) i l = (1 : Matrix (Fin n) (Fin n) k) i l := by
    intro i l hl
    have hGY : ∀ a, (G * Y) a l = Y a l := by
      intro a
      rw [mul_apply, ← one_mul Y, mul_apply, one_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hb : b.val < j + 1
      · exact congrArg (· * Y b l) (hg a b (Or.inr hb))
      · have h1 : Y b l = 0 := by
          rw [hy b l (Or.inl (by omega)), one_apply_ne]; intro h; rw [h] at hb; omega
        rw [h1, mul_zero, mul_zero]
    rw [Matrix.mul_assoc, mul_apply, ← hXY, mul_apply]
    exact Finset.sum_congr rfl fun a _ => by rw [hGY]

  have hB : ∀ i l : Fin n, j ≤ i.val → j + 1 ≤ l.val → (X * G * Y) i l = G i l := by
    intro i l hi hl
    rw [mul_col_of_good hy _ hl, mul_row_of_good hx _ hi]
  refine ⟨fun i l hil => ?_, ?_⟩
  · rw [hval]
    by_cases hl : l.val < j + 1
    · exact hA i l hl
    · have hli : l ≤ i := hil.resolve_right hl
      rw [hB i l (by rw [Fin.le_iff_val_le_val] at hli; omega) (by omega)]
      exact hg i l (Or.inl hli)
  · rw [hval, sdS, sdS]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    split_ifs with h
    · exact hB i l (by omega) h.2
    · rfl

end DiscreteGroups.sglob.LConvGenM
end
end

section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix

namespace DiscreteGroups.sglob.LConvGenM

variable {k : Type} [Field k] {n : ℕ}

theorem good_colU (j : ℕ) (c : Fin n → k) : Good j ((colU j c : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  intro i l h
  rw [val_colU, Matrix.add_apply, colM_apply, if_neg (by omega), add_zero]

theorem good_colU_inv (j : ℕ) (c : Fin n → k) :
    Good j (((colU j c)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  rw [colU_inv]; exact good_colU j _

theorem peel_apply (j : ℕ) (hj : j < n) (g : GL (Fin n) k) (i l : Fin n) :
    ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i l =
      (g : Matrix (Fin n) (Fin n) k) i l + (if i.val < j then
        -(g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩ * (g : Matrix (Fin n) (Fin n) k) ⟨j, hj⟩ l else 0) := by
  rw [Units.val_mul, colU_mul_apply j hj]
  rfl

theorem peel_N (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) {g : GL (Fin n) k} (hg : g ∈ Nset j) :
    colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g ∈ Nset (j + 1) ∧
    sdS j (g : Matrix (Fin n) (Fin n) k) =
      sdS (j + 1) ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) :
        Matrix (Fin n) (Fin n) k) + (g : Matrix (Fin n) (Fin n) k) ⟨j - 1, by omega⟩ ⟨j, hj⟩ := by
  have hg' : ∀ i l : Fin n, (l ≤ i ∨ l.val < j) → (g : Matrix (Fin n) (Fin n) k) i l = (1 : Matrix (Fin n) (Fin n) k) i l := hg
  have hjj : (g : Matrix (Fin n) (Fin n) k) ⟨j, hj⟩ ⟨j, hj⟩ = 1 := by rw [hg' _ _ (Or.inl le_rfl), one_apply_eq]
  have hrow : ∀ l : Fin n, l.val < j → (g : Matrix (Fin n) (Fin n) k) ⟨j, hj⟩ l = 0 := fun l hl => by
    rw [hg' _ _ (Or.inr hl), one_apply_ne]; intro h; rw [← h] at hl; simp at hl
  have hhi : ∀ i l : Fin n, j ≤ i.val → ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) :
      Matrix (Fin n) (Fin n) k) i l = (g : Matrix (Fin n) (Fin n) k) i l := fun i l hi => by
    rw [peel_apply, if_neg (by omega), add_zero]
  refine ⟨fun i l hil => ?_, ?_⟩
  · rw [peel_apply]
    by_cases hl : l.val < j
    · rw [hg' i l (Or.inr hl), hrow l hl]; simp
    · by_cases hlj : l.val = j
      · have hl' : l = ⟨j, hj⟩ := Fin.ext hlj
        subst hl'
        by_cases hi : i.val < j
        · rw [if_pos hi, hjj, mul_one, add_neg_cancel, one_apply_ne]
          intro h; rw [h] at hi; simp at hi
        · rw [if_neg hi, add_zero]
          exact hg' i _ (Or.inl (by rw [Fin.le_iff_val_le_val]; simp; omega))
      · have hli : l ≤ i := hil.resolve_right (by omega)
        rw [if_neg (by rw [Fin.le_iff_val_le_val] at hli; omega), add_zero]
        exact hg' i l (Or.inl hli)
  · have key : ∀ i l : Fin n, (if l.val = i.val + 1 ∧ j ≤ l.val then (g : Matrix (Fin n) (Fin n) k) i l else 0) =
        (if l.val = i.val + 1 ∧ j + 1 ≤ l.val then ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) :
          Matrix (Fin n) (Fin n) k) i l else 0) +
        (if i = (⟨j - 1, by omega⟩ : Fin n) then (if l = (⟨j, hj⟩ : Fin n) then (g : Matrix (Fin n) (Fin n) k) i l else 0) else 0) := by
      intro i l
      by_cases h2 : l.val = i.val + 1 ∧ j + 1 ≤ l.val
      · rw [if_pos ⟨h2.1, by omega⟩, if_pos h2, hhi i l (by omega),
          if_neg (fun h => by rw [Fin.ext_iff] at h; simp at h; omega), add_zero]
      · rw [if_neg h2, zero_add]
        by_cases h1 : l.val = i.val + 1 ∧ j ≤ l.val
        · have e1 : i = ⟨j - 1, by omega⟩ := Fin.ext (by simp; omega)
          have e2 : l = ⟨j, hj⟩ := Fin.ext (by simp; omega)
          rw [if_pos h1, if_pos e1, if_pos e2]
        · rw [if_neg h1]
          by_cases e1 : i = ⟨j - 1, by omega⟩
          · by_cases e2 : l = ⟨j, hj⟩
            · exfalso; apply h1; rw [e1, e2]; simp; omega
            · rw [if_pos e1, if_neg e2]
          · rw [if_neg e1]
    rw [sdS, sdS]
    simp only [key, Finset.sum_add_distrib]
    congr 1
    simp

end DiscreteGroups.sglob.LConvGenM
end
end

section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix

namespace DiscreteGroups.sglob.LConvGenM

variable {k : Type} [Field k] {n : ℕ}

theorem entries_of_mem_unipRad (j : ℕ) (h : ∑ i, ![j, n - j] i = n) {g : GL (Fin n) k}
    (hg : g ∈ unipRad k (stdBlocks ![j, n - j] h)) (i l : Fin n) (hil : ¬ (i.val < j ∧ j ≤ l.val)) :
    (g : Matrix (Fin n) (Fin n) k) i l = (1 : Matrix (Fin n) (Fin n) k) i l := by
  refine GlobalTheory.ThetaRad.mem_unipRad_iff_entries.1 hg i l ?_
  rw [GlobalTheory.ThetaRad.blk_stdBlocks_two, GlobalTheory.ThetaRad.blk_stdBlocks_two]
  by_cases hi : i.val < j
  · have hl : l.val < j := by omega
    simp [hi, hl]
  · simp only [hi, if_false]
    split_ifs <;> decide

theorem peel_rad (j : ℕ) (hj : j < n) (h : ∑ i, ![j, n - j] i = n) {g : GL (Fin n) k}
    (hg : g ∈ unipRad k (stdBlocks ![j, n - j] h)) :
    colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g ∈ Nset (j + 1) ∧
    sdS (j + 1) ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) :
        Matrix (Fin n) (Fin n) k) = 0 := by
  have hent := entries_of_mem_unipRad j h hg
  have key : ∀ i l : Fin n, ¬ (i.val < j ∧ j + 1 ≤ l.val) →
      ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) :
        Matrix (Fin n) (Fin n) k) i l = (1 : Matrix (Fin n) (Fin n) k) i l := by
    intro i l hil
    rw [peel_apply]
    by_cases hi : i.val < j
    · rw [if_pos hi, hent ⟨j, hj⟩ l (by simp)]
      by_cases hlj : l.val = j
      · have hl' : l = ⟨j, hj⟩ := Fin.ext hlj
        subst hl'
        rw [one_apply_eq, mul_one, add_neg_cancel, one_apply_ne]
        intro e; rw [e] at hi; simp at hi
      · have hne : (⟨j, hj⟩ : Fin n) ≠ l := fun e => hlj (by rw [← e])
        rw [one_apply_ne hne, mul_zero, add_zero, hent i l (by omega)]
    · rw [if_neg hi, add_zero, hent i l (by omega)]
  refine ⟨fun i l hil => key i l (by
    rcases hil with hil | hil
    · rw [Fin.le_iff_val_le_val] at hil; omega
    · omega), ?_⟩
  rw [sdS]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun l _ => ?_
  split_ifs with hh
  · rw [key i l (by omega), one_apply_ne]
    intro e; rw [e] at hh; omega
  · rfl

def TopLeft (j : ℕ) (x : Matrix (Fin n) (Fin n) k) : Prop :=
  ∀ i l : Fin n, (j ≤ i.val ∨ j ≤ l.val) → x i l = (1 : Matrix (Fin n) (Fin n) k) i l

theorem TopLeft.good {j : ℕ} {x : Matrix (Fin n) (Fin n) k} (hx : TopLeft j x) : Good j x :=
  fun i l h => hx i l (by omega)

def dotj (j : ℕ) (ξ c : Fin n → k) : k := ∑ i : Fin n, if i.val < j then ξ i * c i else 0

def rowMul (j : ℕ) (ξ : Fin n → k) (Y : Matrix (Fin n) (Fin n) k) : Fin n → k :=
  fun a => ∑ i : Fin n, if i.val < j then ξ i * Y i a else 0

def colMul (j : ℕ) (Y : Matrix (Fin n) (Fin n) k) (c : Fin n → k) : Fin n → k :=
  fun i => ∑ a : Fin n, if a.val < j then Y i a * c a else 0

theorem dotj_colMul (j : ℕ) (ξ c : Fin n → k) (Y : Matrix (Fin n) (Fin n) k) :
    dotj j ξ (colMul j Y c) = dotj j (rowMul j ξ Y) c := by
  let F : Fin n → Fin n → k := fun i a => if i.val < j ∧ a.val < j then ξ i * Y i a * c a else 0
  have hL : dotj j ξ (colMul j Y c) = ∑ i : Fin n, ∑ a : Fin n, F i a := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i.val < j
    · rw [if_pos hi, colMul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by by_cases ha : a.val < j <;> simp [F, hi, ha, mul_assoc]
    · rw [if_neg hi]; simp [F, hi]
  have hR : dotj j (rowMul j ξ Y) c = ∑ a : Fin n, ∑ i : Fin n, F i a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a.val < j
    · rw [if_pos ha, rowMul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by by_cases hi : i.val < j <;> simp [F, hi, ha]
    · rw [if_neg ha]; simp [F, ha]
  rw [hL, hR, Finset.sum_comm]

end DiscreteGroups.sglob.LConvGenM
end
end

section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix

namespace DiscreteGroups.sglob.LConvGenM

variable {k : Type} [Field k] {n : ℕ}

theorem conj_colU (j : ℕ) (hj : j < n) (x : GL (Fin n) k) (hx : TopLeft j (x : Matrix (Fin n) (Fin n) k))
    (hy : TopLeft j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (c : Fin n → k) :
    x⁻¹ * colU j c * x = colU j (colMul j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) c) := by
  set X := (x : Matrix (Fin n) (Fin n) k)
  set Y := ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
  have hYX : Y * X = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hYC : Y * colM j c = colM j (colMul j Y c) := by
    ext i b
    rw [mul_apply, colM_apply]
    by_cases hb : b.val = j
    · simp only [colM_apply, hb, and_true]
      by_cases hi : i.val < j
      · rw [if_pos hi, colMul]
        exact Finset.sum_congr rfl fun a _ => by split_ifs <;> simp
      · rw [if_neg hi]
        refine Finset.sum_eq_zero fun a _ => ?_
        split_ifs with ha
        · rw [hy i a (Or.inl (by omega)), one_apply_ne (by intro e; rw [e] at hi; omega), zero_mul]
        · rw [mul_zero]
    · simp [colM_apply, hb]
  have hCX : ∀ d : Fin n → k, colM j d * X = colM j d := by
    intro d
    ext i l
    rw [mul_apply, Finset.sum_eq_single (⟨j, hj⟩ : Fin n)]
    · rw [hx _ l (Or.inl le_rfl)]
      by_cases hl : (⟨j, hj⟩ : Fin n) = l
      · rw [← hl, one_apply_eq, mul_one]
      · rw [one_apply_ne hl, mul_zero, colM_apply, if_neg (fun h => hl (Fin.ext h.2.symm))]
    · intro b _ hb
      rw [colM_apply, if_neg (fun h => hb (Fin.ext h.2)), zero_mul]
    · simp
  ext : 1
  rw [Units.val_mul, Units.val_mul, val_colU, val_colU, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hYX, hYC, hCX]

def i0 (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) : Fin n := ⟨j - 1, by omega⟩

section RankOne

variable (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) (ξ : Fin n → k)

def vrow : Fin n → k := fun l => if l.val < j then ξ l - (if l = i0 j hj hj1 then 1 else 0) else 0

def R1 : Matrix (Fin n) (Fin n) k := Matrix.of fun i l => if i = i0 j hj hj1 then vrow j hj hj1 ξ l else 0

theorem rankOne_mul_self : R1 j hj hj1 ξ * R1 j hj hj1 ξ = (vrow j hj hj1 ξ (i0 j hj hj1)) • R1 j hj hj1 ξ := by
  ext i l
  rw [mul_apply, Finset.sum_eq_single (i0 j hj hj1)]
  · simp only [R1, of_apply, Matrix.smul_apply, smul_eq_mul, if_true]
    split_ifs <;> ring
  · intro b _ hb; simp [R1, hb]
  · simp

theorem rowVector_at_index : vrow j hj hj1 ξ (i0 j hj hj1) = ξ (i0 j hj hj1) - 1 := by
  simp [vrow, i0, show j - 1 < j by omega]

theorem rankOne_top_left_zero : ∀ i l : Fin n, (j ≤ i.val ∨ j ≤ l.val) → R1 j hj hj1 ξ i l = 0 := by
  intro i l h
  simp only [R1, of_apply]
  split_ifs with hi
  · have : ¬ l.val < j := by rw [hi] at h; simp [i0] at h; omega
    simp [vrow, this]
  · rfl

end RankOne

end DiscreteGroups.sglob.LConvGenM
end
end

section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix

namespace DiscreteGroups.sglob.LConvGenM

variable {k : Type} [Field k] {n : ℕ}

section RankOne

variable (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) (ξ : Fin n → k) (hξ : ξ (i0 j hj hj1) ≠ 0)
include hξ

theorem coef_eq : (ξ (i0 j hj hj1))⁻¹ * (ξ (i0 j hj hj1) - 1) = 1 - (ξ (i0 j hj hj1))⁻¹ := by
  field_simp

def xA : GL (Fin n) k :=
  ⟨1 + R1 j hj hj1 ξ, 1 - (ξ (i0 j hj hj1))⁻¹ • R1 j hj hj1 ξ,
    by rw [add_mul, one_mul, mul_sub, mul_one, Matrix.mul_smul, rankOne_mul_self, smul_smul, rowVector_at_index, coef_eq j hj hj1 ξ hξ,
      sub_smul, one_smul]; abel,
    by rw [sub_mul, one_mul, mul_add, mul_one, Matrix.smul_mul, rankOne_mul_self, smul_smul, rowVector_at_index, coef_eq j hj hj1 ξ hξ,
      sub_smul, one_smul]; abel⟩

theorem topLeft_xA : TopLeft j ((xA j hj hj1 ξ hξ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  intro i l h
  show (1 + R1 j hj hj1 ξ) i l = _
  rw [Matrix.add_apply, rankOne_top_left_zero j hj hj1 ξ i l h, add_zero]

theorem topLeft_xA_inv : TopLeft j (((xA j hj hj1 ξ hξ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  intro i l h
  show (1 - (ξ (i0 j hj hj1))⁻¹ • R1 j hj hj1 ξ) i l = _
  rw [Matrix.sub_apply, Matrix.smul_apply, rankOne_top_left_zero j hj hj1 ξ i l h, smul_zero, sub_zero]

theorem rowMul_xA_inv (a : Fin n) (ha : a.val < j) :
    rowMul j ξ (((xA j hj hj1 ξ hξ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a =
      if a = i0 j hj hj1 then 1 else 0 := by
  have hi0 : (i0 j hj hj1).val < j := by simp [i0]; omega
  have key : ∀ i : Fin n, (if i.val < j then ξ i *
      (((xA j hj hj1 ξ hξ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i a else 0) =
      (if i = a then ξ a else 0) - (if i = i0 j hj hj1 then vrow j hj hj1 ξ a else 0) := by
    intro i
    show (if i.val < j then ξ i * (1 - (ξ (i0 j hj hj1))⁻¹ • R1 j hj hj1 ξ) i a else 0) = _
    by_cases hi : i.val < j
    · rw [if_pos hi]
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, R1, of_apply, one_apply]
      by_cases hia : i = a <;> by_cases hii : i = i0 j hj hj1
      · subst hia; subst hii; simp; field_simp
      · subst hia; simp [hii]
      · subst hii; simp [hia]; field_simp
      · simp [hia, hii]
    · rw [if_neg hi, if_neg (fun e => hi (by rw [e]; exact ha)), if_neg (fun e => hi (by rw [e]; exact hi0))]
      ring
  rw [rowMul, Finset.sum_congr rfl fun i _ => key i, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
  simp only [vrow, if_pos ha]
  ring

theorem dotj_xA_inv (c : Fin n → k) :
    dotj j (rowMul j ξ (((xA j hj hj1 ξ hξ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) c = c (i0 j hj hj1) := by
  have hi0 : (i0 j hj hj1).val < j := by simp [i0]; omega
  rw [dotj, Finset.sum_congr rfl fun a _ => (?_ : _ = if a = i0 j hj hj1 then c a else 0), Finset.sum_ite_eq',
    if_pos (Finset.mem_univ _)]
  by_cases ha : a.val < j
  · rw [if_pos ha, rowMul_xA_inv j hj hj1 ξ hξ a ha]
    split_ifs <;> simp
  · rw [if_neg ha, if_neg (fun e => ha (by rw [e]; exact hi0))]

end RankOne

end DiscreteGroups.sglob.LConvGenM
end
end

section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix

namespace DiscreteGroups.sglob.LConvGenM

variable {k : Type} [Field k] {n : ℕ}

variable (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) {p : Fin n} (hp : p.val < j) (hne : p ≠ i0 j hj hj1)
include hp

theorem topLeft_single (y : k) (i l : Fin n) (h : j ≤ i.val ∨ j ≤ l.val) :
    Matrix.single p (i0 j hj hj1) y i l = 0 := by
  have hi0 : (i0 j hj hj1).val < j := by simp [i0]; omega
  rw [Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  omega

theorem topLeft_elem (y : k) : TopLeft j ((GlobalTheory.RootUp.elem hne y : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  intro i l h
  rw [GlobalTheory.RootUp.val_elem, Matrix.add_apply, topLeft_single j hj hj1 hp y i l h, add_zero]

theorem topLeft_elem_inv (y : k) :
    TopLeft j (((GlobalTheory.RootUp.elem hne y)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  intro i l h
  show (1 - Matrix.single p (i0 j hj hj1) y) i l = _
  rw [Matrix.sub_apply, topLeft_single j hj hj1 hp y i l h, sub_zero]

theorem rowMul_elem_inv (ξ : Fin n → k) :
    rowMul j ξ (((GlobalTheory.RootUp.elem hne (-1 : k))⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (i0 j hj hj1) =
      ξ (i0 j hj hj1) + ξ p := by
  have hi0 : (i0 j hj hj1).val < j := by simp [i0]; omega
  have key : ∀ i : Fin n, (if i.val < j then ξ i *
      (((GlobalTheory.RootUp.elem hne (-1 : k))⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i (i0 j hj hj1) else 0) =
      (if i = i0 j hj hj1 then ξ (i0 j hj hj1) else 0) + (if i = p then ξ p else 0) := by
    intro i
    show (if i.val < j then ξ i * (1 - Matrix.single p (i0 j hj hj1) (-1 : k)) i (i0 j hj hj1) else 0) = _
    rw [Matrix.sub_apply, Matrix.single_apply, one_apply]
    by_cases hi : i.val < j
    · rw [if_pos hi]
      by_cases h1 : i = i0 j hj hj1
      · subst h1
        have : ¬ (p = i0 j hj hj1) := hne
        simp [this, Ne.symm hne]
      · by_cases h2 : i = p
        · subst h2; simp [h1]
        · simp [h1, h2, Ne.symm h2]
    · rw [if_neg hi, if_neg (fun e => hi (by rw [e]; exact hi0)), if_neg (fun e => hi (by rw [e]; exact hp)),
        add_zero]
  rw [rowMul, Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]

end DiscreteGroups.sglob.LConvGenM
end
end

section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix DiscreteGroups.sglob.LConvGenM

namespace DiscreteGroups.sglob.LConvGenR

variable {k : Type} [Field k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (GL (Fin n) k) V) (ψ : AddChar k Circle)

def chM (m : ℕ) (g : GL (Fin n) k) : ℂ := ((ψ (sdS m (g : Matrix (Fin n) (Fin n) k)) : Circle) : ℂ)

def KN (m : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {w | ∃ g ∈ Nset m, ∃ v : V, w = π g v - chM ψ m g • v}

def KUS (j : ℕ) (S : Finset (Fin n)) (ξ : Fin n → k) : Submodule ℂ V :=
  Submodule.span ℂ {w | ∃ c : Fin n → k, (∀ r ∉ S, c r = 0) ∧ ∃ v : V,
    w = π (colU j c) v - ((ψ (dotj j ξ c) : Circle) : ℂ) • v}

theorem conj_apply (x g : GL (Fin n) k) (v : V) : π x (π g v) = π (x * g * x⁻¹) (π x v) := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

theorem KN_stable (j : ℕ) (x : GL (Fin n) k) (hx : Good j (x : Matrix (Fin n) (Fin n) k))
    (hy : Good j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) {w : V} (hw : w ∈ KN π ψ (j + 1)) :
    π x w ∈ KN π ψ (j + 1) := by
  refine (Submodule.span_le.2 ?_ : KN π ψ (j + 1) ≤ (KN π ψ (j + 1)).comap (π x)) hw
  rintro _ ⟨g, hg, v, rfl⟩
  obtain ⟨h1, h2⟩ := good_conj x hx hy hg
  refine Submodule.subset_span ⟨x * g * x⁻¹, h1, π x v, ?_⟩
  rw [map_sub, map_smul, conj_apply, chM, chM, h2]

theorem colU_comm (j : ℕ) (c d : Fin n → k) : colU j c * colU j d = colU j d * colU j c := by
  rw [← colU_add, ← colU_add, add_comm]

theorem KUS_stable (j : ℕ) (S : Finset (Fin n)) (ξ d : Fin n → k) {w : V} (hw : w ∈ KUS π ψ j S ξ) :
    π (colU j d) w ∈ KUS π ψ j S ξ := by
  refine (Submodule.span_le.2 ?_ : KUS π ψ j S ξ ≤ (KUS π ψ j S ξ).comap (π (colU j d))) hw
  rintro _ ⟨c, hc, v, rfl⟩
  refine Submodule.subset_span ⟨c, hc, π (colU j d) v, ?_⟩
  rw [map_sub, map_smul, ← Module.End.mul_apply, ← map_mul, colU_comm, map_mul, Module.End.mul_apply]

theorem W_stable (j : ℕ) (S : Finset (Fin n)) (ξ d : Fin n → k) {w : V}
    (hw : w ∈ KN π ψ (j + 1) ⊔ KUS π ψ j S ξ) : π (colU j d) w ∈ KN π ψ (j + 1) ⊔ KUS π ψ j S ξ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
  rw [map_add]
  exact Submodule.add_mem_sup (KN_stable π ψ j _ (good_colU j d) (good_colU_inv j d) ha)
    (KUS_stable π ψ j S ξ d hb)

theorem KN_top (m : ℕ) (hm : n ≤ m) : KN π ψ m = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨g, hg, v, rfl⟩
  have hg1 : g = 1 := by
    ext i l
    rw [hg i l (Or.inr (by omega)), Units.val_one]
  have hs : sdS m ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun l _ => ?_
    rw [if_neg (by omega)]
  rw [hg1, chM, hs, AddChar.map_zero_eq_one, Circle.coe_one, one_smul, map_one, Module.End.one_apply, sub_self]

end DiscreteGroups.sglob.LConvGenR
end
end

section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix DiscreteGroups.sglob.LConvGenM

namespace DiscreteGroups.sglob.LConvGenR

variable {k : Type} [Field k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (GL (Fin n) k) V) (ψ : AddChar k Circle)

theorem univ_supp (c : Fin n → k) : ∀ r ∉ (Finset.univ : Finset (Fin n)), c r = 0 :=
  fun r hr => absurd (Finset.mem_univ r) hr

theorem conj_S (j : ℕ) (hj : j < n) (x : GL (Fin n) k) (hx : TopLeft j (x : Matrix (Fin n) (Fin n) k))
    (hy : TopLeft j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (ξ : Fin n → k) {w : V}
    (hw : w ∈ KN π ψ (j + 1) ⊔ KUS π ψ j Finset.univ (rowMul j ξ ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) :
    π x⁻¹ w ∈ KN π ψ (j + 1) ⊔ KUS π ψ j Finset.univ ξ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
  rw [map_add]
  refine Submodule.add_mem_sup (KN_stable π ψ j _ hy.good (by rw [inv_inv]; exact hx.good) ha) ?_
  refine (Submodule.span_le.2 ?_ : KUS π ψ j Finset.univ (rowMul j ξ ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))
    ≤ (KUS π ψ j Finset.univ ξ).comap (π x⁻¹)) hb
  rintro _ ⟨c, -, v, rfl⟩
  refine Submodule.subset_span ⟨colMul j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) c, univ_supp _, π x⁻¹ v, ?_⟩
  rw [map_sub, map_smul, conj_apply, inv_inv, conj_colU j hj x hx hy, dotj_colMul]

theorem ne_top_of_conj (j : ℕ) (hj : j < n) (x : GL (Fin n) k) (hx : TopLeft j (x : Matrix (Fin n) (Fin n) k))
    (hy : TopLeft j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (ξ : Fin n → k)
    (h : KN π ψ (j + 1) ⊔ KUS π ψ j Finset.univ ξ ≠ ⊤) :
    KN π ψ (j + 1) ⊔ KUS π ψ j Finset.univ (rowMul j ξ ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) ≠ ⊤ := by
  intro htop
  apply h
  refine eq_top_iff.2 fun v _ => ?_
  have := conj_S π ψ j hj x hx hy ξ (w := π x v) (by rw [htop]; exact Submodule.mem_top)
  rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this

theorem KN_le (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) (η : Fin n → k) (hη : ∀ c, dotj j η c = c (i0 j hj hj1)) :
    KN π ψ j ≤ KN π ψ (j + 1) ⊔ KUS π ψ j Finset.univ η := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, hg, v, rfl⟩
  obtain ⟨h1, h2⟩ := peel_N j hj hj1 hg
  set c : Fin n → k := fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩ with hc
  set n' := colU j (-c) * g with hn'
  have hg' : g = colU j c * n' := by rw [hn', ← mul_assoc, ← colU_add, add_neg_cancel, colU_zero, one_mul]
  have hch : chM ψ j g = chM ψ (j + 1) n' * ((ψ (c (i0 j hj hj1)) : Circle) : ℂ) := by
    rw [chM, chM, h2, AddChar.map_add_eq_mul, Circle.coe_mul]; rfl
  have e : π g v - chM ψ j g • v = π (colU j c) (π n' v - chM ψ (j + 1) n' • v) +
      chM ψ (j + 1) n' • (π (colU j c) v - ((ψ (dotj j η c) : Circle) : ℂ) • v) := by
    rw [hη, hch, map_sub, map_smul, smul_sub, smul_smul]
    conv_lhs => rw [hg', map_mul, Module.End.mul_apply]
    abel
  show _ ∈ _
  rw [e]
  refine Submodule.add_mem_sup (KN_stable π ψ j _ (good_colU j c) (good_colU_inv j c)
    (Submodule.subset_span ⟨n', h1, v, rfl⟩)) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, univ_supp c, v, rfl⟩))

theorem twKer_le (j : ℕ) (hj : j < n) (h : ∑ i, ![j, n - j] i = n) (ξ : Fin n → k) (hz : ∀ i : Fin n, i.val < j → ξ i = 0) :
    twKer π (unipRad k (stdBlocks ![j, n - j] h)) 1 ≤ KN π ψ (j + 1) ⊔ KUS π ψ j Finset.univ ξ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨g, hg⟩, v, rfl⟩
  obtain ⟨h1, h2⟩ := peel_rad j hj h hg
  set c : Fin n → k := fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩ with hc
  set n' := colU j (-c) * g with hn'
  have hg' : g = colU j c * n' := by rw [hn', ← mul_assoc, ← colU_add, add_neg_cancel, colU_zero, one_mul]
  have hch : chM ψ (j + 1) n' = 1 := by rw [chM, h2, AddChar.map_zero_eq_one, Circle.coe_one]
  have hd : dotj j ξ c = 0 := Finset.sum_eq_zero fun i _ => by
    by_cases hi : i.val < j
    · rw [if_pos hi, hz i hi, zero_mul]
    · rw [if_neg hi]
  have e : π g v - (((1 : ↥(unipRad k (stdBlocks ![j, n - j] h)) →* ℂˣ) ⟨g, hg⟩ : ℂˣ) : ℂ) • v =
      π (colU j c) (π n' v - chM ψ (j + 1) n' • v) + (π (colU j c) v - ((ψ (dotj j ξ c) : Circle) : ℂ) • v) := by
    rw [hch, hd, AddChar.map_zero_eq_one, Circle.coe_one, MonoidHom.one_apply, Units.val_one, one_smul,
      map_sub]
    conv_lhs => rw [hg', map_mul, Module.End.mul_apply]
    abel
  show _ ∈ _
  rw [e]
  exact Submodule.add_mem_sup (KN_stable π ψ j _ (good_colU j c) (good_colU_inv j c)
    (Submodule.subset_span ⟨n', h1, v, rfl⟩)) (Submodule.subset_span ⟨c, univ_supp c, v, rfl⟩)

end DiscreteGroups.sglob.LConvGenR
end
end

section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix DiscreteGroups.sglob.LConvGenM DiscreteGroups.sglob.LConvGenF

namespace DiscreteGroups.sglob.LConvGenR

section Dot

variable {k : Type} [Field k] {n : ℕ}

theorem dotj_add (j : ℕ) (ξ c d : Fin n → k) : dotj j ξ (c + d) = dotj j ξ c + dotj j ξ d := by
  simp only [dotj, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [mul_add]

theorem dotj_single (j : ℕ) (ξ : Fin n → k) (a : Fin n) (x : k) :
    dotj j ξ (Pi.single a x) = if a.val < j then ξ a * x else 0 := by
  rw [dotj, Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem dotj_update (j : ℕ) (ξ c : Fin n → k) (a : Fin n) (x : k) (hc : c a = 0) :
    dotj j (Function.update ξ a x) c = dotj j ξ c := by
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i = a
  · subst hi; simp [hc]
  · rw [Function.update_of_ne hi]

end Dot

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (GL (Fin n) k) V) (ψ : AddChar k Circle)

theorem KUS_empty (j : ℕ) (ξ : Fin n → k) : KUS π ψ j ∅ ξ = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨c, hc, v, rfl⟩
  have : c = 0 := funext fun r => hc r (Finset.notMem_empty r)
  subst this
  have h0 : dotj j ξ (0 : Fin n → k) = 0 := Finset.sum_eq_zero fun i _ => by split_ifs <;> simp
  rw [colU_zero, h0, AddChar.map_zero_eq_one, Circle.coe_one, one_smul, map_one, Module.End.one_apply, sub_self]

theorem smooth_col (hs : IsSmooth π) (j : ℕ) (hj : j < n) (a : Fin n) (v : V) :
    ∃ s : kˣ, ∀ h ∈ ball s, π (colU j (Pi.single a h)) v = v := by
  by_cases ha : a.val < j
  · have hne : a ≠ (⟨j, hj⟩ : Fin n) := fun e => by
      have := congrArg Fin.val e; simp at this; omega
    have hU : {g : GL (Fin n) k | π g v = v} ∈ nhds (1 : GL (Fin n) k) := (hs v).mem_nhds (by simp)
    have h0 : GlobalTheory.RootUp.elem hne (0 : k) = 1 := Units.ext (by simp [GlobalTheory.RootUp.val_elem])
    have hpre : (GlobalTheory.RootUp.elem hne) ⁻¹' {g : GL (Fin n) k | π g v = v} ∈ nhds (0 : k) :=
      (GlobalTheory.RootUp.continuous_elem hne).continuousAt.preimage_mem_nhds (by rw [h0]; exact hU)
    obtain ⟨s, hs'⟩ := exists_cball_subset hpre
    refine ⟨s, fun h hh => ?_⟩
    rw [colU_single_of_lt j hj ha]
    exact hs' hh
  · exact ⟨1, fun h _ => by rw [colU_single_of_ge j (by omega), map_one, Module.End.one_apply]⟩

end DiscreteGroups.sglob.LConvGenR
end
end

section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix DiscreteGroups.sglob.LConvGenM DiscreteGroups.sglob.LConvGenF

namespace DiscreteGroups.sglob.LConvGenR

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (GL (Fin n) k) V) (ψ : AddChar k Circle)

theorem exists_col_char {c : kˣ} (hc : HasConductor ψ c) (hs : IsSmooth π) (j : ℕ) (hj : j < n)
    (h0 : KN π ψ (j + 1) ≠ ⊤) (S : Finset (Fin n)) : ∃ ξ : Fin n → k, KN π ψ (j + 1) ⊔ KUS π ψ j S ξ ≠ ⊤ := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by rw [KUS_empty, sup_bot_eq]; exact h0⟩
  | insert a S ha ih =>
    obtain ⟨ξ, hξ⟩ := ih
    let σ : k → V →ₗ[ℂ] V := fun t => π (colU j (Pi.single a t))
    have hadd : ∀ s t, σ (s + t) = σ s * σ t := fun s t => by
      simp only [σ]; rw [Pi.single_add, colU_add, map_mul]
    have hW : ∀ t, ∀ w ∈ KN π ψ (j + 1) ⊔ KUS π ψ j S ξ, σ t w ∈ KN π ψ (j + 1) ⊔ KUS π ψ j S ξ :=
      fun t w hw => W_stable π ψ j S ξ _ hw
    obtain ⟨ξa, hξa⟩ := exists_character_sup_ne_top ψ σ hc hadd _ hW (fun v => smooth_col π hs j hj a v) hξ
    refine ⟨Function.update ξ a ξa, fun htop => hξa (eq_top_iff.2 ?_)⟩
    rw [← htop]
    refine sup_le (le_sup_left.trans le_sup_left) (Submodule.span_le.2 ?_)
    rintro _ ⟨c, hcS, v, rfl⟩
    set cS := Function.update c a 0 with hcS'
    have hcS0 : ∀ r ∉ S, cS r = 0 := by
      intro r hr
      by_cases hra : r = a
      · subst hra; simp [cS]
      · rw [hcS', Function.update_of_ne hra]; exact hcS r (by simp [hra, hr])
    have hsplit : c = Pi.single a (c a) + cS := by
      funext r
      by_cases hra : r = a
      · subst hra; simp [cS]
      · simp [cS, hra, Pi.single_apply]
    have hdot : dotj j (Function.update ξ a ξa) c =
        dotj j (Function.update ξ a ξa) (Pi.single a (c a)) + dotj j ξ cS := by
      conv_lhs => rw [hsplit]
      rw [dotj_add, dotj_update j ξ cS a ξa (by simp [cS])]
    have e : π (colU j c) v - ((ψ (dotj j (Function.update ξ a ξa) c) : Circle) : ℂ) • v =
        σ (c a) (π (colU j cS) v - ((ψ (dotj j ξ cS) : Circle) : ℂ) • v) +
        ((ψ (dotj j ξ cS) : Circle) : ℂ) • (σ (c a) v -
          ((ψ (dotj j (Function.update ξ a ξa) (Pi.single a (c a))) : Circle) : ℂ) • v) := by
      have hcol : π (colU j c) v = σ (c a) (π (colU j cS) v) := by
        conv_lhs => rw [hsplit]
        rw [colU_add, map_mul, Module.End.mul_apply]
      rw [hcol, hdot, AddChar.map_add_eq_mul, Circle.coe_mul, map_sub, map_smul, smul_sub, smul_smul,
        mul_comm ((ψ (dotj j (Function.update ξ a ξa) (Pi.single a (c a))) : Circle) : ℂ)]
      abel
    show _ ∈ _
    rw [e]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (hW _ _ (Submodule.mem_sup_right
      (Submodule.subset_span ⟨cS, hcS0, v, rfl⟩)))) (Submodule.smul_mem _ _ ?_)
    rw [dotj_single]
    by_cases haj : a.val < j
    · rw [if_pos haj, Function.update_self]
      exact Submodule.mem_sup_right (Submodule.subset_span ⟨c a, v, rfl⟩)
    · rw [if_neg haj, AddChar.map_zero_eq_one, Circle.coe_one, one_smul]
      simp only [σ]
      rw [colU_single_of_ge j (by omega), map_one, Module.End.one_apply, sub_self]
      exact Submodule.zero_mem _

end DiscreteGroups.sglob.LConvGenR
end
end

section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix DiscreteGroups.sglob.LConvGenM DiscreteGroups.sglob.LConvGenF

namespace DiscreteGroups.sglob.LConvGenR

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (GL (Fin n) k) V) (ψ : AddChar k Circle)

theorem step {c : kˣ} (hc : HasConductor ψ c) (hcusp : IsCuspidal π) (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j)
    (h0 : KN π ψ (j + 1) ≠ ⊤) : KN π ψ j ≠ ⊤ := by
  obtain ⟨ξ, hξ⟩ := exists_col_char π ψ hc hcusp.1 j hj h0 Finset.univ
  by_cases hz : ∀ i : Fin n, i.val < j → ξ i = 0
  · exfalso
    have h : ∑ i, ![j, n - j] i = n := by simp [Fin.sum_univ_two]; omega
    have htw : twKer π (unipRad k (stdBlocks ![j, n - j] h)) 1 = ⊤ :=
      Submodule.Quotient.subsingleton_iff.1 (hcusp.2 2 ![j, n - j] (stdBlocks ![j, n - j] h)
        (GlobalTheory.T.unipRad_stdBlocks_two_ne_bot' k n j (n - j) h hj1 (by omega)))
    exact hξ (eq_top_iff.2 (by rw [← htw]; exact twKer_le π ψ j hj h ξ hz))
  · push Not at hz
    obtain ⟨p, hp, hpξ⟩ := hz
    obtain ⟨ξ1, h1, hξ1⟩ : ∃ ξ1 : Fin n → k, ξ1 (i0 j hj hj1) ≠ 0 ∧
        KN π ψ (j + 1) ⊔ KUS π ψ j Finset.univ ξ1 ≠ ⊤ := by
      by_cases hi0 : ξ (i0 j hj hj1) = 0
      · have hne : p ≠ i0 j hj hj1 := fun e => hpξ (by rw [e]; exact hi0)
        refine ⟨_, ?_, ne_top_of_conj π ψ j hj (GlobalTheory.RootUp.elem hne (-1 : k))
          (topLeft_elem j hj hj1 hp hne _) (topLeft_elem_inv j hj hj1 hp hne _) ξ hξ⟩
        rw [rowMul_elem_inv j hj hj1 hp hne ξ, hi0, zero_add]
        exact hpξ
      · exact ⟨ξ, hi0, hξ⟩
    have h2 := ne_top_of_conj π ψ j hj (xA j hj hj1 ξ1 h1) (topLeft_xA j hj hj1 ξ1 h1)
      (topLeft_xA_inv j hj hj1 ξ1 h1) ξ1 hξ1
    exact fun htop => h2 (eq_top_iff.2 (by rw [← htop]; exact KN_le π ψ j hj hj1 _ (dotj_xA_inv j hj hj1 ξ1 h1)))

theorem KN_one_ne_top [Nontrivial V] {c : kˣ} (hc : HasConductor ψ c) (hcusp : IsCuspidal π) :
    KN π ψ 1 ≠ ⊤ := by
  have hbase : ∀ m, n ≤ m → KN π ψ m ≠ ⊤ := fun m hm => by rw [KN_top π ψ m hm]; exact bot_ne_top
  have key : ∀ d, d + 1 ≤ n → KN π ψ (n - d) ≠ ⊤ := by
    intro d
    induction d with
    | zero => intro _; exact hbase _ (by omega)
    | succ d ih =>
      intro hd
      refine step π ψ hc hcusp (n - (d + 1)) (by omega) (by omega) ?_
      rw [show n - (d + 1) + 1 = n - d by omega]
      exact ih (by omega)
  by_cases hn : n ≤ 1
  · exact hbase 1 hn
  · have := key (n - 1) (by omega)
    rwa [show n - (n - 1) = 1 by omega] at this

theorem sdS_one (M : Matrix (Fin n) (Fin n) k) : sdS 1 M = ∑ i : Fin n, ∑ l : Fin n with l.val = i.val + 1, M i l := by
  simp only [sdS, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)

theorem mem_Nset_one {u : GL (Fin n) k} (hu : u ∈ unipB k (Fin n)) : u ∈ Nset 1 := by
  obtain ⟨h1, h2⟩ := (mem_unipB k).1 hu
  intro i l hil
  have hli : l ≤ i := hil.elim id (fun h => by rw [Fin.le_iff_val_le_val]; omega)
  rcases hli.lt_or_eq with hlt | heq
  · rw [h1 i l hlt, one_apply_ne (ne_of_gt hlt)]
  · rw [heq, h2 i, one_apply_eq]

end DiscreteGroups.sglob.LConvGenR

namespace DiscreteGroups.sglob.LConv

open DiscreteGroups.sglob.LConvGenR

theorem cuspGen : CuspGen := by
  intro k _ _ _ _ ψ hψ hψ1 n V _ _ π hV hcusp
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ hψ1
  have hne := KN_one_ne_top π ψ hc hcusp
  obtain ⟨x, hx⟩ : ∃ x, x ∉ KN π ψ 1 := by
    by_contra h
    push Not at h
    exact hne (eq_top_iff.2 fun x _ => h x)
  obtain ⟨f, hfx, hker⟩ := Submodule.exists_le_ker_of_notMem hx
  refine ⟨f, fun h0 => hfx (by rw [h0]; rfl), fun u hu v => ?_⟩
  have hmem : π u v - chM ψ 1 u • v ∈ KN π ψ 1 := Submodule.subset_span ⟨u, mem_Nset_one hu, v, rfl⟩
  have h1 := hker hmem
  rw [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at h1
  rw [h1, smul_eq_mul, chM, sdS_one]
  rfl

end DiscreteGroups.sglob.LConv
end
end
