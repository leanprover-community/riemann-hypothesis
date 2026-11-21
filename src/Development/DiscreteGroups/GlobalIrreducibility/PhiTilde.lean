import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
import Development.DiscreteGroups.GlobalIrreducibility.DzRedSupp
import Development.DiscreteGroups.GlobalIrreducibility.DzRedTil
import Development.DiscreteGroups.GlobalIrreducibility.DzIsoKO
import Development.DiscreteGroups.GlobalIrreducibility.LConvSepI

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker GroundTheory.Automorphic

namespace DiscreteGroups.sglob.DzRed

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem rep_conj {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (t u : G) (v : V) :
    π (t * u * t⁻¹) (π t v) = π t (π u v) := by
  simp only [map_mul, Module.End.mul_apply]
  congr 2
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem unipRadical_le_unipB {F : Type} [Field F] {n a : ℕ} {u : GL (Fin n) F}
    (hu : u ∈ GlobalTheory.FiniteGL.unipRadical F (GlobalTheory.FiniteGL.twoBlocks n a)) : u ∈ unipB F (Fin n) := by
  have h := GlobalTheory.FiniteGL.mem_unipRadical.1 hu
  rw [mem_unipB]
  refine ⟨fun p q hqp => ?_, fun p => ?_⟩
  · have := h p q (by
      have : q.val < p.val := hqp
      simp only [GlobalTheory.FiniteGL.twoBlocks]; split_ifs <;> omega)
    rwa [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_gt hqp), sub_zero] at this
  · have := h p p le_rfl
    rwa [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at this

theorem val_uniformizer_pow_lt {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (k : ℕ) {y : K} (hy : valuation K y ≤ 1) :
    valuation K ((GLnLocal.uniformizer K : K) ^ (k + 1) * y) < 1 := by
  have hlt := GLnLocal.valuation_uniformizer_lt_one K
  rw [map_mul, map_pow]
  calc valuation K (GLnLocal.uniformizer K : K) ^ (k + 1) * valuation K y
      ≤ valuation K (GLnLocal.uniformizer K : K) ^ (k + 1) := mul_le_of_le_one_right' hy
    _ = valuation K (GLnLocal.uniformizer K : K) ^ k * valuation K (GLnLocal.uniformizer K : K) := pow_succ _ _
    _ ≤ valuation K (GLnLocal.uniformizer K : K) := mul_le_of_le_one_left' (pow_le_one' hlt.le k)
    _ < 1 := hlt

theorem torus_entry {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {n : ℕ} (d : Fin n → ℤ) (a b : Fin n) (k : ℕ) (hk : d b = d a + ((k + 1 : ℕ) : ℤ)) (y : K) :
    ((Iwasawa.uniformizerUnit K ^ d a : Kˣ) : K) * ((GLnLocal.uniformizer K : K) ^ (k + 1) * y) *
      ((Iwasawa.uniformizerUnit K ^ d b : Kˣ) : K)⁻¹ = y := by
  have hϖ : (GLnLocal.uniformizer K : K) ≠ 0 := fun h =>
    (GLnLocal.irreducible_uniformizer K).ne_zero (Subtype.ext h)
  rw [hk, zpow_add, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, zpow_natCast,
    Iwasawa.coe_uniformizerUnit]
  have h1 : (GLnLocal.uniformizer K : K) ^ d a ≠ 0 := zpow_ne_zero _ hϖ
  have h2 : (GLnLocal.uniformizer K : K) ^ (k + 1) ≠ 0 := pow_ne_zero _ hϖ
  field_simp

theorem torus_entry' {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {n : ℕ} (d : Fin n → ℤ) (a b : Fin n) (k : ℕ) (hk : d a = d b + ((k + 1 : ℕ) : ℤ)) (y : K) :
    ((Iwasawa.uniformizerUnit K ^ d a : Kˣ) : K) * y * ((Iwasawa.uniformizerUnit K ^ d b : Kˣ) : K)⁻¹ =
      (GLnLocal.uniformizer K : K) ^ (k + 1) * y := by
  have hϖ : (GLnLocal.uniformizer K : K) ≠ 0 := fun h =>
    (GLnLocal.irreducible_uniformizer K).ne_zero (Subtype.ext h)
  rw [hk, zpow_add, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, zpow_natCast,
    Iwasawa.coe_uniformizerUnit]
  have h1 : (GLnLocal.uniformizer K : K) ^ d b ≠ 0 := zpow_ne_zero _ hϖ
  field_simp

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
  {ψ₀ : AddChar (ZMod g) Circle} {ψ : AddChar (w.adicCompletion E) Circle}

include hi in
theorem psi_eq_one (hψ : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x)) {y : w.adicCompletion E}
    (hy : valuation (w.adicCompletion E) y < 1) : ψ y = 1 := by
  have h1 : ‖i.symm y‖ < 1 :=
    (DzIso.valuation_lt_iff i hi (i.symm y)).1 (by rwa [RingEquiv.apply_symm_apply])
  let x : ℤ_[g] := ⟨i.symm y, h1.le⟩
  have hx : i (x : ℚ_[g]) = y := RingEquiv.apply_symm_apply i y
  rw [← hx, hψ]
  have h2 : PadicInt.toZMod x = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
    exact h1
  rw [h2, AddChar.map_zero_eq_one]

theorem exists_psi_ne_one (hψ : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x)) (h0 : ψ₀ ≠ 1) :
    ∃ x : ℤ_[g], ψ (i (x : ℚ_[g])) ≠ 1 := by
  obtain ⟨z, hz⟩ : ∃ z, ψ₀ z ≠ 1 := by
    by_contra h
    push Not at h
    exact h0 (AddChar.ext ψ₀ 1 fun z => (h z).trans (AddChar.one_apply z).symm)
  refine ⟨(z.val : ℤ_[g]), ?_⟩
  rw [hψ, map_natCast, ZMod.natCast_zmod_val]
  exact hz

include hi in
theorem fix_of_mem_KOne {n : ℕ} (τ : FDRep ℂ (Gn g n)) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (φ : τ →ₗ[ℂ] V)
    (hφ : ∀ (κ : GL (Fin n) ℤ_[g]) (x : τ),
      φ (τ.ρ (red g n κ) x) = π (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n κ)) (φ x))
    {k : GL (Fin n) (w.adicCompletion E)} (hk : k ∈ KOne (w.adicCompletion E) (Fin n)) (x : τ) :
    π k (φ x) = φ x := by
  obtain ⟨κ, h1, rfl⟩ := DzIso.exists_of_mem_KOne i hi hk
  rw [← hφ, h1, map_one]
  rfl

end DiscreteGroups.sglob.DzRed
end
end

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker GroundTheory.Automorphic

namespace DiscreteGroups.sglob.DzRed

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
  {ψ₀ : AddChar (ZMod g) Circle} {ψ : AddChar (w.adicCompletion E) Circle}

include hi in
theorem step_up (hψ : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x)) (h0 : ψ₀ ≠ 1) {n : ℕ}
    (τ : FDRep ℂ (Gn g n)) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (φ : τ →ₗ[ℂ] V)
    (hφ : ∀ (κ : GL (Fin n) ℤ_[g]) (x : τ),
      φ (τ.ρ (red g n κ) x) = π (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n κ)) (φ x))
    (L : Module.Dual ℂ V) (hL : IsFunctional ψ π L) (x : τ) (d : Fin n → ℤ) (a b : Fin n)
    (hb : b.val = a.val + 1) (hd : d a < d b) :
    L (π (Iwasawa.torusPow (w.adicCompletion E) n d) (φ x)) = 0 := by
  obtain ⟨x0, hx0⟩ := exists_psi_ne_one i hψ h0
  have hab : a ≠ b := fun h => by rw [h] at hb; omega
  have hlt : a < b := by rw [Fin.lt_def]; omega
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d b = d a + ((k + 1 : ℕ) : ℤ) := ⟨(d b - d a - 1).toNat, by omega⟩
  have hyv : valuation (w.adicCompletion E) (i (x0 : ℚ_[g])) ≤ 1 := (DzIso.valuation_le_iff i hi _).2 x0.2
  set c : w.adicCompletion E := (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) ^ (k + 1) *
    i (x0 : ℚ_[g]) with hc_def
  have hcv : valuation (w.adicCompletion E) c < 1 := val_uniformizer_pow_lt k hyv
  have hmem : tv a b hab c ∈ KOne (w.adicCompletion E) (Fin n) := by
    rw [GlobalTheory.StepData.mem_KOne]
    intro p q
    show valuation (w.adicCompletion E) (((tv a b hab c : Matrix (Fin n) (Fin n) (w.adicCompletion E)) - 1) p q) < 1
    rw [Matrix.sub_apply, tv_apply, add_sub_cancel_left]
    split_ifs
    · exact hcv
    · simp
  have hconj : Iwasawa.torusPow (w.adicCompletion E) n d * tv a b hab c *
      (Iwasawa.torusPow (w.adicCompletion E) n d)⁻¹ = tv a b hab (i (x0 : ℚ_[g])) := by
    rw [Iwasawa.torusPow, conj_tv, hc_def, torus_entry d a b k hk]
  have key := hL _ (tv_mem_unipB a b hlt (i (x0 : ℚ_[g]))) (π (Iwasawa.torusPow (w.adicCompletion E) n d) (φ x))
  rw [superDiag_tv a b hb] at key
  rw [← hconj, rep_conj, fix_of_mem_KOne i hi τ π φ hφ hmem] at key
  have hne : (ψ (i (x0 : ℚ_[g])) : ℂ) ≠ 1 := fun h => hx0 (Circle.ext (by simpa using h))
  have h2 : (1 - (ψ (i (x0 : ℚ_[g])) : ℂ)) * L (π (Iwasawa.torusPow (w.adicCompletion E) n d) (φ x)) = 0 := by
    rw [sub_mul, one_mul]; exact sub_eq_zero.2 key
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne.symm)

end DiscreteGroups.sglob.DzRed
end
end

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker GroundTheory.Automorphic

namespace DiscreteGroups.sglob.DzRed

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
  {ψ₀ : AddChar (ZMod g) Circle} {ψ : AddChar (w.adicCompletion E) Circle}

include hi in
theorem step_down (hψ : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x)) {n : ℕ}
    (τ : FDRep ℂ (Gn g n)) (hτ : IsCusp τ.character) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (φ : τ →ₗ[ℂ] V)
    (hφ : ∀ (κ : GL (Fin n) ℤ_[g]) (x : τ),
      φ (τ.ρ (red g n κ) x) = π (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n κ)) (φ x))
    (L : Module.Dual ℂ V) (hL : IsFunctional ψ π L) (x : τ) (d : Fin n → ℤ) (a b : Fin n)
    (hb : b.val = a.val + 1) (hd : d b < d a) :
    L (π (Iwasawa.torusPow (w.adicCompletion E) n d) (φ x)) = 0 := by
  classical
  have hS := DzLc.sum_unip_eq_zero τ hτ (Nat.succ_pos a.val) (by have := b.isLt; omega)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d a = d b + ((k + 1 : ℕ) : ℤ) := ⟨(d a - d b - 1).toNat, by omega⟩
  have hterm : ∀ u ∈ GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n (a.val + 1)),
      L (π (Iwasawa.torusPow (w.adicCompletion E) n d) (φ (τ.ρ u x))) =
        L (π (Iwasawa.torusPow (w.adicCompletion E) n d) (φ x)) := by
    intro u hu
    obtain ⟨κ, hκ, hmem⟩ := DzLc.exists_lift i u hu
    rw [← hκ, hφ]
    have hU := unipRadical_le_unipB hmem
    rw [← rep_conj π _ _ (φ x), hL _ (by rw [Iwasawa.torusPow]; exact conj_mem_unipB _ hU)]
    rw [psi_eq_one i hi hψ, Circle.coe_one, one_mul]
    rw [Iwasawa.torusPow, superDiag_conj]
    refine Valuation.map_sum_lt _ one_ne_zero fun p _ => Valuation.map_sum_lt _ one_ne_zero fun q hq => ?_
    have hq' : q.val = p.val + 1 := (Finset.mem_filter.1 hq).2
    have hent : ∀ r s : Fin n, valuation (w.adicCompletion E)
        ((Matrix.GeneralLinearGroup.map i.toRingHom (inc g n κ) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) r s) ≤ 1 :=
      fun r s => (DzIso.valuation_le_iff i hi _).2 (κ r s).2
    by_cases hp : p = a
    · have hqb : q = b := Fin.ext (by rw [hq', hb, hp])
      rw [hp, hqb, torus_entry' d a b k hk]
      exact val_uniformizer_pow_lt k (hent a b)
    · have hpa : p.val ≠ a.val := fun h => hp (Fin.ext h)
      have h0 : (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n κ) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
          p q = 0 := by
        have := (GlobalTheory.FiniteGL.mem_unipRadical.1 hmem) p q (by
          simp only [GlobalTheory.FiniteGL.twoBlocks]; split_ifs <;> omega)
        rwa [Matrix.sub_apply, Matrix.one_apply_ne (fun h => by rw [h] at hq'; omega), sub_zero] at this
      rw [h0]; simp
  have h3 := congrArg (fun F : Module.End ℂ τ => L (π (Iwasawa.torusPow (w.adicCompletion E) n d) (φ (F x)))) hS
  simp only [LinearMap.sum_apply, map_sum, LinearMap.zero_apply, map_zero] at h3
  rw [Finset.sum_congr rfl
    (fun (u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n (a.val + 1))) _ => hterm u.1 u.2), Finset.sum_const, Finset.card_univ, smul_eq_zero] at h3
  exact h3.resolve_left Fintype.card_ne_zero

end DiscreteGroups.sglob.DzRed
end
end

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker GroundTheory.Automorphic

namespace DiscreteGroups.sglob.DzRed

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
  {ψ₀ : AddChar (ZMod g) Circle} {ψ : AddChar (w.adicCompletion E) Circle}

include hi in

theorem supp_const (hψ : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x)) (h0 : ψ₀ ≠ 1) {n : ℕ}
    (τ : FDRep ℂ (Gn g n)) (hτ : IsCusp τ.character) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (φ : τ →ₗ[ℂ] V)
    (hφ : ∀ (κ : GL (Fin n) ℤ_[g]) (x : τ),
      φ (τ.ρ (red g n κ) x) = π (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n κ)) (φ x))
    (L : Module.Dual ℂ V) (hL : IsFunctional ψ π L) (x : τ) (d : Fin n → ℤ)
    (h : L (π (Iwasawa.torusPow (w.adicCompletion E) n d) (φ x)) ≠ 0) : ∀ a b, d a = d b := by
  have hcons : ∀ (j : ℕ) (hj : j + 1 < n), d ⟨j, by omega⟩ = d ⟨j + 1, hj⟩ := by
    intro j hj
    rcases lt_trichotomy (d ⟨j, by omega⟩) (d ⟨j + 1, hj⟩) with hlt | heq | hgt
    · exact absurd (step_up i hi hψ h0 τ π φ hφ L hL x d ⟨j, by omega⟩ ⟨j + 1, hj⟩ rfl hlt) h
    · exact heq
    · exact absurd (step_down i hi hψ τ hτ π φ hφ L hL x d ⟨j, by omega⟩ ⟨j + 1, hj⟩ rfl hgt) h
  have hall : ∀ (j : ℕ) (hj : j < n), d ⟨j, hj⟩ = d ⟨0, by omega⟩ := by
    intro j
    induction j with
    | zero => intro hj; rfl
    | succ j ih => intro hj; rw [← hcons j hj, ih (by omega)]
  intro a b
  exact (hall a.val a.isLt).trans (hall b.val b.isLt).symm

end DiscreteGroups.sglob.DzRed
end
end

section
noncomputable section

open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GroundTheory.Automorphic

namespace DiscreteGroups.sglob.DzRed

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem corner_torusPow {m : ℕ} (d : Fin m → ℤ) :
    corner (Iwasawa.torusPow K m d) = Iwasawa.torusPow K (m + 1) (Fin.snoc d 0) := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  induction a using Fin.lastCases <;> induction b using Fin.lastCases
  · rw [corner_last_last]; simp [Iwasawa.torusPow]
  · rw [corner_last_cs]; simp [Iwasawa.torusPow, Matrix.diagonal_apply, (Fin.castSucc_lt_last _).ne']
  · rw [corner_cs_last]; simp [Iwasawa.torusPow, Matrix.diagonal_apply, (Fin.castSucc_lt_last _).ne]
  · rw [corner_cs_cs]; simp [Iwasawa.torusPow, Matrix.diagonal_apply]

theorem longElt_mul_invT_torusPow {n : ℕ} (D : Fin n → ℤ) :
    longElt n K * GlobalTheory.CuspRep.invT n K (Iwasawa.torusPow K n D) =
      Iwasawa.torusPow K n (fun j => -D j.rev) * longElt n K := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [Units.val_mul, Units.val_mul, longElt_mul_apply, mul_longElt_apply, val_invT, ← Iwasawa.torusPow_neg]
  simp only [Matrix.transpose_apply, Iwasawa.torusPow, Iwasawa.coe_diagGL, Matrix.diagonal_apply, Pi.neg_apply]
  by_cases h : b = a.rev
  · subst h; simp
  · have h' : a ≠ b.rev := fun h' => h (by rw [h', Fin.rev_rev])
    simp [h, h']

theorem torusPow_const_comm {n : ℕ} (c : ℤ) (y : GL (Fin n) K) :
    Iwasawa.torusPow K n (fun _ => c) * y = y * Iwasawa.torusPow K n (fun _ => c) := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  simp [Iwasawa.torusPow, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

theorem torusPow_zero' {n : ℕ} : Iwasawa.torusPow K n 0 = 1 := by
  show Iwasawa.diagGL K n (fun _ => _ ^ (0 : ℤ)) = 1
  simp only [zpow_zero]
  exact map_one _

theorem unipotent_le_unipB {n : ℕ} {u : GL (Fin n) K} (hu : u ∈ Iwasawa.unipotent K n) : u ∈ unipB K (Fin n) := by
  rw [Iwasawa.mem_unipotent] at hu
  exact (mem_unipB K).2 ⟨fun i j h => hu.1 h, hu.2⟩

end DiscreteGroups.sglob.DzRed
end
end

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker GroundTheory.Automorphic

namespace DiscreteGroups.sglob.DzRed

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem rep_mul_apply {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    (a b : G) (v : V) : π (a * b) v = π a (π b v) := by
  rw [map_mul]; rfl

theorem rep_one_apply {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    (v : V) : π 1 v = v := by
  rw [map_one]; rfl

theorem superDiag_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} (x : GL (Fin n) R) :
    superDiag (Matrix.GeneralLinearGroup.map f x) = f (superDiag x) := by
  simp only [superDiag, map_sum]
  rfl

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
  {ψ₀ : AddChar (ZMod g) Circle} {ψ : AddChar (w.adicCompletion E) Circle}

include hi in
theorem exists_lift_unipB (hψ : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x)) {n : ℕ}
    {u : Gn g n} (hu : u ∈ unipB (ZMod g) (Fin n)) :
    ∃ κ : GL (Fin n) ℤ_[g], red g n κ = u ∧
      Matrix.GeneralLinearGroup.map i.toRingHom (inc g n κ) ∈ unipB (w.adicCompletion E) (Fin n) ∧
      ψ (superDiag (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n κ))) = ψ₀ (superDiag u) := by
  classical
  have hu' := (mem_unipB (R := ZMod g)).1 hu
  let M : Matrix (Fin n) (Fin n) ℤ_[g] := fun a b => (((u : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℤ_[g])
  have hlow : ∀ a b, b < a → M a b = 0 := fun a b h => by simp only [M, hu'.1 a b h, ZMod.val_zero, Nat.cast_zero]
  have hdiag : ∀ a, M a a = 1 := fun a => by simp only [M, hu'.2 a, ZMod.val_one, Nat.cast_one]
  have hdet : M.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (fun a b h => hlow a b h)]
    simp [hdiag]
  have hU : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (by rw [hdet]; exact isUnit_one)
  let κ : GL (Fin n) ℤ_[g] := hU.unit
  have hκ : (κ : Matrix (Fin n) (Fin n) ℤ_[g]) = M := hU.unit_spec
  have hred : red g n κ = u := by
    refine Units.ext (Matrix.ext fun a b => ?_)
    show PadicInt.toZMod ((κ : Matrix (Fin n) (Fin n) ℤ_[g]) a b) = _
    rw [hκ]
    simp only [M, map_natCast, ZMod.natCast_zmod_val]
  refine ⟨κ, hred, ?_, ?_⟩
  · rw [mem_unipB]
    refine ⟨fun a b h => ?_, fun a => ?_⟩
    · show i (((κ : Matrix (Fin n) (Fin n) ℤ_[g]) a b : ℤ_[g]) : ℚ_[g]) = 0
      rw [hκ, hlow a b h]; simp
    · show i (((κ : Matrix (Fin n) (Fin n) ℤ_[g]) a a : ℤ_[g]) : ℚ_[g]) = 1
      rw [hκ, hdiag]; simp
  · rw [show inc g n κ = Matrix.GeneralLinearGroup.map (algebraMap ℤ_[g] ℚ_[g]) κ from rfl, superDiag_map,
      superDiag_map, ← hred, show red g n κ = Matrix.GeneralLinearGroup.map (PadicInt.toZMod (p := g)) κ from rfl,
      superDiag_map]
    exact hψ _

def cellFun {m : ℕ} {V' : Type} [AddCommGroup V'] [Module ℂ V']
    (ρ₀ : Representation ℂ (GL (Fin m) (w.adicCompletion E)) V') (l' : Module.Dual ℂ V') (v' : V')
    (s : Gn g m → GL (Fin m) ℤ_[g]) (x : Gn g m) : ℂ :=
  l' (ρ₀ (Matrix.GeneralLinearGroup.map i.toRingHom (inc g m (s x))) v')

theorem isLower_one {m : ℕ} : ∀ a b : Fin m, a < b → ((1 : Gn g m) : Mt g m) a b = 0 :=
  fun a b h => by simp [Matrix.one_apply_ne (ne_of_lt h)]

theorem cellFun_eq {m : ℕ} {V' : Type} [AddCommGroup V'] [Module ℂ V']
    (ρ₀ : Representation ℂ (GL (Fin m) (w.adicCompletion E)) V') (l' : Module.Dual ℂ V') (v' : V')
    (hv' : ∀ x : GL (Fin m) ℤ_[g], (∀ a b : Fin m, a < b → (red g m x : Mt g m) a b = 0) →
      ρ₀ (Matrix.GeneralLinearGroup.map i.toRingHom (inc g m x)) v' = v')
    (s : Gn g m → GL (Fin m) ℤ_[g]) (hs : ∀ κ, red g m (s κ) = κ) (κ₁ : GL (Fin m) ℤ_[g]) :
    cellFun i ρ₀ l' v' s (red g m κ₁) = l' (ρ₀ (Matrix.GeneralLinearGroup.map i.toRingHom (inc g m κ₁)) v') := by
  unfold cellFun
  have h1 : red g m ((s (red g m κ₁))⁻¹ * κ₁) = 1 := by rw [map_mul, map_inv, hs, inv_mul_cancel]
  have h2 := hv' ((s (red g m κ₁))⁻¹ * κ₁) (by rw [h1]; exact isLower_one)
  conv_rhs => rw [show κ₁ = s (red g m κ₁) * ((s (red g m κ₁))⁻¹ * κ₁) by group]
  generalize (s (red g m κ₁))⁻¹ * κ₁ = y at h2 ⊢
  rw [map_mul (inc g m), map_mul (Matrix.GeneralLinearGroup.map i.toRingHom), rep_mul_apply, h2]

theorem cellFun_lower {m : ℕ} {V' : Type} [AddCommGroup V'] [Module ℂ V']
    (ρ₀ : Representation ℂ (GL (Fin m) (w.adicCompletion E)) V') (l' : Module.Dual ℂ V') (v' : V')
    (hv' : ∀ x : GL (Fin m) ℤ_[g], (∀ a b : Fin m, a < b → (red g m x : Mt g m) a b = 0) →
      ρ₀ (Matrix.GeneralLinearGroup.map i.toRingHom (inc g m x)) v' = v')
    (s : Gn g m → GL (Fin m) ℤ_[g]) (hs : ∀ κ, red g m (s κ) = κ) (x b : Gn g m)
    (hb : ∀ a c : Fin m, a < c → (b : Mt g m) a c = 0) :
    cellFun i ρ₀ l' v' s (x * b) = cellFun i ρ₀ l' v' s x := by
  rw [show x * b = red g m (s x * s b) by rw [map_mul, hs, hs], cellFun_eq i ρ₀ l' v' hv' s hs,
    map_mul (inc g m), map_mul (Matrix.GeneralLinearGroup.map i.toRingHom), rep_mul_apply, hv' (s b) (by rw [hs]; exact hb)]
  rfl

include hi in
theorem cellFun_unip (hψ : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x)) {m : ℕ} {V' : Type}
    [AddCommGroup V'] [Module ℂ V']
    (ρ₀ : Representation ℂ (GL (Fin m) (w.adicCompletion E)) V') (l' : Module.Dual ℂ V') (v' : V')
    (hl' : IsFunctional ψ⁻¹ ρ₀ l')
    (hv' : ∀ x : GL (Fin m) ℤ_[g], (∀ a b : Fin m, a < b → (red g m x : Mt g m) a b = 0) →
      ρ₀ (Matrix.GeneralLinearGroup.map i.toRingHom (inc g m x)) v' = v')
    (s : Gn g m → GL (Fin m) ℤ_[g]) (hs : ∀ κ, red g m (s κ) = κ) {u : Gn g m} (hu : u ∈ unipB (ZMod g) (Fin m))
    (x : Gn g m) :
    cellFun i ρ₀ l' v' s (u * x) = (((ψ₀ (superDiag u))⁻¹ : Circle) : ℂ) * cellFun i ρ₀ l' v' s x := by
  obtain ⟨κ, hred, hmem, hsd⟩ := exists_lift_unipB i hi hψ hu
  rw [show u * x = red g m (κ * s x) by rw [map_mul, hred, hs], cellFun_eq i ρ₀ l' v' hv' s hs,
    map_mul (inc g m), map_mul (Matrix.GeneralLinearGroup.map i.toRingHom), rep_mul_apply, hl' _ hmem, AddChar.inv_apply', hsd]
  rfl

theorem cellFun_one {m : ℕ} {V' : Type} [AddCommGroup V'] [Module ℂ V']
    (ρ₀ : Representation ℂ (GL (Fin m) (w.adicCompletion E)) V') (l' : Module.Dual ℂ V') (v' : V')
    (hv' : ∀ x : GL (Fin m) ℤ_[g], (∀ a b : Fin m, a < b → (red g m x : Mt g m) a b = 0) →
      ρ₀ (Matrix.GeneralLinearGroup.map i.toRingHom (inc g m x)) v' = v')
    (s : Gn g m → GL (Fin m) ℤ_[g]) (hs : ∀ κ, red g m (s κ) = κ) :
    cellFun i ρ₀ l' v' s 1 = l' v' := by
  have h := cellFun_eq i ρ₀ l' v' hv' s hs 1
  rw [map_one] at h
  rw [h, map_one, map_one, rep_one_apply]

end DiscreteGroups.sglob.DzRed
end
end

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker GroundTheory.Automorphic

namespace DiscreteGroups.sglob.DzRed

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
  {ψ₀ : AddChar (ZMod g) Circle} {ψ : AddChar (w.adicCompletion E) Circle}

include hi in
theorem exists_functional_ne (hψ : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x)) (h0 : ψ₀ ≠ 1) {n : ℕ}
    (τ : FDRep ℂ (Gn g n)) (hτ : IsCusp τ.character) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (hirr : π.IsIrreducible) (φ : τ →ₗ[ℂ] V)
    (hφ : ∀ (κ : GL (Fin n) ℤ_[g]) (x : τ),
      φ (τ.ρ (red g n κ) x) = π (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n κ)) (φ x))
    (hφ0 : φ ≠ 0) (L : Module.Dual ℂ V) (hL : IsFunctional ψ π L) (hL0 : L ≠ 0) :
    ∃ L' : Module.Dual ℂ V, IsFunctional ψ π L' ∧ ∃ x : τ, L' (φ x) ≠ 0 := by
  obtain ⟨h, x, hx⟩ : ∃ (h : GL (Fin n) (w.adicCompletion E)) (x : τ), L (π h (φ x)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    let S : Subrepresentation π :=
      ⟨Submodule.span ℂ (Set.range fun p : GL (Fin n) (w.adicCompletion E) × τ => π p.1 (φ p.2)), by
        intro g0 v hv
        refine Submodule.span_induction (p := fun v _ => π g0 v ∈
            Submodule.span ℂ (Set.range fun p : GL (Fin n) (w.adicCompletion E) × τ => π p.1 (φ p.2)))
          (fun y hy => ?_) (by simp) (fun a b _ _ ha hb => by rw [map_add]; exact Submodule.add_mem _ ha hb)
          (fun c a _ ha => by rw [map_smul]; exact Submodule.smul_mem _ c ha) hv
        obtain ⟨⟨h1, x1⟩, rfl⟩ := hy
        exact Submodule.subset_span ⟨(g0 * h1, x1), by simp only [rep_mul_apply]⟩⟩
    have hS : S ≠ ⊥ := by
      intro hS
      obtain ⟨x0, hx0⟩ : ∃ x0, φ x0 ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hφ0 (LinearMap.ext hc)
      have hmem : φ x0 ∈ S.toSubmodule := Submodule.subset_span ⟨(1, x0), by simp only [rep_one_apply]⟩
      rw [hS] at hmem
      exact hx0 ((Submodule.mem_bot ℂ).1 hmem)
    have hT := (IsSimpleOrder.eq_bot_or_eq_top S).resolve_left hS
    apply hL0
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ S.toSubmodule := by rw [hT]; exact Submodule.mem_top
    have hle : S.toSubmodule ≤ LinearMap.ker L :=
      Submodule.span_le.2 (by rintro _ ⟨⟨h1, x1⟩, rfl⟩; exact hcon h1 x1)
    exact hle hv
  obtain ⟨u, hu, d, k, hk, rfl⟩ := Iwasawa.exists_iwasawa (w.adicCompletion E) n h
  obtain ⟨κ, rfl⟩ := DzLc.exists_inc_eq i hi k hk
  rw [rep_mul_apply, rep_mul_apply, hL _ (unipotent_le_unipB hu)] at hx
  have hx' := right_ne_zero_of_mul hx
  rw [← hφ] at hx'
  have hd := supp_const i hi hψ h0 τ hτ π φ hφ L hL _ d hx'
  have hdc : d = fun _ => (if h : 0 < n then d ⟨0, h⟩ else 0) := by
    funext j
    rw [dif_pos (Fin.pos j)]
    exact hd j _
  rw [hdc] at hx'
  refine ⟨L.comp (π (Iwasawa.torusPow (w.adicCompletion E) n (fun _ => (if h : 0 < n then d ⟨0, h⟩ else 0)))),
    fun u' hu' v => ?_, τ.ρ (red g n κ) x, hx'⟩
  simp only [LinearMap.comp_apply]
  rw [← rep_mul_apply, torusPow_const_comm, rep_mul_apply, hL _ hu']

end DiscreteGroups.sglob.DzRed
end
end

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker GroundTheory.Automorphic
  GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.DzRed

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem psi_cancel (a : Circle) (X Y : ℂ) : (a : ℂ) * X * (((a⁻¹ : Circle) : ℂ) * Y) = X * Y := by
  have h : ((a⁻¹ : Circle) : ℂ) * (a : ℂ) = 1 := by rw [← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
  linear_combination (X * Y) * h

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
  {ψ₀ : AddChar (ZMod g) Circle} {ψ : AddChar (w.adicCompletion E) Circle}

theorem phi_corner {m : ℕ} (κ : GL (Fin m) ℤ_[g]) :
    Matrix.GeneralLinearGroup.map i.toRingHom (inc g (m + 1) (corner κ)) =
      corner (Matrix.GeneralLinearGroup.map i.toRingHom (inc g m κ)) := by
  show Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[g] ℚ_[g]) (corner κ)) = _
  rw [map_corner, map_corner]
  rfl

theorem phi_invT {n : ℕ} (κ : GL (Fin n) ℤ_[g]) :
    Matrix.GeneralLinearGroup.map i.toRingHom (inc g n (GlobalTheory.CuspRep.invT n ℤ_[g] κ)) =
      GlobalTheory.CuspRep.invT n _ (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n κ)) := by
  show Matrix.GeneralLinearGroup.map i.toRingHom
    (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[g] ℚ_[g]) (GlobalTheory.CuspRep.invT n ℤ_[g] κ)) = _
  rw [map_invT, map_invT]
  rfl

theorem phi_longElt (n : ℕ) :
    Matrix.GeneralLinearGroup.map i.toRingHom (inc g n (longElt n ℤ_[g])) = longElt n (w.adicCompletion E) := by
  show Matrix.GeneralLinearGroup.map i.toRingHom
    (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[g] ℚ_[g]) (longElt n ℤ_[g])) = _
  rw [map_longElt, map_longElt]

theorem red_corner {m : ℕ} (κ : GL (Fin m) ℤ_[g]) : red g (m + 1) (corner κ) = corner (red g m κ) :=
  map_corner _ κ

theorem red_invT {n : ℕ} (κ : GL (Fin n) ℤ_[g]) :
    red g n (GlobalTheory.CuspRep.invT n ℤ_[g] κ) = GlobalTheory.CuspRep.invT n _ (red g n κ) :=
  map_invT _ κ

def FR {m : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (π : Representation ℂ (GL (Fin (m + 1)) (w.adicCompletion E)) V)
    (ρ₀ : Representation ℂ (GL (Fin m) (w.adicCompletion E)) V') (L : Module.Dual ℂ V) (l' : Module.Dual ℂ V')
    (y : V) (v' : V') (h : GL (Fin m) (w.adicCompletion E)) : ℂ :=
  L (π (corner h) y) * l' (ρ₀ h v')

def FL {m : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (π : Representation ℂ (GL (Fin (m + 1)) (w.adicCompletion E)) V)
    (ρ₀ : Representation ℂ (GL (Fin m) (w.adicCompletion E)) V') (L : Module.Dual ℂ V) (l' : Module.Dual ℂ V')
    (y : V) (v' : V') (h : GL (Fin m) (w.adicCompletion E)) : ℂ :=
  L (π (tilde (corner h)) y) * l' (ρ₀ (tilde h) v')

section Inv

variable {m : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (π : Representation ℂ (GL (Fin (m + 1)) (w.adicCompletion E)) V)
    (ρ₀ : Representation ℂ (GL (Fin m) (w.adicCompletion E)) V') (L : Module.Dual ℂ V) (l' : Module.Dual ℂ V')

theorem FR_left (hL : IsFunctional ψ π L) (hl' : IsFunctional ψ⁻¹ ρ₀ l') (y : V) (v' : V')
    {u : GL (Fin m) (w.adicCompletion E)} (hu : u ∈ unipB (w.adicCompletion E) (Fin m)) (h : GL (Fin m) (w.adicCompletion E)) :
    FR π ρ₀ L l' y v' (u * h) = FR π ρ₀ L l' y v' h := by
  unfold FR
  rw [corner_mul, rep_mul_apply, hL _ (corner_mem hu), superDiag_corner, rep_mul_apply, hl' _ hu, AddChar.inv_apply']
  exact psi_cancel _ _ _

theorem FL_left (hL : IsFunctional ψ π L) (hl' : IsFunctional ψ⁻¹ ρ₀ l') (y : V) (v' : V')
    {u : GL (Fin m) (w.adicCompletion E)} (hu : u ∈ unipB (w.adicCompletion E) (Fin m)) (h : GL (Fin m) (w.adicCompletion E)) :
    FL π ρ₀ L l' y v' (u * h) = FL π ρ₀ L l' y v' h := by
  obtain ⟨u₁, hu₁, u₂, hu₂, e1, e2, e3⟩ := tilde_corner_unip hu h
  unfold FL
  rw [e1, e2, rep_mul_apply, rep_mul_apply, hL _ hu₁, hl' _ hu₂, e3, AddChar.inv_apply']
  exact psi_cancel _ _ _

end Inv

end DiscreteGroups.sglob.DzRed
end
end

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker GroundTheory.Automorphic
  GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.DzRed

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
  {ψ₀ : AddChar (ZMod g) Circle} {ψ : AddChar (w.adicCompletion E) Circle}

section Inv

variable {m : ℕ} (τ : FDRep ℂ (Gn g (m + 1))) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V']
    [Module ℂ V'] (π : Representation ℂ (GL (Fin (m + 1)) (w.adicCompletion E)) V)
    (ρ₀ : Representation ℂ (GL (Fin m) (w.adicCompletion E)) V') (L : Module.Dual ℂ V) (l' : Module.Dual ℂ V')
    (φ : τ →ₗ[ℂ] V)

include hi in
theorem FR_right
    (hφ : ∀ (κ : GL (Fin (m + 1)) ℤ_[g]) (x : τ),
      φ (τ.ρ (red g (m + 1) κ) x) = π (Matrix.GeneralLinearGroup.map i.toRingHom (inc g (m + 1) κ)) (φ x))
    (v' : V') (hv' : ∀ x : GL (Fin m) ℤ_[g], (∀ a b : Fin m, a < b → (red g m x : Mt g m) a b = 0) →
      ρ₀ (Matrix.GeneralLinearGroup.map i.toRingHom (inc g m x)) v' = v')
    (x : τ) (h : GL (Fin m) (w.adicCompletion E)) {k : GL (Fin m) (w.adicCompletion E)}
    (hk : k ∈ KOne (w.adicCompletion E) (Fin m)) :
    FR π ρ₀ L l' (φ x) v' (h * k) = FR π ρ₀ L l' (φ x) v' h := by
  obtain ⟨κ, h1, rfl⟩ := DzIso.exists_of_mem_KOne i hi hk
  unfold FR
  rw [corner_mul, rep_mul_apply, rep_mul_apply ρ₀, hv' κ (by rw [h1]; exact isLower_one), ← phi_corner, ← hφ,
    red_corner, h1, corner_one, rep_one_apply]

include hi in
theorem FL_right
    (hφ : ∀ (κ : GL (Fin (m + 1)) ℤ_[g]) (x : τ),
      φ (τ.ρ (red g (m + 1) κ) x) = π (Matrix.GeneralLinearGroup.map i.toRingHom (inc g (m + 1) κ)) (φ x))
    (v' : V') (hv' : ∀ x : GL (Fin m) ℤ_[g], (∀ a b : Fin m, a < b → (red g m x : Mt g m) a b = 0) →
      ρ₀ (Matrix.GeneralLinearGroup.map i.toRingHom (inc g m x)) v' = v')
    (x : τ) (h : GL (Fin m) (w.adicCompletion E)) {k : GL (Fin m) (w.adicCompletion E)}
    (hk : k ∈ KOne (w.adicCompletion E) (Fin m)) :
    FL π ρ₀ L l' (φ x) v' (h * k) = FL π ρ₀ L l' (φ x) v' h := by
  obtain ⟨κ, h1, rfl⟩ := DzIso.exists_of_mem_KOne i hi hk
  unfold FL
  rw [corner_mul, tilde_mul, tilde_mul, rep_mul_apply, rep_mul_apply ρ₀, ← phi_invT,
    hv' _ (by rw [red_invT, h1, map_one]; exact isLower_one), ← phi_corner, ← phi_invT, ← hφ,
    red_invT, red_corner, h1, corner_one, map_one, rep_one_apply]

include hi in
theorem FR_supp (hψ : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x)) (h0 : ψ₀ ≠ 1)
    (hτ : IsCusp τ.character)
    (hφ : ∀ (κ : GL (Fin (m + 1)) ℤ_[g]) (x : τ),
      φ (τ.ρ (red g (m + 1) κ) x) = π (Matrix.GeneralLinearGroup.map i.toRingHom (inc g (m + 1) κ)) (φ x))
    (hL : IsFunctional ψ π L) (hl' : IsFunctional ψ⁻¹ ρ₀ l') (v' : V') (x : τ) (h : GL (Fin m) (w.adicCompletion E))
    (hne : FR π ρ₀ L l' (φ x) v' h ≠ 0) :
    ∃ u ∈ unipB (w.adicCompletion E) (Fin m), ∃ k ∈ KO (w.adicCompletion E) (Fin m), h = u * k := by
  obtain ⟨u, hu, d, k, hk, rfl⟩ := Iwasawa.exists_iwasawa (w.adicCompletion E) m h
  obtain ⟨κ, rfl⟩ := DzLc.exists_inc_eq i hi k hk
  rw [mul_assoc, FR_left π ρ₀ L l' hL hl' _ _ (unipotent_le_unipB hu)] at hne
  unfold FR at hne
  have hne' := left_ne_zero_of_mul hne
  rw [corner_mul, rep_mul_apply, ← phi_corner, ← hφ, corner_torusPow] at hne'
  have hd := supp_const i hi hψ h0 τ hτ π φ hφ L hL _ _ hne'
  have hd0 : d = 0 := funext fun j => by simpa using hd j.castSucc (Fin.last m)
  refine ⟨u, unipotent_le_unipB hu, _, DzIso.map_inc_mem_KO i hi κ, ?_⟩
  rw [hd0, torusPow_zero', mul_one]

include hi in
theorem FL_supp (hψ : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x)) (h0 : ψ₀ ≠ 1)
    (hτ : IsCusp τ.character)
    (hφ : ∀ (κ : GL (Fin (m + 1)) ℤ_[g]) (x : τ),
      φ (τ.ρ (red g (m + 1) κ) x) = π (Matrix.GeneralLinearGroup.map i.toRingHom (inc g (m + 1) κ)) (φ x))
    (hL : IsFunctional ψ π L) (hl' : IsFunctional ψ⁻¹ ρ₀ l') (v' : V') (x : τ) (h : GL (Fin m) (w.adicCompletion E))
    (hne : FL π ρ₀ L l' (φ x) v' h ≠ 0) :
    ∃ u ∈ unipB (w.adicCompletion E) (Fin m), ∃ k ∈ KO (w.adicCompletion E) (Fin m), h = u * k := by
  obtain ⟨u, hu, d, k, hk, rfl⟩ := Iwasawa.exists_iwasawa (w.adicCompletion E) m h
  obtain ⟨κ, rfl⟩ := DzLc.exists_inc_eq i hi k hk
  rw [mul_assoc, FL_left π ρ₀ L l' hL hl' _ _ (unipotent_le_unipB hu)] at hne
  unfold FL at hne
  have hne' := left_ne_zero_of_mul hne
  rw [corner_mul, tilde_mul,
    show tilde (corner (Iwasawa.torusPow (w.adicCompletion E) m d)) =
      longElt (m + 1) _ * GlobalTheory.CuspRep.invT (m + 1) _ (corner (Iwasawa.torusPow (w.adicCompletion E) m d)) from rfl,
    corner_torusPow, longElt_mul_invT_torusPow, mul_assoc, rep_mul_apply, ← phi_corner, ← phi_invT,
    ← phi_longElt (g := g) i (m + 1), ← map_mul (Matrix.GeneralLinearGroup.map i.toRingHom), ← map_mul (inc g (m + 1)), ← hφ] at hne'
  have hd := supp_const i hi hψ h0 τ hτ π φ hφ L hL _ _ hne'
  have hd0 : d = 0 := funext fun j => by simpa using hd (j.castSucc).rev (Fin.last m).rev
  refine ⟨u, unipotent_le_unipB hu, _, DzIso.map_inc_mem_KO i hi κ, ?_⟩
  rw [hd0, torusPow_zero', mul_one]

end Inv

end DiscreteGroups.sglob.DzRed
end
end

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocLanglands
open scoped Pointwise

namespace DiscreteGroups.sglob.DzRed

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

local notation "NK₁[" k ", " m "]" =>
  ((unipB k (Fin m) : Set (GL (Fin m) k)) * (KOne k (Fin m) : Set (GL (Fin m) k)))

section Ring

variable {m : ℕ}

theorem unipB_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {x : GL (Fin m) R}
    (hx : x ∈ unipB R (Fin m)) : Matrix.GeneralLinearGroup.map f x ∈ unipB S (Fin m) := by
  rw [mem_unipB] at hx ⊢
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · show f ((x : Matrix (Fin m) (Fin m) R) a b) = 0
    rw [hx.1 a b hab, map_zero]
  · show f ((x : Matrix (Fin m) (Fin m) R) a a) = 1
    rw [hx.2 a, map_one]

theorem unipB_of_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f)
    {x : GL (Fin m) R} (hx : Matrix.GeneralLinearGroup.map f x ∈ unipB S (Fin m)) : x ∈ unipB R (Fin m) := by
  rw [mem_unipB] at hx ⊢
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · have h0 : f ((x : Matrix (Fin m) (Fin m) R) a b) = 0 := hx.1 a b hab
    exact (map_eq_zero_iff f hf).1 h0
  · have h1 : f ((x : Matrix (Fin m) (Fin m) R) a a) = f 1 := by rw [map_one]; exact hx.2 a
    exact hf h1

end Ring

section Gen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

theorem mem_unipotentKOne_mul_left {u x : GL (Fin m) k} (hu : u ∈ unipB k (Fin m)) :
    u * x ∈ NK₁[k, m] ↔ x ∈ NK₁[k, m] := by
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, e⟩ := Set.mem_mul.1 h
    refine Set.mem_mul.2 ⟨u⁻¹ * a, (unipB k (Fin m)).mul_mem ((unipB k (Fin m)).inv_mem hu) ha, b, hb, ?_⟩
    rw [mul_assoc, e, inv_mul_cancel_left]
  · intro h
    obtain ⟨a, ha, b, hb, e⟩ := Set.mem_mul.1 h
    refine Set.mem_mul.2 ⟨u * a, (unipB k (Fin m)).mul_mem hu ha, b, hb, ?_⟩
    rw [mul_assoc, e]

theorem isOpen_unipotentKOne : IsOpen NK₁[k, m] :=
  (GlobalTheory.StepData.isOpen_KOne (k := k) (n := Fin m)).mul_left

theorem isClosed_unipotentKOne : IsClosed NK₁[k, m] := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  rw [Set.mem_compl_iff] at hx
  have hU : IsOpen ((fun y : GL (Fin m) k => x⁻¹ * y) ⁻¹' (KOne k (Fin m) : Set (GL (Fin m) k))) :=
    (GlobalTheory.StepData.isOpen_KOne (k := k) (n := Fin m)).preimage (continuous_const.mul continuous_id)
  have hx1 : x ∈ (fun y : GL (Fin m) k => x⁻¹ * y) ⁻¹' (KOne k (Fin m) : Set (GL (Fin m) k)) := by
    show x⁻¹ * x ∈ KOne k (Fin m)
    rw [inv_mul_cancel]
    exact (KOne k (Fin m)).one_mem
  refine Filter.mem_of_superset (hU.mem_nhds hx1) ?_
  intro y hy
  rw [Set.mem_compl_iff]
  intro hyS
  have hy' : x⁻¹ * y ∈ KOne k (Fin m) := hy
  obtain ⟨a, ha, b, hb, e⟩ := Set.mem_mul.1 hyS
  apply hx
  refine Set.mem_mul.2 ⟨a, ha, b * (x⁻¹ * y)⁻¹, (KOne k (Fin m)).mul_mem hb ((KOne k (Fin m)).inv_mem hy'), ?_⟩
  rw [← mul_assoc, e, mul_inv_rev, inv_inv, mul_inv_cancel_left]

theorem isLocallyConstant_indicator_one {X : Type*} [TopologicalSpace X] {U : Set X} (hU : IsOpen U)
    (hU' : IsClosed U) : IsLocallyConstant (U.indicator (1 : X → ℂ)) := by
  intro s
  change IsOpen (U.indicator (fun _ => (1 : ℂ)) ⁻¹' s)
  have h := Set.indicator_const_preimage U s (1 : ℂ)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h <;> rw [h]
  · exact isOpen_univ
  · exact hU
  · exact hU'.isOpen_compl
  · exact isOpen_empty

theorem isTestFun_indicator_unipotentKOne : IsTestFun (Set.indicator NK₁[k, m] (1 : GL (Fin m) k → ℂ)) := by
  classical
  refine ⟨fun u hu x => ?_, isLocallyConstant_indicator_one isOpen_unipotentKOne isClosed_unipotentKOne,
    (KO k (Fin m) : Set (GL (Fin m) k)), GlobalTheory.SplitFlip.isCompact_KO, fun x hx => ?_⟩
  · simp only [Set.indicator_apply, mem_unipotentKOne_mul_left hu, Pi.one_apply]
  · obtain ⟨a, ha, b, hb, e⟩ := Set.mem_mul.1 (Set.mem_of_indicator_ne_zero hx)
    exact ⟨a, ha, b, GlobalTheory.StepData.KOne_le_KO hb, e.symm⟩

end Gen

section Loc

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]

theorem exists_unip_lift {m : ℕ} {u : Gn g m} (hu : u ∈ unipB (ZMod g) (Fin m)) :
    ∃ v : GL (Fin m) ℤ_[g], v ∈ unipB ℤ_[g] (Fin m) ∧ red g m v = u := by
  classical
  rw [mem_unipB] at hu
  let M : Matrix (Fin m) (Fin m) ℤ_[g] := fun a b =>
    if b < a then 0 else if a = b then 1 else (ZMod.cast ((u : Matrix (Fin m) (Fin m) (ZMod g)) a b) : ℤ_[g])
  have hM : M.BlockTriangular id := fun a b hab => by
    have hab' : b < a := hab
    simp only [M]; rw [if_pos hab']
  have hdiag : ∀ a, M a a = 1 := fun a => by simp [M]
  have hd : IsUnit M.det := by
    rw [Matrix.det_of_isUpperTriangular hM]
    simp [hdiag]
  obtain ⟨v, hv⟩ := (Matrix.isUnit_iff_isUnit_det M).2 hd
  refine ⟨v, ?_, ?_⟩
  · rw [mem_unipB, hv]
    exact ⟨fun a b hab => by simp only [M]; rw [if_pos hab], hdiag⟩
  · refine Units.ext (Matrix.ext fun a b => ?_)
    show PadicInt.toZMod ((v : Matrix (Fin m) (Fin m) ℤ_[g]) a b) = (u : Matrix (Fin m) (Fin m) (ZMod g)) a b
    rw [hv]
    simp only [M]
    split_ifs with h1 h2
    · rw [map_zero, hu.1 a b h1]
    · rw [← h2, map_one, hu.2 a]
    · exact ZMod.ringHom_map_cast _ _

theorem card_filter_unip {m : ℕ} (c : Gn g m)
    [DecidablePred fun κ : Gn g m => c * κ⁻¹ ∈ unipB (ZMod g) (Fin m)] :
    (Finset.univ.filter fun κ : Gn g m => c * κ⁻¹ ∈ unipB (ZMod g) (Fin m)).card =
      Nat.card (unipB (ZMod g) (Fin m)) := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr
    { toFun := fun κ => ⟨c * (κ : Gn g m)⁻¹, κ.2⟩
      invFun := fun v => ⟨(v : Gn g m)⁻¹ * c, by rw [mul_inv_rev, inv_inv, mul_inv_cancel_left]; exact v.2⟩
      left_inv := fun κ => Subtype.ext (by simp only [mul_inv_rev, inv_inv, inv_mul_cancel_right])
      right_inv := fun v => Subtype.ext (by simp only [mul_inv_rev, inv_inv, mul_inv_cancel_left]) }

variable (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

def phi (m : ℕ) : GL (Fin m) ℤ_[g] →* GL (Fin m) (w.adicCompletion E) :=
  (Matrix.GeneralLinearGroup.map i.toRingHom).comp (inc g m)

theorem phi_apply {m : ℕ} (b : GL (Fin m) ℤ_[g]) :
    phi i m b = Matrix.GeneralLinearGroup.map i.toRingHom (inc g m b) := rfl

include hi

theorem mem_unipotentKOne_iff {m : ℕ} (b : GL (Fin m) ℤ_[g]) :
    phi i m b ∈ NK₁[w.adicCompletion E, m] ↔ red g m b ∈ unipB (ZMod g) (Fin m) := by
  constructor
  · intro h
    obtain ⟨a, ha, c, hc, e⟩ := Set.mem_mul.1 h
    obtain ⟨d, hd, rfl⟩ := DzIso.exists_of_mem_KOne i hi hc
    have e' : a * phi i m d = phi i m b := e
    have ha' : phi i m (b * d⁻¹) = a := by rw [map_mul, map_inv, ← e', mul_inv_cancel_right]
    have h1 : phi i m (b * d⁻¹) ∈ unipB (w.adicCompletion E) (Fin m) := by rw [ha']; exact ha
    have h2 : inc g m (b * d⁻¹) ∈ unipB ℚ_[g] (Fin m) :=
      unipB_of_map (x := inc g m (b * d⁻¹)) i.toRingHom i.injective h1
    have h3 : b * d⁻¹ ∈ unipB ℤ_[g] (Fin m) :=
      unipB_of_map (algebraMap ℤ_[g] ℚ_[g]) (fun x y hxy => PadicInt.ext hxy) h2
    have h4 : red g m (b * d⁻¹) ∈ unipB (ZMod g) (Fin m) := unipB_map (PadicInt.toZMod (p := g)) h3
    rwa [map_mul, map_inv, hd, inv_one, mul_one] at h4
  · intro h
    obtain ⟨v, hv, hvr⟩ := exists_unip_lift h
    have h1 : red g m (v⁻¹ * b) = 1 := by rw [map_mul, map_inv, hvr, inv_mul_cancel]
    refine Set.mem_mul.2 ⟨phi i m v, unipB_map i.toRingHom (unipB_map (algebraMap ℤ_[g] ℚ_[g]) hv),
      phi i m (v⁻¹ * b), DzIso.map_mem_KOne i hi _ h1, ?_⟩
    rw [← map_mul (phi i m), mul_inv_cancel_left]

theorem eq_of_red {m : ℕ} (F : GL (Fin m) (w.adicCompletion E) → ℂ)
    (h2 : ∀ x, ∀ k ∈ KOne (w.adicCompletion E) (Fin m), F (x * k) = F x) {a b : GL (Fin m) ℤ_[g]}
    (hab : red g m a = red g m b) : F (phi i m a) = F (phi i m b) := by
  have h0 : red g m (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
  have hk : phi i m (a⁻¹ * b) ∈ KOne (w.adicCompletion E) (Fin m) := DzIso.map_mem_KOne i hi _ h0
  rw [← h2 (phi i m a) _ hk, ← map_mul (phi i m), mul_inv_cancel_left]

theorem integral_eq {m : ℕ}
    (I : (GL (Fin m) (w.adicCompletion E) → ℂ) →ₗ[ℂ] ℂ) (hI : IsInvIntegral I) (F : GL (Fin m) (w.adicCompletion E) → ℂ)
    (h1 : ∀ u ∈ unipB (w.adicCompletion E) (Fin m), ∀ x, F (u * x) = F x)
    (h2 : ∀ x, ∀ k ∈ KOne (w.adicCompletion E) (Fin m), F (x * k) = F x)
    (h3 : ∀ x, F x ≠ 0 → ∃ u ∈ unipB (w.adicCompletion E) (Fin m), ∃ k ∈ KO (w.adicCompletion E) (Fin m), x = u * k)
    (s : Gn g m → GL (Fin m) ℤ_[g]) (hs : ∀ κ, GlobalTheory.GLp.red g m (s κ) = κ) :
    (Nat.card (unipB (ZMod g) (Fin m)) : ℂ) * I F =
      I (Set.indicator ((unipB (w.adicCompletion E) (Fin m) : Set _) * (KOne (w.adicCompletion E) (Fin m) : Set _)) 1) *
        ∑ κ : Gn g m, F (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g m (s κ))) := by
  classical
  simp only [← phi_apply i]
  have hT := isTestFun_indicator_unipotentKOne (k := w.adicCompletion E) (m := m)
  have key : ∀ y, (Nat.card (unipB (ZMod g) (Fin m)) : ℂ) * F y =
      ∑ κ : Gn g m, F (phi i m (s κ)) * Set.indicator NK₁[w.adicCompletion E, m] 1 (y * (phi i m (s κ))⁻¹) := by
    intro y
    by_cases hmem : ∃ u ∈ unipB (w.adicCompletion E) (Fin m), ∃ c ∈ KO (w.adicCompletion E) (Fin m), y = u * c
    · obtain ⟨u, hu, c, hc, rfl⟩ := hmem
      obtain ⟨a, rfl⟩ := DzIso.exists_of_mem_KO i hi hc
      rw [← phi_apply i a]
      have hterm : ∀ κ : Gn g m, F (phi i m (s κ)) *
          Set.indicator NK₁[w.adicCompletion E, m] 1 (u * phi i m a * (phi i m (s κ))⁻¹) =
          if red g m a * κ⁻¹ ∈ unipB (ZMod g) (Fin m) then F (phi i m a) else 0 := by
        intro κ
        have e : u * phi i m a * (phi i m (s κ))⁻¹ = u * phi i m (a * (s κ)⁻¹) := by
          rw [mul_assoc, map_mul, map_inv]
        have hr : red g m (a * (s κ)⁻¹) = red g m a * κ⁻¹ := by rw [map_mul, map_inv, hs]
        rw [e]
        simp only [Set.indicator_apply, mem_unipotentKOne_mul_left hu, mem_unipotentKOne_iff i hi, hr, Pi.one_apply]
        split_ifs with hU
        · rw [mul_one]
          obtain ⟨v, hv, hvr⟩ := exists_unip_lift hU
          have hvN : phi i m v ∈ unipB (w.adicCompletion E) (Fin m) :=
            unipB_map i.toRingHom (unipB_map (algebraMap ℤ_[g] ℚ_[g]) hv)
          rw [← h1 _ hvN, ← map_mul (phi i m)]
          apply eq_of_red i hi F h2
          rw [map_mul, hvr, hs, inv_mul_cancel_right]
        · rw [mul_zero]
      rw [h1 u hu, Finset.sum_congr rfl fun κ _ => hterm κ, Finset.sum_ite, Finset.sum_const_zero, add_zero,
        Finset.sum_const, card_filter_unip, nsmul_eq_mul]
    · have hFy : F y = 0 := by
        by_contra hne
        exact hmem (h3 y hne)
      rw [hFy, mul_zero]
      refine (Finset.sum_eq_zero fun κ _ => ?_).symm
      have hn : y * (phi i m (s κ))⁻¹ ∉ NK₁[w.adicCompletion E, m] := by
        intro hS
        obtain ⟨a, ha, b, hb, e⟩ := Set.mem_mul.1 hS
        exact hmem ⟨a, ha, b * phi i m (s κ),
          (KO (w.adicCompletion E) (Fin m)).mul_mem (GlobalTheory.StepData.KOne_le_KO hb) (DzIso.map_inc_mem_KO i hi _),
          by rw [← mul_assoc, e, inv_mul_cancel_right]⟩
      rw [Set.indicator_apply, if_neg hn, mul_zero]
  have e2 : (fun y => (Nat.card (unipB (ZMod g) (Fin m)) : ℂ) * F y) =
      ∑ κ : Gn g m, F (phi i m (s κ)) •
        (fun y => Set.indicator NK₁[w.adicCompletion E, m] 1 (y * (phi i m (s κ))⁻¹)) := by
    funext y
    rw [key y, Finset.sum_apply]
    rfl
  have e1 : I (fun y => (Nat.card (unipB (ZMod g) (Fin m)) : ℂ) * F y) =
      (Nat.card (unipB (ZMod g) (Fin m)) : ℂ) * I F := by
    have : (fun y => (Nat.card (unipB (ZMod g) (Fin m)) : ℂ) * F y) = (Nat.card (unipB (ZMod g) (Fin m)) : ℂ) • F := rfl
    rw [this, map_smul, smul_eq_mul]
  rw [← e1, congrArg I e2, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [map_smul, smul_eq_mul, hI _ hT, mul_comm]

end Loc

end DiscreteGroups.sglob.DzRed
end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker
open scoped Pointwise

namespace DiscreteGroups.sglob.DzRed

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E)

theorem phi_tilde {n : ℕ} (κ : GL (Fin n) ℤ_[g]) :
    Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n (tilde κ)) =
      tilde (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n κ)) := by
  show Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[g] ℚ_[g]) (tilde κ)) = _
  rw [map_tilde, map_tilde]
  rfl

theorem red_tilde {n : ℕ} (κ : GL (Fin n) ℤ_[g]) : GlobalTheory.GLp.red g n (tilde κ) = tilde (GlobalTheory.GLp.red g n κ) :=
  map_tilde _ κ

end DiscreteGroups.sglob.DzRed

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem lRed : LRed := by
  intro hCG E _ _ w g _ i hi ψ₀ hψ₀ ψ hψc hψ m τ hτ σ hσ hinf τ₀ ω hω hcell e he
  obtain ⟨φ, hφ0, hφ⟩ := hinf
  have hφ' : ∀ (κ : GL (Fin (m + 1)) ℤ_[g]) (x : τ), φ (τ.ρ (GlobalTheory.GLp.red g (m + 1) κ) x) =
      σ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g (m + 1) κ)) (φ x) := hφ
  have hψ' : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x) := hψ
  obtain ⟨x0, hx0⟩ := DzRed.exists_psi_ne_one i hψ' hψ₀
  have hψ1 : ψ ≠ 1 := fun h => hx0 (by rw [h, AddChar.one_apply])
  have hnt : Nontrivial σ.V := by
    obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hφ0 (LinearMap.ext hc)
    exact ⟨⟨φ x, 0, hx⟩⟩
  obtain ⟨L, hL0, hL⟩ := hCG (w.adicCompletion E) ψ hψc hψ1 (m + 1) σ.V σ.ρ hnt hσ
  obtain ⟨L', hL', x1, hx1⟩ := DzRed.exists_functional_ne i hi hψ' hψ₀ τ hτ σ.ρ σ.irr φ hφ' hφ0 L hL hL0
  obtain ⟨l', v', hl', hlv', hv'⟩ := hcell
  choose s hs using GlobalTheory.GLp.Model.red_surjective (g := g) m
  obtain ⟨I, hI, -, hpos⟩ := LConv.exists_pos_isInvIntegral (w.adicCompletion E) m
  refine ⟨L'.comp φ, DzRed.cellFun i τ₀.ρ l' v' s, ?_, ?_, ?_, ?_⟩
  · intro u hu x
    obtain ⟨κ, hred, hmem, hsd⟩ := DzRed.exists_lift_unipB i hi hψ' hu
    simp only [LinearMap.comp_apply]
    conv_lhs => rw [← hred]
    rw [hφ', hL' _ hmem, hsd]
  · intro h
    exact hx1 (LinearMap.congr_fun h x1)
  · refine ⟨fun u hu x => DzRed.cellFun_unip i hi hψ' τ₀.ρ l' v' hl' hv' s hs hu x,
      fun b hb x => DzRed.cellFun_lower i τ₀.ρ l' v' hv' s hs x b hb, ?_⟩
    rw [DzRed.cellFun_one i τ₀.ρ l' v' hv' s hs]
    exact hlv'
  · classical
    intro v
    have hPE : I (DzRed.FL σ.ρ τ₀.ρ L' l' (φ v) v') =
        (ω (-1) : ℂ) ^ m * e * I (DzRed.FR σ.ρ τ₀.ρ L' l' (φ v) v') :=
      he ω hω L' l' hL' hl' I hI (φ v) v'
    have intL := DzRed.integral_eq i hi I hI (DzRed.FL σ.ρ τ₀.ρ L' l' (φ v) v')
      (fun u hu x => DzRed.FL_left σ.ρ τ₀.ρ L' l' hL' hl' _ _ hu x)
      (fun x k hk => DzRed.FL_right i hi τ σ.ρ τ₀.ρ L' l' φ hφ' v' hv' v x hk)
      (fun x hx => DzRed.FL_supp i hi τ σ.ρ τ₀.ρ L' l' φ hψ' hψ₀ hτ hφ' hL' hl' v' v x hx) s hs
    have intR := DzRed.integral_eq i hi I hI (DzRed.FR σ.ρ τ₀.ρ L' l' (φ v) v')
      (fun u hu x => DzRed.FR_left σ.ρ τ₀.ρ L' l' hL' hl' _ _ hu x)
      (fun x k hk => DzRed.FR_right i hi τ σ.ρ τ₀.ρ L' l' φ hφ' v' hv' v x hk)
      (fun x hx => DzRed.FR_supp i hi τ σ.ρ τ₀.ρ L' l' φ hψ' hψ₀ hτ hφ' hL' hl' v' v x hx) s hs
    have tL : ∀ κ : Gn g m, DzRed.FL σ.ρ τ₀.ρ L' l' (φ v) v'
        (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g m (s κ))) =
        (L'.comp φ) (τ.ρ (tilde (corner κ)) v) * DzRed.cellFun i τ₀.ρ l' v' s (tilde κ) := by
      intro κ
      unfold DzRed.FL
      rw [← DzRed.phi_corner, ← DzRed.phi_tilde, ← hφ', ← DzRed.phi_tilde, DzRed.red_tilde, DzRed.red_corner, hs,
        ← DzRed.cellFun_eq i τ₀.ρ l' v' hv' s hs, DzRed.red_tilde, hs]
      rfl
    have tR : ∀ κ : Gn g m, DzRed.FR σ.ρ τ₀.ρ L' l' (φ v) v'
        (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g m (s κ))) =
        (L'.comp φ) (τ.ρ (corner κ) v) * DzRed.cellFun i τ₀.ρ l' v' s κ := by
      intro κ
      unfold DzRed.FR
      rw [← DzRed.phi_corner, ← hφ', DzRed.red_corner, hs]
      rfl
    simp only [tL, tR] at intL intR
    have hT := DzRed.isTestFun_indicator_unipotentKOne (k := w.adicCompletion E) (m := m)
    have hI1 : I (Set.indicator ((unipB (w.adicCompletion E) (Fin m) : Set _) *
        (KOne (w.adicCompletion E) (Fin m) : Set _)) 1) ≠ 0 := by
      intro h0
      have h1mem : (1 : GL (Fin m) (w.adicCompletion E)) ∈
          ((unipB (w.adicCompletion E) (Fin m) : Set (GL (Fin m) (w.adicCompletion E))) *
          (KOne (w.adicCompletion E) (Fin m) : Set (GL (Fin m) (w.adicCompletion E)))) :=
        Set.mem_mul.2 ⟨1, one_mem _, 1, one_mem _, one_mul 1⟩
      have := (hpos _ hT (fun x => by rw [Set.indicator_apply]; split_ifs <;> simp)).2 (by rw [h0]; simp) 1
      rw [Set.indicator_of_mem h1mem] at this
      simp at this
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    refine mul_left_cancel₀ hI1 ?_
    rw [← intL, hPE, mul_left_comm, intR]
    ring

end DiscreteGroups.sglob.DzType
end
end
