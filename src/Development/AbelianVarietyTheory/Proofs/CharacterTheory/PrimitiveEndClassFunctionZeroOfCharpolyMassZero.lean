import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.AdditiveEqPolynomialVonMangoldtConvolutionOne
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ConjOfPrimaryFinrankKerPowEq
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyLinearEqui
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.AdditiveEqPolynomialVonMangoldtConvolutionOneStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ConjOfPrimaryFinrankKerPowEqStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EndomorphismMassMobiusInverseMonicEqStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EqZeroOfNotPrimaryStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyBlockAndInvariantUnderStabilizerNilradicStatement
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement

section
section
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

theorem pow_add_nilRad {A : Submodule F V} {g h : Module.End F V} (hg : ∀ x ∈ A, g x ∈ A)
    (hh : h ∈ nilRad A) (n : ℕ) :
    (∀ x ∈ A, ((g + h) ^ n) x = (g ^ n) x ∧ (g ^ n) x ∈ A) ∧ ∀ x, ((g + h) ^ n) x - (g ^ n) x ∈ A := by
  induction n with
  | zero => exact ⟨fun x hx => ⟨by simp, by simpa using hx⟩, fun x => by simp⟩
  | succ n ih =>
    refine ⟨fun x hx => ?_, fun x => ?_⟩
    · obtain ⟨h1, h2⟩ := ih.1 x hx
      simp only [pow_succ', Module.End.mul_apply, LinearMap.add_apply, h1, hh.2 _ h2, add_zero, true_and]
      exact hg _ h2
    · have h1 := hg _ (ih.2 x)
      have h2 := hh.1 (((g + h) ^ n) x)
      have := A.add_mem h1 h2
      simp only [pow_succ', Module.End.mul_apply, LinearMap.add_apply]
      rw [map_sub] at this
      convert this using 1
      abel

theorem aeval_add_nilRad {A : Submodule F V} {g h : Module.End F V} (hg : ∀ x ∈ A, g x ∈ A)
    (hh : h ∈ nilRad A) (p : F[X]) :
    (∀ x ∈ A, aeval (g + h) p x = aeval g p x) ∧ ∀ x, aeval (g + h) p x - aeval g p x ∈ A := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    refine ⟨fun x hx => ?_, fun x => ?_⟩
    · simp only [map_add, LinearMap.add_apply, hp.1 x hx, hq.1 x hx]
    · have := A.add_mem (hp.2 x) (hq.2 x)
      simp only [map_add, LinearMap.add_apply]
      convert this using 1
      abel
  | monomial n a =>
    have H := pow_add_nilRad hg hh n
    refine ⟨fun x hx => ?_, fun x => ?_⟩
    · simp only [aeval_monomial, Module.End.mul_apply, (H.1 x hx).1]
    · simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, ← smul_sub]
      exact A.smul_mem _ (H.2 x)

theorem ker_aeval_add_nilRad :
    ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g h : Module.End F V) (f : F[X]), h ∈ nilRad (LinearMap.ker (aeval g f)) → LinearMap.ker (aeval g f) ≤ LinearMap.ker (aeval (g + h) f) ∧ (LinearMap.ker (aeval (g + h) f) = LinearMap.ker (aeval g f) → ∀ j : ℕ, Module.finrank F (LinearMap.ker (aeval g (f ^ j))) = Module.finrank F (LinearMap.ker (aeval (g + h) (f ^ j)))) := by
  intro F _ V _ _ _ g h f hh
  have hg : ∀ x ∈ LinearMap.ker (aeval g f), g x ∈ LinearMap.ker (aeval g f) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have : aeval g f * g = g * aeval g f := by
      have h1 : aeval g (f * X) = aeval g (X * f) := by rw [mul_comm]
      simpa using h1
    rw [← Module.End.mul_apply, this, Module.End.mul_apply, hx, map_zero]
  refine ⟨fun x hx => ?_, fun he j => ?_⟩
  · rw [LinearMap.mem_ker, (aeval_add_nilRad hg hh f).1 x hx]
    exact hx
  · have : LinearMap.ker (aeval g (f ^ j)) = LinearMap.ker (aeval (g + h) (f ^ j)) := by
      cases j with
      | zero =>
        ext x
        simp
      | succ j =>
        ext x
        have H := (aeval_add_nilRad hg hh (f ^ j)).2 x
        have e1 : x ∈ LinearMap.ker (aeval g (f ^ (j + 1))) ↔
            aeval g (f ^ j) x ∈ LinearMap.ker (aeval g f) := by
          rw [pow_succ', map_mul, LinearMap.mem_ker, LinearMap.mem_ker, Module.End.mul_apply]
        have e2 : x ∈ LinearMap.ker (aeval (g + h) (f ^ (j + 1))) ↔
            aeval (g + h) (f ^ j) x ∈ LinearMap.ker (aeval (g + h) f) := by
          rw [pow_succ', map_mul, LinearMap.mem_ker, LinearMap.mem_ker, Module.End.mul_apply]
        rw [e1, e2, he]
        constructor
        · intro a
          have := Submodule.add_mem _ H a
          rwa [sub_add_cancel] at this
        · intro a
          have := Submodule.sub_mem _ a H
          rwa [sub_sub_cancel] at this
    rw [this]

end GlobalTheory.CuspGL
end

open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_aeval_add_stabilizerNilradical_socle : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g h : Module.End F V) (f : F[X]), h ∈ nilRad (LinearMap.ker (aeval g f)) → LinearMap.ker (aeval g f) ≤ LinearMap.ker (aeval (g + h) f) ∧ (LinearMap.ker (aeval (g + h) f) = LinearMap.ker (aeval g f) → ∀ j : ℕ, Module.finrank F (LinearMap.ker (aeval g (f ^ j))) = Module.finrank F (LinearMap.ker (aeval (g + h) (f ^ j)))) := by
  atlas_forward_decl GlobalTheory.CuspGL.ker_aeval_add_nilRad
end

section
section
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem primitive_eq_zero_of_primary : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → ∀ (f : F[X]) (m : ℕ), Irreducible f → (∀ g : Module.End F V, LinearMap.charpoly g = f ^ m → aeval g f = 0 → φ g = 0) → ∀ g : Module.End F V, LinearMap.charpoly g = f ^ m → φ g = 0 := by
  intro F _ _ V _ _ _ φ hcl hpr f m hf h0
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F V) :=
    Finite.of_injective (fun g : Module.End F V => (g : V → V)) DFunLike.coe_injective
  have key : ∀ n : ℕ, ∀ g : Module.End F V,
      Module.finrank F V - Module.finrank F (LinearMap.ker (aeval g f)) = n →
      LinearMap.charpoly g = f ^ m → φ g = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro g hn hg
    by_cases htop : LinearMap.ker (aeval g f) = ⊤
    · exact h0 g hg (LinearMap.ker_eq_top.mp htop)
    have hCH : ∀ g' : Module.End F V, LinearMap.charpoly g' = f ^ m → aeval g' (f ^ m) = 0 := by
      intro g' hg'
      rw [← hg']
      exact LinearMap.aeval_self_charpoly g'
    have hbot : LinearMap.ker (aeval g f) ≠ ⊥ := by
      intro hb
      have hinj : Function.Injective (aeval g f : Module.End F V) := LinearMap.ker_eq_bot.mp hb
      have hinj' : Function.Injective ((aeval g f) ^ m : Module.End F V) := by
        rw [Module.End.coe_pow]
        exact hinj.iterate m
      rw [← map_pow, hCH g hg] at hinj'
      apply htop
      rw [hb, eq_comm, eq_bot_iff]
      intro x _
      exact (Submodule.mem_bot F).mpr (hinj' (by simp))
    have hinv : ∀ x ∈ LinearMap.ker (aeval g f), g x ∈ LinearMap.ker (aeval g f) := by
      intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      have hc : aeval g f * g = g * aeval g f := by
        have : aeval g (f * X) = aeval g (X * f) := by rw [mul_comm]
        simpa using this
      have := congrArg (fun k : Module.End F V => k x) hc
      simpa [hx] using this
    have hsum := hpr _ hbot htop g hinv
    have hfin : (nilRad (LinearMap.ker (aeval g f))).Finite := Set.toFinite _
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hsum
    have hterm : ∀ h ∈ hfin.toFinset, φ (g + h) =
        if LinearMap.ker (aeval (g + h) f) = LinearMap.ker (aeval g f) then φ g else 0 := by
      intro h hh
      rw [Set.Finite.mem_toFinset] at hh
      have hcp : LinearMap.charpoly (g + h) = f ^ m := by
        rw [(GlobalTheory.T.charpoly_block_and_invariant_under_stabilizerNilradical F V _ g hinv).2 h hh, hg]
      obtain ⟨hle, heq⟩ := GlobalTheory.T.ker_aeval_add_stabilizerNilradical_socle F V g h f hh
      split_ifs with hc
      · obtain ⟨e, he⟩ := GlobalTheory.T.conj_of_primary_finrank_ker_pow_eq F V g (g + h) f m hf (hCH g hg) (hCH _ hcp) (heq hc)
        rw [← he, hcl e g]
      · have hlt : LinearMap.ker (aeval g f) < LinearMap.ker (aeval (g + h) f) :=
          lt_of_le_of_ne hle (Ne.symm hc)
        have h1 := Submodule.finrank_lt_finrank_of_lt hlt
        have h2 := Submodule.finrank_le (LinearMap.ker (aeval (g + h) f))
        exact ih _ (by omega) (g + h) rfl hcp
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at hsum
    refine (mul_eq_zero.mp hsum).resolve_left ?_
    rw [Nat.cast_eq_zero, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty]
    refine ⟨0, ?_⟩
    simp [nilRad]
  intro g hg
  exact key _ g rfl hg

end GlobalTheory.CuspGL
end

open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveEndClassFunction_eq_zero_of_primary : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → ∀ (f : F[X]) (m : ℕ), Irreducible f → (∀ g : Module.End F V, LinearMap.charpoly g = f ^ m → aeval g f = 0 → φ g = 0) → ∀ g : Module.End F V, LinearMap.charpoly g = f ^ m → φ g = 0 := by
  atlas_forward_decl GlobalTheory.CuspGL.primitive_eq_zero_of_primary
end

section
section
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem finsum_mem_lin_comb_of_finite {α : Type} [Finite α] (S : Set α) (a b : ℂ) (u v : α → ℂ) :
    ∑ᶠ x ∈ S, (a * u x - b * v x) = a * (∑ᶠ x ∈ S, u x) - b * ∑ᶠ x ∈ S, v x := by
  have hS : S.Finite := Set.toFinite S
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, finsum_mem_eq_finite_toFinset_sum _ hS,
    finsum_mem_eq_finite_toFinset_sum _ hS, Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]

theorem eq_zero_of_mass_charpoly_eq_zero (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (φ : Module.End F V → ℂ) (hc : IsClassFn φ) (hp : IsPrimitive φ)
    (g : Module.End F V) (hm : mass φ (LinearMap.charpoly g) = 0) : φ g = 0 := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F V) := Finite.of_injective (fun h : Module.End F V => (h : V → V))
    DFunLike.coe_injective
  rcases Nat.eq_zero_or_pos (Module.finrank F V) with h0 | hpos
  · haveI : Subsingleton V := Module.finrank_zero_iff.mp h0
    have hset : {g' : Module.End F V | LinearMap.charpoly g' = LinearMap.charpoly g} = {g} := by
      ext g'
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      have : g' = g := Subsingleton.elim _ _
      simp [this]
    rw [mass, hset, finsum_mem_singleton] at hm
    exact hm
  by_cases hprim : ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ LinearMap.charpoly g = f ^ m
  swap
  · exact GlobalTheory.T.classFn_eq_zero_of_charpoly_not_irreducible_pow F V φ hc hp hpos g hprim
  obtain ⟨f, m, hfm, hf, hm0, hg⟩ := hprim
  set s : F[X] → ℂ := fun P => (P.natDegree : ℂ) with hs
  have hsa : IsAdditive s := isAdditive_natDegree
  have hπc : IsClassFn (psi s V) := fun e x => GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj F s V V e x
  have hπp : IsPrimitive (psi s V) := GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse F V s hsa
  have hdeg : (LinearMap.charpoly g).natDegree = Module.finrank F V := LinearMap.charpoly_natDegree g
  have hmass : mass (psi s V) (LinearMap.charpoly g) ≠ 0 := by
    rw [GlobalTheory.T.endomorphismMass_mobiusInverse_monic_eq F V s hsa _ (LinearMap.charpoly_monic g) hdeg, hdeg, hg,
      (GlobalTheory.T.additive_eq_polynomialVonMangoldt_convolution_one F s hsa).2.1 f m hfm hf hm0]
    have h1 : glCard F (Module.finrank F V) ≠ 0 := by
      rw [glCard]
      exact_mod_cast (Nat.card_pos (α := GL (Fin (Module.finrank F V)) F)).ne'
    have h2 : s f ≠ 0 := by
      simp only [hs]
      exact_mod_cast hf.natDegree_pos.ne'
    have h3 : (Nat.card F : ℂ) ^ Module.finrank F V - 1 ≠ 0 := by
      have hq : 1 < Nat.card F := Finite.one_lt_card
      have : 1 < Nat.card F ^ Module.finrank F V := Nat.one_lt_pow hpos.ne' hq
      rw [sub_ne_zero]
      exact_mod_cast this.ne'
    exact div_ne_zero (mul_ne_zero h1 h2) h3
  have hex : ∃ g₀ : Module.End F V, LinearMap.charpoly g₀ = f ^ m ∧ aeval g₀ f = 0 ∧ psi s V g₀ ≠ 0 := by
    by_contra hne
    push_neg at hne
    apply hmass
    rw [mass]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun x hx => ?_
    exact GlobalTheory.T.primitiveEndClassFunction_eq_zero_of_primary F V _ hπc hπp f m hf hne x (hg ▸ hx)
  obtain ⟨g₀, hg₀, hfg₀, hπ₀⟩ := hex
  have hconj : ∀ g₁ : Module.End F V, aeval g₁ f = 0 → ∃ e : V ≃ₗ[F] V, e.conj g₀ = g₁ := by
    intro g₁ h₁
    refine GlobalTheory.T.conj_of_primary_finrank_ker_pow_eq F V g₀ g₁ f 1 hf (by simpa using hfg₀) (by simpa using h₁) fun j => ?_
    rw [map_pow, map_pow, hfg₀, h₁]
  set φ' : Module.End F V → ℂ := fun x => psi s V g₀ * φ x - φ g₀ * psi s V x with hφ'
  have hc' : IsClassFn φ' := fun e x => by simp only [hφ', hc e x, hπc e x]
  have hp' : IsPrimitive φ' := fun A h1 h2 x hx => by
    simp only [hφ']
    rw [finsum_mem_lin_comb_of_finite _ _ _ (fun h => φ (x + h)) (fun h => psi s V (x + h)),
      hp A h1 h2 x hx, hπp A h1 h2 x hx]
    simp
  have hz : ∀ x : Module.End F V, LinearMap.charpoly x = f ^ m → φ' x = 0 := by
    refine GlobalTheory.T.primitiveEndClassFunction_eq_zero_of_primary F V φ' hc' hp' f m hf fun x _ hx => ?_
    obtain ⟨e, rfl⟩ := hconj x hx
    simp only [hφ', hc e g₀, hπc e g₀]
    ring
  have hm' : mass φ' (LinearMap.charpoly g) = 0 := by
    rw [mass]
    exact finsum_mem_eq_zero_of_forall_eq_zero fun x hx => hz x (hg ▸ hx)
  have hlin : mass φ' (LinearMap.charpoly g) = psi s V g₀ * mass φ (LinearMap.charpoly g) -
      φ g₀ * mass (psi s V) (LinearMap.charpoly g) :=
    finsum_mem_lin_comb_of_finite _ _ _ _ _
  rw [hm', hm, mul_zero, zero_sub, eq_comm, neg_eq_zero] at hlin
  have h0 : φ g₀ = 0 := (mul_eq_zero.mp hlin).resolve_right hmass
  have := hz g hg
  simp only [hφ', h0, zero_mul, sub_zero] at this
  exact (mul_eq_zero.mp this).resolve_left hπ₀

end GlobalTheory.CuspGL
end

open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveEndClassFunction_zero_of_charpoly_mass_zero : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → ∀ g : Module.End F V, mass φ (LinearMap.charpoly g) = 0 → φ g = 0 := by
  atlas_forward_decl GlobalTheory.CuspGL.eq_zero_of_mass_charpoly_eq_zero
end
