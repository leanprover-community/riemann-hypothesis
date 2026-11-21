import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TemperedProducts.CentredSegSqInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleIrreducibleCentralScalar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetTwoFactorCentralCharacterMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetTwoFactorSplitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepCentralCharacterFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingUnitAbsPowBounds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterTwistPowDegree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterEqOfScalar

section
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.Segment

private theorem two_mul_triangle_add_mul_eq (d l₀ l₁ : ℕ) (h₀ : 1 ≤ l₀) (h₁ : 1 ≤ l₁) :
    2 * (d * (l₀ * l₁ + l₀ * (l₀ - 1) / 2)) * (l₀ + l₁) =
      2 * (d * ((l₀ + l₁) * (l₀ + l₁ - 1) / 2)) * l₀ + d * ((l₀ + l₁) * l₀ * l₁) := by
  obtain ⟨a, rfl⟩ : ∃ a, l₀ = a + 1 := ⟨l₀ - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, l₁ = b + 1 := ⟨l₁ - 1, by omega⟩
  rw [show a + 1 + (b + 1) = a + b + 1 + 1 by ring, Nat.add_sub_cancel, Nat.add_sub_cancel]
  have hp : 2 * ((a + 1) * a / 2) = (a + 1) * a :=
    Nat.two_mul_div_two_of_even (by rw [mul_comm]; exact Nat.even_mul_succ_self a)
  have hq : 2 * ((a + b + 1 + 1) * (a + b + 1) / 2) = (a + b + 1 + 1) * (a + b + 1) :=
    Nat.two_mul_div_two_of_even (by rw [mul_comm]; exact Nat.even_mul_succ_self (a + b + 1))
  generalize (a + 1) * a / 2 = p at hp ⊢
  generalize (a + b + 1 + 1) * (a + b + 1) / 2 = q at hq ⊢
  zify at hp hq ⊢
  linear_combination ((d : ℤ) * (a + b + 1 + 1)) * hp - ((d : ℤ) * (a + 1)) * hq

theorem top_piece_exponent_lt_one : ∀ (α r : ℝ) (d l0 l1 : ℕ), 0 < α → α < 1 → 0 < r → 1 ≤ d → 1 ≤ l0 → 1 ≤ l1 →
    r ^ (l0 + l1) * α ^ (d * ((l0 + l1) * (l0 + l1 - 1) / 2)) = 1 →
    r ^ l0 * α ^ (d * (l0 * l1 + l0 * (l0 - 1) / 2)) < 1 := by
  intro α r d l0 l1 hα0 hα1 hr hd hl0 hl1 h
  have key := two_mul_triangle_add_mul_eq d l0 l1 hl0 hl1
  set T := (l0 + l1) * (l0 + l1 - 1) / 2
  set S := l0 * l1 + l0 * (l0 - 1) / 2
  have hpow : (r ^ l0 * α ^ (d * S)) ^ (2 * (l0 + l1)) = α ^ (d * ((l0 + l1) * l0 * l1)) := by
    calc (r ^ l0 * α ^ (d * S)) ^ (2 * (l0 + l1))
        = (r ^ (l0 + l1)) ^ (2 * l0) * α ^ (2 * (d * S) * (l0 + l1)) := by
          rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
          congr 2 <;> ring
      _ = (r ^ (l0 + l1) * α ^ (d * T)) ^ (2 * l0) * α ^ (d * ((l0 + l1) * l0 * l1)) := by
          rw [key, pow_add α, mul_pow (r ^ (l0 + l1)), ← pow_mul α (d * T),
            show d * T * (2 * l0) = 2 * (d * T) * l0 by ring, ← mul_assoc ((r ^ (l0 + l1)) ^ (2 * l0))]
      _ = α ^ (d * ((l0 + l1) * l0 * l1)) := by rw [h, one_pow, one_mul]
  have hlt : α ^ (d * ((l0 + l1) * l0 * l1)) < 1 :=
    pow_lt_one₀ hα0.le hα1
      (Nat.mul_pos (by omega) (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))).ne'
  by_contra hc
  push_neg at hc
  have h1 : 1 ≤ (r ^ l0 * α ^ (d * S)) ^ (2 * (l0 + l1)) := one_le_pow₀ hc
  rw [hpow] at h1
  exact absurd hlt (not_lt.mpr h1)

end GlobalTheory.CompanionTheory.Segment
end

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_pow_partial_segment_lt_one : ∀ (α r : ℝ) (d l0 l1 : ℕ), 0 < α → α < 1 → 0 < r → 1 ≤ d → 1 ≤ l0 → 1 ≤ l1 → r ^ (l0 + l1) * α ^ (d * ((l0 + l1) * (l0 + l1 - 1) / 2)) = 1 → r ^ l0 * α ^ (d * (l0 * l1 + l0 * (l0 - 1) / 2)) < 1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Segment.top_piece_exponent_lt_one
end

section
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.SegLink

theorem one_le_deg_of_isLSeg {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {Δ : Segment k} {y : IrrGL k} (hL : IsLSeg Δ y.rep) : 1 ≤ y.1 := by
  obtain ⟨hd, -⟩ := hL
  have hterm : ∀ a, (Δ.term a).fst = Δ.d := fun a => rfl
  rw [← hd]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact Nat.mul_pos Δ.len_pos Δ.d_pos

theorem norm_top_eq (r A : ℝ) (d d0 l0 l1 m : ℕ) (h : d0 = d) :
    (r * (A ^ l1) ^ d) ^ l0 * (A ^ d0) ^ m = r ^ l0 * A ^ (d * (l0 * l1 + m)) := by
  subst h
  ring

theorem centredSegSqInt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    Zls.CasselmanSuffSq k → GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.LSegJacquet k → Zz.CentredSegSqInt k := by
  intro k _ _ _ _ hCas hIA hLJ Δ y hL hU
  have hN : 1 ≤ y.1 := one_le_deg_of_isLSeg hL
  have hmax : Zls.MaxExpStrict y.rep := by
    intro x hd hpos hjm t ht c hc
    obtain ⟨Γ, ⟨hlen, hfirst⟩, hΓ⟩ := GlobalTheory.T.segment_jacquet_two_factor_split k Δ y.1 _ y.rep hLJ hL x hd hpos hjm
    obtain ⟨hα0, hα1, hnorm⟩ := GlobalTheory.T.contracting_unit_abs_pow_bounds k t ht
    obtain ⟨c0, hc0⟩ := GlobalTheory.T.admissible_irreducible_central_scalar k Δ.first.fst _ Δ.first.rep Δ.first.snd.rep.smooth
      Δ.first.snd.rep.irr (hIA k _ _ _ Δ.first.snd.rep.smooth Δ.first.snd.rep.irr) t
    obtain ⟨cy, hcy⟩ := GlobalTheory.T.admissible_irreducible_central_scalar k y.fst _ y.rep y.snd.rep.smooth y.snd.rep.irr
      (hIA k _ _ _ y.snd.rep.smooth y.snd.rep.irr) t
    have hprod := GlobalTheory.T.jacquet_two_factor_central_character_mul k y.fst _ y.rep x hd hjm t cy (c 0) (c 1) hcy (hc 0) (hc 1)
    have hcy1 : ‖cy‖ = 1 := hU t cy hcy
    have hy1 := hU t _ (GlobalTheory.T.segment_rep_central_character_formula k Δ y hL t c0 hc0)
    rw [norm_mul, norm_pow, norm_pow, hnorm, ← pow_mul] at hy1
    have hr : 0 < ‖c0‖ := by
      rcases (norm_nonneg c0).lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h, zero_pow (Nat.pos_iff_ne_zero.mp Δ.len_pos), zero_mul] at hy1
        exact zero_ne_one hy1
    have hlen2 : (Γ 0).len + (Γ 1).len = Δ.len := by rw [← hlen, Fin.sum_univ_two]
    rw [← hlen2] at hy1
    have hb0 : Zc.below Γ 0 = (Γ 1).len := by
      simp [Zc.below, Finset.sum_filter, Fin.sum_univ_two]
    have hf0 : (Γ 0).first.fst = Δ.first.fst := by rw [hfirst 0]; rfl
    have hG0 : Zl.ScalarBy (Γ 0).first t
        (c0 * ↑((GlobalTheory.SmGL.absPow k ↑(Zc.below Γ 0)) t) ^ Δ.first.fst) := by
      rw [hfirst 0]
      exact GlobalTheory.T.central_character_twist_pow_degree k Δ.first t c0 _ hc0
    have he0 := GlobalTheory.T.central_character_eq_of_scalar k (x 0) t _ _ (hc 0) (GlobalTheory.T.segment_rep_central_character_formula k (Γ 0) (x 0) (hΓ 0) t _ hG0)
    have hn0 : ‖c 0‖ = ‖c0‖ ^ (Γ 0).len * GlobalTheory.SplitWeil.nabs k t ^
        (Δ.first.fst * ((Γ 0).len * (Γ 1).len + (Γ 0).len * ((Γ 0).len - 1) / 2)) := by
      rw [he0, norm_mul, norm_pow, norm_mul, norm_pow, norm_pow, hnorm, hnorm, hb0]
      exact norm_top_eq _ _ _ _ _ _ _ hf0
    refine ⟨?_, ?_⟩
    · intro j hj
      have hj0 : j = 0 := Fin.ext (by omega)
      subst hj0
      have hp : (∏ i ∈ Finset.univ.filter (fun i : Fin 2 => i ≤ 0), ‖c i‖) = ‖c 0‖ := by
        simp [Finset.prod_filter, Fin.prod_univ_two]
      rw [hp, hn0]
      exact GlobalTheory.T.real_pow_partial_segment_lt_one _ _ _ _ _ hα0 hα1 hr Δ.d_pos (Γ 0).len_pos (Γ 1).len_pos hy1
    · rw [Fin.prod_univ_two, ← norm_mul, hprod, hcy1]
  exact @hCas y.1 _ _ _ y.rep hN y.snd.rep.smooth y.snd.rep.irr (fun t c hc => hU t c hc) hmax

end GlobalTheory.CompanionTheory.SegLink
end

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centred_segment_square_integrable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zls.CasselmanSuffSq k → GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.LSegJacquet k → Zz.CentredSegSqInt k := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SegLink.centredSegSqInt
end
