import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTrSelf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLatTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JTEqAndPowTwelveEqDD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfLatticeTauLatticeMembership
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneityOfIsTauOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJInvariantOfComplexMultiplicationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinWeierstrassValuesLatticeTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralModularFamilyValueDivPeriodPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelLinearOperations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularGroupRowVecAndConjRightActionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassTorsionQCoefficients
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassPTorsionIsModularFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionNormalizedWeierstrassPTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelLinearOperationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionNormalizedDerivWeierstrassPTorsion

section
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam

theorem isIntegral_sq_mul_wp_sub_div : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (ω : ℂ), IsIntegral ℤ (jT τ) → ω ^ 12 = DD τ →
    ∀ x y : Fin 2 → ZMod N, x ≠ 0 → y ≠ 0 →
      IsIntegral ℤ ((N : ℂ) ^ 2 * (wp N x τ - wp N y τ) / ω ^ 2) := by
  intro N _ τ ω hj hω x y hx hy
  obtain ⟨hR, -, -, -, hz, -⟩ := GlobalTheory.T.modularGroup_rowVec_and_conj_rightActions N
  have hvz : ∀ (v : Fin 2 → ZMod N) (γ : SL(2, ℤ)), vact N v γ = 0 ↔ v = 0 := fun v γ => hz v _
  let ι := {p : (Fin 2 → ZMod N) × (Fin 2 → ZMod N) // p.1 ≠ 0 ∧ p.2 ≠ 0}
  let act : ι → SL(2, ℤ) → ι := fun p γ =>
    ⟨(vact N p.1.1 γ, vact N p.1.2 γ), by simp only [ne_eq, hvz]; exact p.2⟩
  have hRA : IsRAct act :=
    ⟨fun p => Subtype.ext (Prod.ext (hR.1 _) (hR.1 _)),
     fun p γ δ => Subtype.ext (Prod.ext (hR.2 _ _ _) (hR.2 _ _ _))⟩
  have h1 : IsFam act 2 (fun p => wp N p.1.1) :=
    (GlobalTheory.QFam.isFam_algebra _ (vact N)).2.2.2.2.2.2.2 ι act (fun p => p.1.1) 2 (wp N) (fun _ _ => rfl) (GlobalTheory.T.weierstrassP_torsion_isModularFamily N).1
  have h2 : IsFam act 2 (fun p => wp N p.1.2) :=
    (GlobalTheory.QFam.isFam_algebra _ (vact N)).2.2.2.2.2.2.2 ι act (fun p => p.1.2) 2 (wp N) (fun _ _ => rfl) (GlobalTheory.T.weierstrassP_torsion_isModularFamily N).1
  have hsub := ((GlobalTheory.QFam.isFam_algebra ι act).2.1 2 _ _ h1 h2).2
  have hfam : IsFam act ((2 : ℕ) : ℤ) (fun p τ => (N : ℂ) ^ 2 * (wp N p.1.1 τ - wp N p.1.2 τ)) := by
    have := (GlobalTheory.QFam.isFam_algebra ι act).2.2.1 2 ((N : ℂ) ^ 2) _ hsub
    simpa using this
  let R : Subring ℂ := (integralClosure ℤ ℂ).toSubring
  have hmem : ∀ z : ℂ, z ∈ R ↔ IsIntegral ℤ z := fun z => by
    simp [R, Subalgebra.mem_toSubring, mem_integralClosure_iff]
  have hNx : ∀ v : Fin 2 → ZMod N, N • v = 0 := fun v => by
    funext i; simp [nsmul_eq_mul, ZMod.natCast_self]
  have hQ : ∀ p : ι, QAll (· ∈ R) N (fun τ => (N : ℂ) ^ 2 * (wp N p.1.1 τ - wp N p.1.2 τ)) := by
    intro p
    refine ⟨fun n => (N : ℂ) ^ 2 * (cP N p.1.1 n - cP N p.1.2 n), ?_, fun n => ?_⟩
    · exact (GlobalTheory.QFam.hasQ_linear N).2.2.1 _ _ _ ((GlobalTheory.QFam.hasQ_linear N).2.1 _ _ _ _ (GlobalTheory.T.hasQExpansion_normalizedWeierstrassPTorsion N _) (GlobalTheory.T.hasQExpansion_normalizedWeierstrassPTorsion N _))
    · show (N : ℂ) ^ 2 * (cP N p.1.1 n - cP N p.1.2 n) ∈ R
      rw [hmem]
      have e : (N : ℂ) ^ 2 * (cP N p.1.1 n - cP N p.1.2 n) =
          (N : ℂ) ^ 2 * cB N p.1.1 n - (N : ℂ) ^ 2 * cB N p.1.2 n := by
        simp only [cP, if_neg p.2.1, if_neg p.2.2]; ring
      rw [e]
      exact (GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N N p.1.1 n (NeZero.pos N) (hNx _)).1.sub
        (GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N N p.1.2 n (NeZero.pos N) (hNx _)).1
  have hjR : IsIntegral R (jT τ) := hj.tower_top
  have hT := GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow ι act 2 N (fun p τ => (N : ℂ) ^ 2 * (wp N p.1.1 τ - wp N p.1.2 τ)) R τ ω
    (NeZero.pos N) hRA.actBij hfam hQ hjR hω ⟨(x, y), hx, hy⟩
  haveI : Algebra.IsIntegral ℤ R := ⟨fun r => by
    have h : IsIntegral ℤ ((r : ℂ)) := (hmem _).1 r.2
    exact (isIntegral_algHom_iff (R.subtype.toIntAlgHom) Subtype.coe_injective).1 h⟩
  exact isIntegral_trans _ hT

end GlobalTheory.WpFam
end

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_weierstrassP_torsion_difference : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (ω : ℂ), IsIntegral ℤ (jT τ) → ω ^ 12 = DD τ → ∀ x y : Fin 2 → ZMod N, x ≠ 0 → y ≠ 0 → IsIntegral ℤ ((N : ℂ) ^ 2 * (wp N x τ - wp N y τ) / ω ^ 2) := by
  atlas_forward_decl GlobalTheory.WpFam.isIntegral_sq_mul_wp_sub_div
end

section
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.WpInt

theorem isIntegral_int_of_closure (y : ℂ)
    (hy : IsIntegral (integralClosure ℤ ℂ).toSubring y) : IsIntegral ℤ y := by
  set R : Subring ℂ := (integralClosure ℤ ℂ).toSubring
  haveI : Algebra.IsIntegral ℤ R := ⟨fun r => by
    have h : IsIntegral ℤ (r : ℂ) := r.2
    exact (isIntegral_algHom_iff (R.subtype.toIntAlgHom) Subtype.coe_injective).mp h⟩
  exact isIntegral_trans (R := ℤ) (A := R) y hy

theorem main : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (ω : ℂ), IsIntegral ℤ (jT τ) → ω ^ 12 = DD τ →
    ∀ x : Fin 2 → ZMod N, IsIntegral ℤ (12 * (N : ℂ) ^ 2 * wp N x τ / ω ^ 2) ∧
      IsIntegral ℤ ((N : ℂ) ^ 3 * wpd N x τ / ω ^ 3) := by
  intro N _ τ ω hj hω x
  set R : Subring ℂ := (integralClosure ℤ ℂ).toSubring with hR
  have hjR : IsIntegral R (jT τ) := hj.tower_top
  have hbij : ActBij (vact N) := (GlobalTheory.T.modularGroup_rowVec_and_conj_rightActions N).1.actBij
  have hfam := GlobalTheory.T.weierstrassP_torsion_isModularFamily N
  have halg := GlobalTheory.T.isSLTwoPermutedModularFamily_algebra_closure (Fin 2 → ZMod N) (vact N)
  have hlin := GlobalTheory.T.hasQExpansionOfLevel_linear_operations N
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNx : ∀ y : Fin 2 → ZMod N, N • y = 0 := fun y => by
    funext i; simp [nsmul_eq_mul]
  constructor
  · have hF : IsFam (vact N) ((2 : ℕ) : ℤ) (fun y t => (12 * (N : ℂ) ^ 2) * wp N y t) :=
      halg.2.2.1 2 _ (wp N) hfam.1
    have hQ : ∀ y, QAll (· ∈ R) N ((fun y t => (12 * (N : ℂ) ^ 2) * wp N y t) y) := fun y =>
      ⟨fun k => 12 * (N : ℂ) ^ 2 * cP N y k, hlin.2.2.1 _ _ _ (GlobalTheory.T.hasQExpansion_normalizedWeierstrassPTorsion N y),
        fun k => (GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N N y k hN (hNx y)).2.2.1⟩
    have h := GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow _ (vact N) 2 N _ R τ ω hN hbij hF hQ hjR hω x
    exact isIntegral_int_of_closure _ h
  · have hF : IsFam (vact N) ((3 : ℕ) : ℤ) (fun y t => ((N : ℂ) ^ 3) * wpd N y t) :=
      halg.2.2.1 3 _ (wpd N) hfam.2
    have hQ : ∀ y, QAll (· ∈ R) N ((fun y t => ((N : ℂ) ^ 3) * wpd N y t) y) := fun y =>
      ⟨fun k => (N : ℂ) ^ 3 * cD N y k, hlin.2.2.1 _ _ _ (GlobalTheory.T.hasQExpansion_normalizedDerivWeierstrassPTorsion N y),
        fun k => (GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N N y k hN (hNx y)).2.1⟩
    have h := GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow _ (vact N) 3 N _ R τ ω hN hbij hF hQ hjR hω x
    exact isIntegral_int_of_closure _ h

end GlobalTheory.WpInt
end
end

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_weierstrassP_torsion_integral_j : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (ω : ℂ), IsIntegral ℤ (jT τ) → ω ^ 12 = DD τ → ∀ x : Fin 2 → ZMod N, IsIntegral ℤ (12 * (N : ℂ) ^ 2 * wp N x τ / ω ^ 2) ∧ IsIntegral ℤ ((N : ℂ) ^ 3 * wpd N x τ / ω ^ 3) := by
  atlas_forward_decl GlobalTheory.WpInt.main
end

section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam.LatTorsVal

theorem exists_tors {L : PeriodPair} {c : ℂ} {τ : ℍ} (hτ : IsTauOf L c τ) (M : ℕ) [NeZero M] (P : ℂ)
    (hP : (M : ℂ) * P ∈ L.lattice) :
    ∃ x : Fin 2 → ZMod M, P - c * tors M τ x ∈ L.lattice ∧ (P ∉ L.lattice → x ≠ 0) := by
  have hom := GlobalTheory.T.weierstrassP_homogeneity_of_isTauOf L c τ hτ
  have tm := GlobalTheory.WpFam.TorsMem.main M τ
  have hc : c ≠ 0 := hτ.1
  have hPz : P = c * (P / c) := by field_simp
  have hMz : (M : ℂ) * (P / c) ∈ (tauPair τ).lattice := by
    rw [← hom.1]
    have : c * ((M : ℂ) * (P / c)) = (M : ℂ) * P := by rw [hPz]; field_simp
    rw [this]; exact hP
  obtain ⟨x, hx⟩ := tm.2.2.2.2 (P / c) hMz
  refine ⟨x, ?_, ?_⟩
  · have := (hom.1 _).2 hx
    rwa [mul_sub, ← hPz] at this
  · rintro hPL rfl
    apply hPL
    have h0 := (tm.2.2.1 0).2 rfl
    have : P / c ∈ (tauPair τ).lattice := by
      have := add_mem hx h0
      simpa using this
    rw [hPz]; exact (hom.1 _).2 this

theorem wp_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (M : ℕ) (P : ℂ) (x : Fin 2 → ZMod M)
    (h : P - c * tors M τ x ∈ L.lattice) :
    L.weierstrassP P = L.weierstrassP (c * tors M τ x) ∧
      L.derivWeierstrassP P = L.derivWeierstrassP (c * tors M τ x) := by
  have e : P = c * tors M τ x + ((⟨P - c * tors M τ x, h⟩ : L.lattice) : ℂ) := by simp
  constructor
  · rw [e, L.weierstrassP_add_coe]
  · rw [e, L.derivWeierstrassP_add_coe]

theorem main : ∀ (L : PeriodPair) (β Ω : ℂ) (M : ℕ), MulStable L β → β.im ≠ 0 → Ω ^ 12 = latDisc L → 0 < M → (∀ P, (M : ℂ) * P ∈ L.lattice → IsIntegral ℤ (12 * (M : ℂ) ^ 2 * L.weierstrassP P / Ω ^ 2) ∧ IsIntegral ℤ ((M : ℂ) ^ 3 * L.derivWeierstrassP P / Ω ^ 3)) ∧ ∀ P Q, P ∉ L.lattice → Q ∉ L.lattice → (M : ℂ) * P ∈ L.lattice → (M : ℂ) * Q ∈ L.lattice → IsIntegral ℤ ((M : ℂ) ^ 2 * (L.weierstrassP P - L.weierstrassP Q) / Ω ^ 2) := by
  intro L β Ω M hβ hβi hΩ hM
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨c, τ, hτ⟩ := latTau L
  have hj := GlobalTheory.T.isIntegral_jInvariant_of_complexMultiplication L c τ β hτ hβ hβi
  have hω := (GlobalTheory.QFam.jT_eq_and_pow_twelve_eq_DD L c τ hτ).2 Ω hΩ
  have st := (GlobalTheory.T.eisensteinWeierstrass_values_lattice_tau L c Ω τ hτ).2 M
  refine ⟨fun P hP => ?_, fun P Q hP hQ hMP hMQ => ?_⟩
  · obtain ⟨x, hx, -⟩ := exists_tors hτ M P hP
    obtain ⟨e1, e2⟩ := wp_eq M P x hx
    have hv := GlobalTheory.T.isIntegral_weierstrassP_torsion_integral_j M τ _ hj hω x
    rw [e1, e2, mul_div_assoc, mul_div_assoc, ← (st x).1, ← (st x).2, ← mul_div_assoc, ← mul_div_assoc]
    exact hv
  · obtain ⟨x, hx, hx0⟩ := exists_tors hτ M P hMP
    obtain ⟨y, hy, hy0⟩ := exists_tors hτ M Q hMQ
    have hv := GlobalTheory.T.isIntegral_weierstrassP_torsion_difference M τ _ hj hω x y (hx0 hP) (hy0 hQ)
    rw [(wp_eq M P x hx).1, (wp_eq M Q y hy).1, mul_div_assoc, sub_div, ← (st x).1, ← (st y).1, ← sub_div,
      ← mul_div_assoc]
    exact hv

end GlobalTheory.WpFam.LatTorsVal
end
