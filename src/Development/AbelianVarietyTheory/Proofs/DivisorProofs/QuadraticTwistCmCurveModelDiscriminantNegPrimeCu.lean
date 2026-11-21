import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeValuationEqDiscriminant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJOfNonrealMultiplier
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisStableLatticePointsSymmetricMem
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionWeierstrassPMemValuationSubring
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationDerivWeierstrassPOddTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardSqModPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqrtNegPrimeKernelCyclic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPKerRepsPowFourMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresSqMemStable

section
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem GlobalTheory.CMModel.tangentSlope_mem : ∀ (V : ValuationSubring ℂ) (a₄ a₆ r s t X Y : ℂ) (u : ℂˣ), IntV V ((⟨u, r, s, t⟩ : VariableChange ℂ) • (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ)) → (X - r) / (u : ℂ) ^ 2 ∈ V → (Y - t - s * (X - r)) / (u : ℂ) ^ 3 ∈ V → V.valuation (2 * Y) = V.valuation (u : ℂ) ^ 3 → ((3 * X ^ 2 + a₄) / (2 * Y) - s) / (u : ℂ) ∈ V := by
  intro V a₄ a₆ r s t X Y u hI hx hy hv
  obtain ⟨h1, h2, -, h4, -⟩ := hI
  set W' := (⟨u, r, s, t⟩ : VariableChange ℂ) • (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ) with hW'
  have hu : (u : ℂ) ≠ 0 := u.ne_zero
  have hY : 2 * Y ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact pow_ne_zero 3 ((Valuation.ne_zero_iff _).2 hu) hv.symm
  have hY0 : Y ≠ 0 := right_ne_zero_of_mul hY
  have hq : (u : ℂ) ^ 3 / (2 * Y) ∈ V := by
    rw [← ValuationSubring.valuation_le_one_iff, map_div₀, map_pow, ← hv, div_self]
    exact (Valuation.ne_zero_iff _).2 hY
  have hE : 3 * ((X - r) / (u : ℂ) ^ 2) ^ 2 + 2 * W'.a₂ * ((X - r) / (u : ℂ) ^ 2) + W'.a₄
      - W'.a₁ * ((Y - t - s * (X - r)) / (u : ℂ) ^ 3) ∈ V := by
    have h3 : (3 : ℂ) ∈ V := by simpa using natCast_mem V 3
    have h2' : (2 : ℂ) ∈ V := by simpa using natCast_mem V 2
    exact sub_mem (add_mem (add_mem (mul_mem h3 (pow_mem hx 2)) (mul_mem (mul_mem h2' h2) hx)) h4)
      (mul_mem h1 hy)
  have key : ((3 * X ^ 2 + a₄) / (2 * Y) - s) / (u : ℂ) =
      (3 * ((X - r) / (u : ℂ) ^ 2) ^ 2 + 2 * W'.a₂ * ((X - r) / (u : ℂ) ^ 2) + W'.a₄
      - W'.a₁ * ((Y - t - s * (X - r)) / (u : ℂ) ^ 3)) * ((u : ℂ) ^ 3 / (2 * Y)) := by
    simp only [hW', WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₄, Units.val_inv_eq_inv_val]
    field_simp
    ring
  rw [key]
  exact mul_mem hE hq
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_slope_mem_of_intV : ∀ (V : ValuationSubring ℂ) (a₄ a₆ r s t X Y : ℂ) (u : ℂˣ), IntV V ((⟨u, r, s, t⟩ : VariableChange ℂ) • (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ)) → (X - r) / (u : ℂ) ^ 2 ∈ V → (Y - t - s * (X - r)) / (u : ℂ) ^ 3 ∈ V → V.valuation (2 * Y) = V.valuation (u : ℂ) ^ 3 → ((3 * X ^ 2 + a₄) / (2 * Y) - s) / (u : ℂ) ∈ V := by
  atlas_forward_decl GlobalTheory.CMModel.tangentSlope_mem
end

section
section
noncomputable section

open WeierstrassCurve
open scoped BigOperators

namespace GlobalTheory.CMModel

theorem avg_mem_of_card_unit (V : ValuationSubring ℂ) {ι : Type} [Fintype ι] (f : ι → ℂ)
    (hc : V.valuation (Fintype.card ι : ℂ) = 1) (hf : ∀ i, f i ∈ V) :
    (∑ i, f i) / Fintype.card ι ∈ V := by
  rw [div_eq_mul_inv]
  refine V.mul_mem _ _ (sum_mem (S := V) fun i _ => hf i) ?_
  rw [← V.valuation_le_one_iff, map_inv₀, hc, inv_one]

theorem intV_average (V : ValuationSubring ℂ) (a₄ a₆ r s t : ℂ) (u : ℂˣ) (ι : Type) [Fintype ι]
    (X Y : ι → ℂ)
    (h : IntV V ((⟨u, r, s, t⟩ : VariableChange ℂ) • (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ)))
    (hc : V.valuation (Fintype.card ι : ℂ) = 1)
    (hX : ∀ i, (X i - r) / (u : ℂ) ^ 2 ∈ V)
    (hY : ∀ i, (Y i - t - s * (X i - r)) / (u : ℂ) ^ 3 ∈ V)
    (h2 : ∀ i, V.valuation (2 * Y i) = V.valuation (u : ℂ) ^ 3) :
    IntV V ((⟨u, (∑ i, X i) / Fintype.card ι,
      (∑ i, (3 * X i ^ 2 + a₄) / (2 * Y i)) / Fintype.card ι,
      (∑ i, Y i) / Fintype.card ι⟩ : VariableChange ℂ) •
      (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ)) := by
  have hn : (Fintype.card ι : ℂ) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hc
    exact zero_ne_one hc
  have hu : (u : ℂ) ≠ 0 := u.ne_zero
  have hr := avg_mem_of_card_unit V _ hc hX
  have ht := avg_mem_of_card_unit V _ hc hY
  have hs := avg_mem_of_card_unit V _ hc fun i =>
    GlobalTheory.T.tangent_slope_mem_of_intV V a₄ a₆ r s t (X i) (Y i) u h (hX i) (hY i) (h2 i)
  simp only [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hr hs ht
  set A := ∑ i, X i
  set B := ∑ i, (3 * X i ^ 2 + a₄) / (2 * Y i)
  set D := ∑ i, Y i
  set n : ℂ := ((Fintype.card ι : ℕ) : ℂ)
  have key : (⟨u, A / n, B / n, D / n⟩ : VariableChange ℂ) =
      (⟨1, (A - n * r) / (u : ℂ) ^ 2 / n, (B - n * s) / (u : ℂ) / n,
        (D - n * t - s * (A - n * r)) / (u : ℂ) ^ 3 / n⟩ : VariableChange ℂ) * ⟨u, r, s, t⟩ := by
    rw [VariableChange.mul_def]
    ext
    · simp
    all_goals
      simp only []
      field_simp
      ring
  rw [key, mul_smul]
  exact GlobalTheory.coeff_mem_variableChange V.toSubring h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 hr hs ht rfl

end GlobalTheory.CMModel
end
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassCoeffs_integral_average_change_of_variables : ∀ (V : ValuationSubring ℂ) (a₄ a₆ r s t : ℂ) (u : ℂˣ) (ι : Type) [Fintype ι] (X Y : ι → ℂ), IntV V ((⟨u, r, s, t⟩ : VariableChange ℂ) • (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ)) → V.valuation (Fintype.card ι : ℂ) = 1 → (∀ i, (X i - r) / (u : ℂ) ^ 2 ∈ V) → (∀ i, (Y i - t - s * (X i - r)) / (u : ℂ) ^ 3 ∈ V) → (∀ i, V.valuation (2 * Y i) = V.valuation (u : ℂ) ^ 3) → IntV V ((⟨u, (∑ i, X i) / Fintype.card ι, (∑ i, (3 * X i ^ 2 + a₄) / (2 * Y i)) / Fintype.card ι, (∑ i, Y i) / Fintype.card ι⟩ : VariableChange ℂ) • (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ)) := by
  atlas_forward_decl GlobalTheory.CMModel.intV_average
end

section
section
open WeierstrassCurve

namespace GlobalTheory.CMModel

theorem exists_intV_variableChange (W : WeierstrassCurve ℂ) [W.IsElliptic] (V : ValuationSubring ℂ)
    (u : ℂˣ) (hj : W.j ∈ V) (hu : V.valuation (u : ℂ) ^ 12 = V.valuation W.Δ) :
    ∃ r s t : ℂ, IntV V ((⟨u, r, s, t⟩ : VariableChange ℂ) • W) := by
  have : IsIntegrallyClosedIn V ℂ := (isIntegrallyClosed_iff_isIntegrallyClosedIn ℂ).1 inferInstance
  have ht : HasRationalTorsion W ℂ 12 := by
    intro x y h hn
    exact ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  obtain ⟨C, W₀, e, h₀⟩ := exists_integral_model V (L := ℂ) (W := W) ⟨⟨W.j, hj⟩, rfl⟩ ht
  have hΔ : ((C.u⁻¹ : ℂˣ) : ℂ) ^ 12 * W.Δ = 1 := by
    rw [← variableChange_Δ, e, WeierstrassCurve.baseChange, map_Δ, h₀, map_one]
  have hCu : (C.u : ℂ) ≠ 0 := C.u.ne_zero
  have hu0 : (u : ℂ) ≠ 0 := u.ne_zero
  have hΔ' : W.Δ = (C.u : ℂ) ^ 12 := by
    rw [Units.val_inv_eq_inv_val] at hΔ
    field_simp at hΔ
    exact hΔ
  have hv : V.valuation (u : ℂ) = V.valuation (C.u : ℂ) := by
    rw [hΔ', map_pow] at hu
    exact (pow_left_inj₀ zero_le' zero_le' (by norm_num)).1 hu
  have hw : (C.u : ℂ) / u ∈ V := by
    rw [← V.valuation_le_one_iff, map_div₀, hv, div_self]
    exact (map_ne_zero _).2 hCu
  have h1 : (C • W).a₁ ∈ V := by rw [e]; exact W₀.a₁.2
  have h2 : (C • W).a₂ ∈ V := by rw [e]; exact W₀.a₂.2
  have h3 : (C • W).a₃ ∈ V := by rw [e]; exact W₀.a₃.2
  have h4 : (C • W).a₄ ∈ V := by rw [e]; exact W₀.a₄.2
  have h6 : (C • W).a₆ ∈ V := by rw [e]; exact W₀.a₆.2
  refine ⟨C.r, C.s, C.t, ?_, ?_, ?_, ?_, ?_⟩
  · convert V.mul_mem _ _ hw h1 using 1
    simp only [variableChange_a₁, Units.val_inv_eq_inv_val]; field_simp
  · convert V.mul_mem _ _ (pow_mem hw 2) h2 using 1
    simp only [variableChange_a₂, Units.val_inv_eq_inv_val]; field_simp
  · convert V.mul_mem _ _ (pow_mem hw 3) h3 using 1
    simp only [variableChange_a₃, Units.val_inv_eq_inv_val]; field_simp
  · convert V.mul_mem _ _ (pow_mem hw 4) h4 using 1
    simp only [variableChange_a₄, Units.val_inv_eq_inv_val]; field_simp
  · convert V.mul_mem _ _ (pow_mem hw 6) h6 using 1
    simp only [variableChange_a₆, Units.val_inv_eq_inv_val]; field_simp

end GlobalTheory.CMModel
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_variableChange_intV_of_j_mem : ∀ (W : WeierstrassCurve ℂ) [W.IsElliptic] (V : ValuationSubring ℂ) (u : ℂˣ), W.j ∈ V → V.valuation (u : ℂ) ^ 12 = V.valuation W.Δ → ∃ r s t : ℂ, IntV V ((⟨u, r, s, t⟩ : VariableChange ℂ) • W) := by
  atlas_forward_decl GlobalTheory.CMModel.exists_intV_variableChange
end

section
open PeriodPair WeierstrassCurve

namespace GlobalTheory

theorem weierstrassP_two_mul_mul_sq (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice)
    (h2 : 2 * z ∉ L.lattice) :
    L.weierstrassP (2 * z) * L.derivWeierstrassP z ^ 2 =
      (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) ^ 2 / 4 -
        2 * L.weierstrassP z * L.derivWeierstrassP z ^ 2 := by
  rw [two_mul z] at h2 ⊢
  have hd : L.derivWeierstrassP z ≠ 0 := (derivWeierstrassP_eq_zero_iff L hz).not.mpr h2
  have hy : L.derivWeierstrassP z / 2 ≠
      (latticeCurve L).toAffine.negY (L.weierstrassP z) (L.derivWeierstrassP z / 2) := by
    intro h
    apply hd
    simp only [Affine.negY, latticeCurve] at h
    linear_combination h
  have h := latticePoint_add L z z
  rw [latticePoint_of_notMem L hz, latticePoint_of_notMem L h2,
    Affine.Point.add_self_of_Y_ne hy, Affine.Point.some.injEq] at h
  have e := h.1
  rw [Affine.slope_of_Y_ne rfl hy] at e
  simp only [Affine.negY, Affine.addX, latticeCurve] at e
  have e2 : L.derivWeierstrassP z / 2 -
      (-(L.derivWeierstrassP z / 2) - 0 * L.weierstrassP z - 0) = L.derivWeierstrassP z := by ring
  rw [e2] at e
  rw [e]
  field_simp
  ring

end GlobalTheory
end

section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassP_two_mul_mul_deriv_sq : ∀ (L : PeriodPair) (z : ℂ), z ∉ L.lattice → 2 * z ∉ L.lattice → L.weierstrassP (2 * z) * L.derivWeierstrassP z ^ 2 = (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) ^ 2 / 4 - 2 * L.weierstrassP z * L.derivWeierstrassP z ^ 2 := by
  atlas_forward_decl GlobalTheory.weierstrassP_two_mul_mul_sq
end

section
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem mem_of_duplication_eq :
    ∀ (V : ValuationSubring ℂ) (W : WeierstrassCurve ℂ) (x y δ : ℂ), IntV V W →
      W.toAffine.Equation x y → 2 * y + W.a₁ * x + W.a₃ ∈ V → δ ∈ V →
      x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ = (2 * y + W.a₁ * x + W.a₃) ^ 2 * (x + δ) →
      x ∈ V ∧ y ∈ V := by
  intro V W x y δ hW hE hl hδ h
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := hW
  have hr : ∀ z : ℂ, z ∈ V → z ∈ (algebraMap V ℂ).range := fun z hz => ⟨⟨z, hz⟩, rfl⟩
  have hr' : ∀ z : ℂ, z ∈ (algebraMap V ℂ).range → z ∈ V := by
    rintro z ⟨w, rfl⟩; exact w.2
  have hb₄ : W.b₄ ∈ V := by
    rw [WeierstrassCurve.b₄]
    exact add_mem (mul_mem (ofNat_mem V 2) h₄) (mul_mem h₁ h₃)
  have hb₆ : W.b₆ ∈ V := by
    rw [WeierstrassCurve.b₆]
    exact add_mem (pow_mem h₃ 2) (mul_mem (ofNat_mem V 4) h₆)
  have hb₈ : W.b₈ ∈ V := by
    rw [WeierstrassCurve.b₈]
    refine sub_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
    · exact mul_mem (pow_mem h₁ 2) h₆
    · exact mul_mem (mul_mem (ofNat_mem V 4) h₂) h₆
    · exact mul_mem (mul_mem h₁ h₃) h₄
    · exact mul_mem h₂ (pow_mem h₃ 2)
    · exact pow_mem h₄ 2
  set l := 2 * y + W.a₁ * x + W.a₃ with hl_def
  have hx : x ∈ V := by
    refine hr' x (GlobalTheory.mem_range_of_quartic (A := V) (c₀ := -(W.b₈ + l ^ 2 * δ))
      (c₁ := -(2 * W.b₆ + l ^ 2)) (c₂ := -W.b₄) (c₃ := 0) (hr _ ?_) (hr _ ?_) (hr _ ?_) (hr _ ?_) ?_)
    · exact neg_mem (add_mem hb₈ (mul_mem (pow_mem hl 2) hδ))
    · exact neg_mem (add_mem (mul_mem (ofNat_mem V 2) hb₆) (pow_mem hl 2))
    · exact neg_mem hb₄
    · exact zero_mem V
    · linear_combination h
  refine ⟨hx, ?_⟩
  rw [WeierstrassCurve.Affine.equation_iff] at hE
  refine hr' y (GlobalTheory.mem_range_of_quartic (A := V) (c₀ := 0) (c₁ := 0)
    (c₂ := -(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) (c₃ := W.a₁ * x + W.a₃)
    (hr _ (zero_mem V)) (hr _ (zero_mem V)) (hr _ ?_) (hr _ ?_) ?_)
  · exact neg_mem (add_mem (add_mem (add_mem (pow_mem hx 3)
      (mul_mem h₂ (pow_mem hx 2))) (mul_mem h₄ hx)) h₆)
  · exact add_mem (mul_mem h₁ hx) h₃
  · linear_combination y ^ 2 * hE

end GlobalTheory.CMModel
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_of_duplication_eq_weierstrass : ∀ (V : ValuationSubring ℂ) (W : WeierstrassCurve ℂ) (x y δ : ℂ), IntV V W → W.toAffine.Equation x y → 2 * y + W.a₁ * x + W.a₃ ∈ V → δ ∈ V → x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ = (2 * y + W.a₁ * x + W.a₃) ^ 2 * (x + δ) → x ∈ V ∧ y ∈ V := by
  atlas_forward_decl GlobalTheory.CMModel.mem_of_duplication_eq
end

section
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem torsion_coords_mem_of_odd : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → Odd N → ∀ (hu : u ≠ 0) (r s t : ℂ), IntV V ((⟨Units.mk0 u hu, r, s, t⟩ : VariableChange ℂ) • latticeCurve L) → ∀ z, z ∉ L.lattice → (N : ℂ) * z ∈ L.lattice → (L.weierstrassP z - r) / u ^ 2 ∈ V ∧ (L.derivWeierstrassP z / 2 - t - s * (L.weierstrassP z - r)) / u ^ 3 ∈ V := by
  intro L β u V N hmul hβ hΔ hN hodd hu r s t hint z hz hNz
  have h2z : 2 * z ∉ L.lattice := by
    intro h
    obtain ⟨k, hk⟩ := hodd
    have e : z = (N : ℂ) * z - ((k : ℤ) • (2 * z)) := by
      rw [zsmul_eq_mul, hk]; push_cast; ring
    exact hz (e ▸ sub_mem hNz (L.lattice.smul_mem _ h))
  have hNz2 : (N : ℂ) * (2 * z) ∈ L.lattice := by
    have e : (N : ℂ) * (2 * z) = N * z + N * z := by ring
    rw [e]; exact add_mem hNz hNz
  obtain ⟨hP', -⟩ := GlobalTheory.T.torsion_weierstrassP_mem_valuationSubring L β u V N hmul hβ hΔ hN z z hz hz hNz hNz
  obtain ⟨-, hδ⟩ := GlobalTheory.T.torsion_weierstrassP_mem_valuationSubring L β u V N hmul hβ hΔ hN (2 * z) z h2z hz hNz2 hNz
  have dup := GlobalTheory.T.weierstrassP_two_mul_mul_deriv_sq L z hz h2z
  have sq := L.derivWeierstrassP_sq z hz
  set C : VariableChange ℂ := ⟨Units.mk0 u hu, r, s, t⟩ with hC
  have hCu : ((C.u⁻¹ : ℂˣ) : ℂ) = u⁻¹ := by simp [hC]
  have hCr : C.r = r := rfl
  have hCs : C.s = s := rfl
  have hCt : C.t = t := rfl
  set P := L.weierstrassP z with hPdef
  set P' := L.derivWeierstrassP z with hP'def
  set P2 := L.weierstrassP (2 * z) with hP2def
  have hD : 2 * ((P' / 2 - t - s * (P - r)) / u ^ 3) + (C • latticeCurve L).a₁ * ((P - r) / u ^ 2)
      + (C • latticeCurve L).a₃ = P' / u ^ 3 := by
    rw [variableChange_a₁, variableChange_a₃, hCu, hCr, hCs, hCt]
    simp only [latticeCurve]
    field_simp
    ring
  apply GlobalTheory.T.mem_of_duplication_eq_weierstrass V (C • latticeCurve L) _ _ ((P2 - P) / u ^ 2) hint
  · rw [Affine.equation_iff]
    simp only [WeierstrassCurve.toAffine]
    rw [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄, variableChange_a₆, hCu, hCr, hCs, hCt]
    simp only [latticeCurve]
    linear_combination (norm := skip) (1 / 4 * u⁻¹ ^ 6) * sq
    field_simp
    ring
  · rw [hD]; exact hP'
  · exact hδ
  · rw [hD, variableChange_b₄, variableChange_b₆, variableChange_b₈, hCu, hCr]
    simp only [latticeCurve, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    linear_combination (norm := skip) (u⁻¹ ^ 8) * (-dup + (2 * P + r) * sq)
    field_simp
    ring

end GlobalTheory.CMModel
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_weierstrass_coords_mem_of_intV : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → Odd N → ∀ (hu : u ≠ 0) (r s t : ℂ), IntV V ((⟨Units.mk0 u hu, r, s, t⟩ : VariableChange ℂ) • latticeCurve L) → ∀ z, z ∉ L.lattice → (N : ℂ) * z ∈ L.lattice → (L.weierstrassP z - r) / u ^ 2 ∈ V ∧ (L.derivWeierstrassP z / 2 - t - s * (L.weierstrassP z - r)) / u ^ 3 ∈ V := by
  atlas_forward_decl GlobalTheory.CMModel.torsion_coords_mem_of_odd
end

section
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem GlobalTheory.CMModel.modelAt_of_stable_torsion : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → Odd N → ∀ (F : IntermediateField ℚ ℂ) (ι : Type) [Fintype ι] (T : ι → ℂ), L.g₂ ∈ F → L.g₃ ∈ F → u ∈ F → Stable L F T → (∀ i, T i ∉ L.lattice ∧ (N : ℂ) * T i ∈ L.lattice) → V.valuation (Fintype.card ι : ℂ) = 1 → ModelAt V F (latticeCurve L) 1 := by
  intro L β u V N hβ hβim hu12 hN hNodd F ι _ T hg2 hg3 huF hst hT hcard
  have hΔ := latticeCurve_Δ_ne_zero L
  have hu : u ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_pow (by norm_num)] at hu12
    exact hΔ ((Valuation.zero_iff _).mp hu12.symm)
  have hj : (latticeCurve L).j ∈ V := by
    have hi : _root_.IsIntegral V (latticeCurve L).j := (GlobalTheory.T.isIntegral_j_of_nonreal_multiplier L β hβ hβim).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
    rw [← hy]; exact y.2
  obtain ⟨r, s, t, hint⟩ := GlobalTheory.T.exists_variableChange_intV_of_j_mem (latticeCurve L) V (Units.mk0 u hu) hj hu12
  have htm := fun i => GlobalTheory.T.torsion_weierstrass_coords_mem_of_intV L β u V N hβ hβim hu12 hN hNodd hu r s t hint (T i) (hT i).1 (hT i).2
  have hud := fun i => GlobalTheory.T.valuation_derivWeierstrassP_oddTorsion L β u V N hβ hβim hu12 hN hNodd (T i) (hT i).1 (hT i).2
  have havg := GlobalTheory.T.weierstrassCoeffs_integral_average_change_of_variables V (-L.g₂ / 4) (-L.g₃ / 4) r s t (Units.mk0 u hu) ι
    (fun i => L.weierstrassP (T i)) (fun i => L.derivWeierstrassP (T i) / 2) hint hcard
    (fun i => (htm i).1) (fun i => (htm i).2)
    (fun i => by
      show V.valuation (2 * (L.derivWeierstrassP (T i) / 2)) = V.valuation u ^ 3
      rw [mul_div_cancel₀ _ two_ne_zero]; exact hud i)
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.T.galoisStable_lattice_points_symmetric_mem F L ι T hg2 hg3 hst (fun i => (hT i).1)
  have hnF : ((Fintype.card ι : ℕ) : ℂ) ∈ F := natCast_mem F _
  refine ⟨⟨Units.mk0 u hu, (∑ i, L.weierstrassP (T i)) / Fintype.card ι,
    (∑ i, (3 * L.weierstrassP (T i) ^ 2 + -L.g₂ / 4) / (2 * (L.derivWeierstrassP (T i) / 2))) / Fintype.card ι,
    (∑ i, L.derivWeierstrassP (T i) / 2) / Fintype.card ι⟩, huF, div_mem h1 hnF, div_mem h3 hnF,
    div_mem h2 hnF, havg, ?_⟩
  have hv : V.valuation u ^ 12 ≠ 0 := by
    rw [hu12]; exact (Valuation.ne_zero_iff _).mpr hΔ
  rw [variableChange_Δ, map_mul, map_pow, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀, map_one,
    ← hu12, inv_pow, inv_mul_cancel₀ hv]
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralModel_of_galoisStable_torsion : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → Odd N → ∀ (F : IntermediateField ℚ ℂ) (ι : Type) [Fintype ι] (T : ι → ℂ), L.g₂ ∈ F → L.g₃ ∈ F → u ∈ F → Stable L F T → (∀ i, T i ∉ L.lattice ∧ (N : ℂ) * T i ∈ L.lattice) → V.valuation (Fintype.card ι : ℂ) = 1 → ModelAt V F (latticeCurve L) 1 := by
  atlas_forward_decl GlobalTheory.CMModel.modelAt_of_stable_torsion
end

section
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem mem_of_pow_mem_valSubring (V : ValuationSubring ℂ) {x : ℂ} {n : ℕ} (hn : n ≠ 0) (h : x ^ n ∈ V) :
    x ∈ V := by
  rw [← V.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  exact (pow_le_one_iff_of_nonneg zero_le' hn).1 h

theorem inv_two_three_mem (V : ValuationSubring ℂ) (h : V.valuation (6 : ℂ) = 1) :
    (2 : ℂ)⁻¹ ∈ V ∧ (3 : ℂ)⁻¹ ∈ V := by
  have h6 : (6 : ℂ)⁻¹ ∈ V := by
    rw [← V.valuation_le_one_iff, map_inv₀, h, inv_one]
  have h2 : (2 : ℂ) ∈ V := by simpa using natCast_mem V 2
  have h3 : (3 : ℂ) ∈ V := by simpa using natCast_mem V 3
  constructor
  · have : (2 : ℂ)⁻¹ = 3 * 6⁻¹ := by norm_num
    rw [this]; exact mul_mem h3 h6
  · have : (3 : ℂ)⁻¹ = 2 * 6⁻¹ := by norm_num
    rw [this]; exact mul_mem h2 h6

theorem short_coeff_mem (V : ValuationSubring ℂ) (h : V.valuation (6 : ℂ) = 1) (a b j : ℂ) (hj : j ∈ V)
    (hd : -16 * (4 * a ^ 3 + 27 * b ^ 2) ∈ V)
    (he : j * (-16 * (4 * a ^ 3 + 27 * b ^ 2)) = (-48 * a) ^ 3) : a ∈ V ∧ b ∈ V := by
  obtain ⟨h2, h3⟩ := inv_two_three_mem V h
  have h1 : -48 * a ∈ V := mem_of_pow_mem_valSubring V (n := 3) (by norm_num) (he ▸ mul_mem hj hd)
  have ha : a ∈ V := by
    have : a = -(((2 : ℂ)⁻¹) ^ 4 * 3⁻¹ * (-48 * a)) := by ring
    rw [this]
    exact neg_mem (mul_mem (mul_mem (pow_mem h2 4) h3) h1)
  refine ⟨ha, mem_of_pow_mem_valSubring V (n := 2) (by norm_num) ?_⟩
  have h4 : (4 : ℂ) ∈ V := by simpa using natCast_mem V 4
  have : b ^ 2 = ((3 : ℂ)⁻¹) ^ 3 * (-(((2 : ℂ)⁻¹) ^ 4 * (-16 * (4 * a ^ 3 + 27 * b ^ 2))) - 4 * a ^ 3) := by
    ring
  rw [this]
  exact mul_mem (pow_mem h3 3) (sub_mem (neg_mem (mul_mem (pow_mem h2 4) hd)) (mul_mem h4 (pow_mem ha 3)))

theorem modelAt_short_of_six_unit :
    ∀ (V : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) (a₄ a₆ j u D : ℂ), j ∈ V → j * (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).Δ = (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).c₄ ^ 3 → V.valuation (6 : ℂ) = 1 → u ∈ F → u ≠ 0 → D ∈ V → V.valuation u ^ 12 * V.valuation D = V.valuation (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).Δ → ModelAt V F ⟨0, 0, 0, a₄, a₆⟩ D := by
  intro V F a₄ a₆ j u D hj he h6 hu hu0 hD hv
  set C : VariableChange ℂ := ⟨Units.mk0 u hu0, 0, 0, 0⟩ with hC
  have hΔ : (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).Δ = -16 * (4 * a₄ ^ 3 + 27 * a₆ ^ 2) := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    ring
  have hc : (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).c₄ = -48 * a₄ := by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring
  have hval : V.valuation (u⁻¹ ^ 12 * (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).Δ) = V.valuation D := by
    have hvu : V.valuation u ≠ 0 := by simpa using hu0
    rw [map_mul, map_pow, map_inv₀, ← hv, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hvu, one_pow, one_mul]
  have hmem : u⁻¹ ^ 12 * (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).Δ ∈ V := by
    rw [← V.valuation_le_one_iff, hval, V.valuation_le_one_iff]; exact hD
  have hab := short_coeff_mem V h6 (u⁻¹ ^ 4 * a₄) (u⁻¹ ^ 6 * a₆) j hj
    (by convert hmem using 1; rw [hΔ]; ring)
    (by rw [hΔ, hc] at he; linear_combination u⁻¹ ^ 12 * he)
  refine ⟨C, hu, zero_mem F, zero_mem F, zero_mem F, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [hC, variableChange_a₁, zero_mem]
  · simp [hC, variableChange_a₂, zero_mem]
  · simp [hC, variableChange_a₃, zero_mem]
  · simpa [hC, variableChange_a₄] using hab.1
  · simpa [hC, variableChange_a₆] using hab.2
  · rw [variableChange_Δ, ← hval]; simp [hC]

end GlobalTheory.CMModel
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelAt_short_of_valuation_six_eq_one : ∀ (V : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) (a₄ a₆ j u D : ℂ), j ∈ V → j * (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).Δ = (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).c₄ ^ 3 → V.valuation (6 : ℂ) = 1 → u ∈ F → u ≠ 0 → D ∈ V → V.valuation u ^ 12 * V.valuation D = V.valuation (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).Δ → ModelAt V F ⟨0, 0, 0, a₄, a₆⟩ D := by
  atlas_forward_decl GlobalTheory.CMModel.modelAt_short_of_six_unit
end

section
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem sqProd_pow_eight_mul (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ)
    (hp : p.Prime) (h4 : p % 4 = 3) (h3 : 3 < p) (hD : Datum p F L t) :
    sqProd p L t ^ 8 * (p : ℂ) ^ 6 = (latticeCurve L).Δ ^ (p - 1) := by
  obtain ⟨hmul, -, hrep⟩ := GlobalTheory.T.sqrtNegPrime_kernel_cyclic p F L t hp h4 h3 hD
  have ht0 : t ≠ 0 := by
    rintro rfl; exact hD.notMem (zero_mem _)
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hα2 : sqrtNegNat p ^ 2 = -(p : ℂ) := by
    simp only [sqrtNegNat, mul_pow, Complex.I_sq]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg p)]
    push_cast; ring
  have hα0 : sqrtNegNat p ≠ 0 := by
    intro h; apply hp0; have := hα2; rw [h] at this; simp at this; exact_mod_cast this
  have hα12 : sqrtNegNat p ^ 12 = (p : ℂ) ^ 6 := by
    rw [show (12 : ℕ) = 2 * 6 from rfl, pow_mul, hα2]; ring
  have hinj : Set.InjOn (fun k : ℕ => (k : ℂ) * t) (Finset.Ico 1 p : Set ℕ) := by
    intro a _ b _ hab
    exact_mod_cast mul_right_cancel₀ ht0 hab
  set S := (Finset.Ico 1 p).image fun k : ℕ => (k : ℂ) * t with hS
  have hcard : S.card = p - 1 := by
    rw [hS, Finset.card_image_of_injOn hinj, Nat.card_Ico]
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have heven : Even S.card := by
    rw [hcard]; obtain ⟨m, hm⟩ := hodd; exact ⟨m, by omega⟩
  have hpf := GlobalTheory.T.prod_derivWeierstrassP_kerReps_pow_four_mul' L (sqrtNegNat p) S hα0 hD.mul hrep heven
  rw [hcard, hα12] at hpf
  rw [← hpf]
  congr 1

  have hprod : ∏ x ∈ S, L.derivWeierstrassP x
      = ∏ k ∈ Finset.Ico 1 p, L.derivWeierstrassP ((k : ℂ) * t) := by
    rw [hS, Finset.prod_image hinj]
  obtain ⟨e, he⟩ := GlobalTheory.T.nonzeroSquares_sum_equiv_Ico_mod_four p hp h4
  have hpt : (p : ℂ) * t ∈ L.lattice := by
    have := (hmul (p : ℤ)).2 dvd_rfl
    simpa using this
  have hsplit : ∏ k ∈ Finset.Ico 1 p, L.derivWeierstrassP ((k : ℂ) * t)
      = ∏ s : Sq p ⊕ Sq p, L.derivWeierstrassP (((e s : ℕ) : ℂ) * t) := by
    rw [← Finset.prod_coe_sort]
    exact (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm
  have hneg : ∀ k : Sq p, L.derivWeierstrassP (((e (Sum.inr k) : ℕ) : ℂ) * t)
      = -L.derivWeierstrassP (sqPt p t k) := by
    intro k
    rw [(he k).2, Nat.cast_sub (le_of_lt k.1.2), sub_mul, sqPt]
    have := L.derivWeierstrassP_add_coe (-((k.1 : ℕ) : ℂ) * t) ⟨_, hpt⟩
    simp only at this
    rw [show (p : ℂ) * t - ((k.1 : ℕ) : ℂ) * t = -((k.1 : ℕ) : ℂ) * t + (p : ℂ) * t by ring, this,
      neg_mul, L.derivWeierstrassP_neg]
  have hpos : ∀ k : Sq p, L.derivWeierstrassP (((e (Sum.inl k) : ℕ) : ℂ) * t)
      = L.derivWeierstrassP (sqPt p t k) := by
    intro k; rw [(he k).1, sqPt]
  rw [hprod, hsplit, Fintype.prod_sum_type]
  simp only [hneg, hpos, Finset.prod_neg]
  have h1 : ((-1 : ℂ) ^ (Finset.univ : Finset (Sq p)).card) ^ 4 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [sqProd, mul_pow, mul_pow, h1]
  ring

end GlobalTheory.CMModel
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prodDerivWeierstrassPOverSquares_pow_eight_mul : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → sqProd p L t ^ 8 * (p : ℂ) ^ 6 = (latticeCurve L).Δ ^ (p - 1) := by
  atlas_forward_decl GlobalTheory.CMModel.sqProd_pow_eight_mul
end

section
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory

private lemma twelfth_power_clear_denom_three_mod_eight (p : ℕ) (D A Q s : ℂ) (n : ℕ) (hp0 : (p:ℂ) ≠ 0) (hD0 : D ≠ 0)
    (hQ0 : Q ≠ 0) (hs2 : s^2 = 1) (hε : Q^4 * (p:ℂ)^3 = s * D^(4*n+1)) :
    (A*D^n/(Q*p))^12 * (p:ℂ)^3 * D^3 * s = A^12 := by
  have h3 : Q^12 * (p:ℂ)^9 = s * D^(12*n+3) := by
    calc Q^12 * (p:ℂ)^9 = (Q^4 * (p:ℂ)^3)^3 := by ring
      _ = s^2 * s * D^(12*n+3) := by rw [hε]; ring
      _ = _ := by rw [hs2]; ring
  rw [div_pow, div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_eq_iff (by positivity)]
  linear_combination (-(A^12 * (p:ℂ)^3)) * h3

private lemma twelfth_power_clear_denom_seven_mod_eight (p : ℕ) (D A Q s : ℂ) (n : ℕ) (hD0 : D ≠ 0)
    (hs2 : s^2 = 1) (hε : Q^4 * (p:ℂ)^3 = s * D^(4*n+3)) :
    (A*Q/D^(n+1))^12 * (p:ℂ)^9 * D^3 * s = A^12 := by
  have h3 : Q^12 * (p:ℂ)^9 = s * D^(12*n+9) := by
    calc Q^12 * (p:ℂ)^9 = (Q^4 * (p:ℂ)^3)^3 := by ring
      _ = s^2 * s * D^(12*n+9) := by rw [hε]; ring
      _ = _ := by rw [hs2]; ring
  rw [div_pow, div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_eq_iff (by positivity)]
  linear_combination (A^12 * D^3 * s) * h3 + (A^12 * D^(12*n+12)) * hs2

private lemma twelfth_cancel (V : ValuationSubring ℂ) (D A u P s : ℂ) (e : ℕ) (hD0 : D ≠ 0)
    (hs2 : s^2 = 1) (hv : V.valuation A ^ 3 = V.valuation D)
    (h : u^12 * P^e * D^3 * s = A^12) :
    V.valuation u ^ 12 * V.valuation P ^ e = V.valuation D := by
  have hs : V.valuation s = 1 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hs2.trans (one_pow 2).symm) with h1 | h1 <;>
      simp [h1]
  have h' := congrArg V.valuation h
  simp only [map_mul, map_pow, hs, mul_one] at h'
  have hD' : V.valuation D ^ 3 ≠ 0 := pow_ne_zero _ ((Valuation.ne_zero_iff _).2 hD0)
  apply mul_right_cancel₀ hD'
  rw [h', show 12 = 3 * 4 from rfl, pow_mul, hv, ← pow_succ']

theorem valuation_twelfth_power_of_cube :
    ∀ (p : ℕ) (V : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) (D A Q : ℂ), p % 4 = 3 →
      D ∈ F → A ∈ F → Q ∈ F → D ≠ 0 → A ≠ 0 → V.valuation A ^ 3 = V.valuation D →
      Q ^ 8 * (p : ℂ) ^ 6 = D ^ (p - 1) →
      ∃ u ∈ F, u ≠ 0 ∧ V.valuation u ^ 12 * V.valuation (p : ℂ) ^ (if p % 8 = 3 then 3 else 9)
        = V.valuation D := by
  intro p V F D A Q hp hD hA hQ hD0 hA0 hv hrel
  obtain ⟨k, hk⟩ : ∃ k, p = 4 * k + 3 := ⟨p / 4, by omega⟩
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  rw [show p - 1 = 2 * (2 * k + 1) by omega, pow_mul'] at hrel
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at hrel
    exact pow_ne_zero _ (pow_ne_zero _ hD0) hrel.symm
  have hsq : (Q^4 * (p:ℂ)^3)^2 = (D^(2*k+1))^2 := by rw [← hrel]; ring
  obtain ⟨s, hs2, hε⟩ : ∃ s : ℂ, s^2 = 1 ∧ Q^4 * (p:ℂ)^3 = s * D^(2*k+1) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · exact ⟨1, by norm_num, by rw [h, one_mul]⟩
    · exact ⟨-1, by norm_num, by rw [h, neg_one_mul]⟩
  rcases Nat.even_or_odd' k with ⟨n, rfl | rfl⟩
  · rw [show 2 * (2 * n) + 1 = 4 * n + 1 by ring] at hε
    refine ⟨A * D^n / (Q * p), div_mem (mul_mem hA (pow_mem hD n)) (mul_mem hQ (natCast_mem F p)),
      div_ne_zero (mul_ne_zero hA0 (pow_ne_zero _ hD0)) (mul_ne_zero hQ0 hp0), ?_⟩
    rw [if_pos (by omega)]
    exact twelfth_cancel V D A _ _ s 3 hD0 hs2 hv (twelfth_power_clear_denom_three_mod_eight p D A Q s n hp0 hD0 hQ0 hs2 hε)
  · rw [show 2 * (2 * n + 1) + 1 = 4 * n + 3 by ring] at hε
    refine ⟨A * Q / D^(n+1), div_mem (mul_mem hA hQ) (pow_mem hD _),
      div_ne_zero (mul_ne_zero hA0 hQ0) (pow_ne_zero _ hD0), ?_⟩
    rw [if_neg (by omega)]
    exact twelfth_cancel V D A _ _ s 9 hD0 hs2 hv (twelfth_power_clear_denom_seven_mod_eight p D A Q s n hD0 hs2 hε)

end GlobalTheory
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuation_pow_twelve_mul_eq : ∀ (p : ℕ) (V : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) (D A Q : ℂ), p % 4 = 3 → D ∈ F → A ∈ F → Q ∈ F → D ≠ 0 → A ≠ 0 → V.valuation A ^ 3 = V.valuation D → Q ^ 8 * (p : ℂ) ^ 6 = D ^ (p - 1) → ∃ u ∈ F, u ≠ 0 ∧ V.valuation u ^ 12 * V.valuation (p : ℂ) ^ (if p % 8 = 3 then 3 else 9) = V.valuation D := by
  atlas_forward_decl GlobalTheory.valuation_twelfth_power_of_cube
end

section
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem sqrtNegNat_im_ne_zero {p : ℕ} (hp : 0 < p) : (sqrtNegNat p).im ≠ 0 := by
  have : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.2 (by exact_mod_cast hp)
  simpa [sqrtNegNat] using this.ne'

theorem modelAt_one_of_sqProd_mem : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ),
    p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → sqProd p L t ∈ F →
    ∀ V : ValuationSubring ℂ, V.valuation (p : ℂ) = 1 → ModelAt V F (latticeCurve L) 1 := by
  intro p F L t hp hp4 hp3 hD hQ V hVp
  have hβ : (sqrtNegNat p).im ≠ 0 := sqrtNegNat_im_ne_zero hp.pos
  have hΔF : (latticeCurve L).Δ ∈ F := by
    rw [latticeCurve_Δ]
    exact sub_mem (pow_mem hD.g₂_mem 3) (mul_mem (by simpa using (algebraMap_mem F (27 : ℚ))) (pow_mem hD.g₃_mem 2))
  obtain ⟨A, hAF, hA0, hAv⟩ := GlobalTheory.T.exists_cube_valuation_eq_discriminant p F L t hp hp4 hp3 hD V
  obtain ⟨u, huF, hu0, huv⟩ := GlobalTheory.T.exists_valuation_pow_twelve_mul_eq p V F (latticeCurve L).Δ A (sqProd p L t) hp4 hΔF hAF hQ
    (latticeCurve_Δ_ne_zero L) hA0 hAv (GlobalTheory.T.prodDerivWeierstrassPOverSquares_pow_eight_mul p F L t hp hp4 hp3 hD)
  rw [hVp, one_pow, mul_one] at huv
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  by_cases h2 : V.valuation (2 : ℂ) = 1
  · by_cases h3 : V.valuation (3 : ℂ) = 1
    ·
      have h6 : V.valuation (6 : ℂ) = 1 := by
        rw [show (6 : ℂ) = 2 * 3 by norm_num, map_mul, h2, h3, one_mul]
      have hj : (latticeCurve L).j ∈ V :=
        ReciprocityTheory.Gal.mem_of_isIntegral_int V (GlobalTheory.T.isIntegral_j_of_nonreal_multiplier L (sqrtNegNat p) hD.mul hβ)
      exact GlobalTheory.T.modelAt_short_of_valuation_six_eq_one V F (-L.g₂ / 4) (-L.g₃ / 4) (latticeCurve L).j u 1 hj
        (GlobalTheory.j_mul_Δ (latticeCurve L)) h6 huF hu0 (one_mem V) (by rw [map_one, mul_one]; exact huv)
    ·
      obtain ⟨N, ι, hι, T, hNodd, hN3, hNv, hcard, hT, hTor⟩ := GlobalTheory.T.exists_galoisStable_torsion_family_ker p F L t hp hp4 hp3 hD V
      have hcop : Nat.Coprime (Fintype.card ι) 3 := by
        rw [hcard]
        exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega))
      have hc : V.valuation (Fintype.card ι : ℂ) = 1 := by
        rcases GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime V _ _ hcop with h | h
        · exact h
        · exact absurd (by simpa using h) h3
      exact GlobalTheory.T.exists_integralModel_of_galoisStable_torsion L (sqrtNegNat p) u V N hD.mul hβ huv hNv hNodd F ι T hD.g₂_mem hD.g₃_mem huF
        hT hTor hc
  ·
    obtain ⟨-, hodd'⟩ := GlobalTheory.T.two_mul_card_sq_add_one_eq_and_odd_of_mod_four_eq_three p hp hp4
    have hcop : Nat.Coprime (Fintype.card (Sq p)) 2 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by rcases hodd' with ⟨k, hk⟩; omega))
    have hc : V.valuation (Fintype.card (Sq p) : ℂ) = 1 := by
      rcases GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime V _ _ hcop with h | h
      · exact h
      · exact absurd (by simpa using h) h2
    exact GlobalTheory.T.exists_integralModel_of_galoisStable_torsion L (sqrtNegNat p) u V p hD.mul hβ huv hVp hodd F (Sq p) (sqPt p t)
      hD.g₂_mem hD.g₃_mem huF ((GlobalTheory.T.prodDerivWeierstrassPOverSquares_sq_mem_stable p F L t hp hp4 hp3 hD).2 hQ)
      (GlobalTheory.T.prodDerivWeierstrassPOverSquares_ne_zero p F L t hp hp4 hp3 hD).1 hc

end GlobalTheory.CMModel
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassModel_unit_discriminant_away_from_p : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → sqProd p L t ∈ F → ∀ V : ValuationSubring ℂ, V.valuation (p : ℂ) = 1 → ModelAt V F (latticeCurve L) 1 := by
  atlas_forward_decl GlobalTheory.CMModel.modelAt_one_of_sqProd_mem
end

section
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem modelAt_shortTwist_four_mul_add_one : ∀ (V : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) (a₄ a₆ D : ℂ) (k : ℤ), a₄ ∈ F → a₆ ∈ F → ModelAt V F ⟨0, 0, 0, a₄, a₆⟩ D → ModelAt V F (shortTwist (4 * (k : ℂ) + 1) a₄ a₆) ((4 * (k : ℂ) + 1) ^ 6 * D) := by
  intro V F a₄ a₆ D k _ _ h
  obtain ⟨C, hu, hr, hs, ht, ⟨h1, h2, h3, h4, h6⟩, hΔ⟩ := h
  set d : ℂ := 4 * (k : ℂ) + 1 with hd
  have hkV : (k : ℂ) ∈ V := intCast_mem V k
  have hdV : d ∈ V := add_mem (mul_mem (by exact_mod_cast intCast_mem V 4 : (4 : ℂ) ∈ V) hkV) (one_mem V)
  have hkF : (k : ℂ) ∈ F := by simpa using IntermediateField.intCast_mem F k
  have hdF : d ∈ F := F.add_mem (F.mul_mem (by simpa using IntermediateField.intCast_mem F 4) hkF) F.one_mem
  let W₀ : WeierstrassCurve ℂ := ⟨0, 0, 0, a₄, a₆⟩
  let C' : VariableChange ℂ := ⟨C.u, d * C.r, C.s, d * C.t⟩
  refine ⟨C', hu, F.mul_mem hdF hr, hs, F.mul_mem hdF ht, ?_, ?_⟩
  · have e1 : (C' • shortTwist d a₄ a₆).a₁ = (C • W₀).a₁ := by
      simp only [variableChange_a₁, shortTwist, W₀, C']
    have e2 : (C' • shortTwist d a₄ a₆).a₂ = d * (C • W₀).a₂ + k * (C • W₀).a₁ ^ 2 := by
      simp only [variableChange_a₁, variableChange_a₂, shortTwist, W₀, C', hd]; ring
    have e3 : (C' • shortTwist d a₄ a₆).a₃ = d * (C • W₀).a₃ := by
      simp only [variableChange_a₃, shortTwist, W₀, C']; ring
    have e4 : (C' • shortTwist d a₄ a₆).a₄ = d ^ 2 * (C • W₀).a₄ + 2 * k * d * (C • W₀).a₁ * (C • W₀).a₃ := by
      simp only [variableChange_a₁, variableChange_a₃, variableChange_a₄, shortTwist, W₀, C', hd]; ring
    have e6 : (C' • shortTwist d a₄ a₆).a₆ = d ^ 3 * (C • W₀).a₆ + k * d ^ 2 * (C • W₀).a₃ ^ 2 := by
      simp only [variableChange_a₃, variableChange_a₆, shortTwist, W₀, C', hd]; ring
    have h2V : (2 : ℂ) ∈ V := by simpa using intCast_mem V 2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [e1]; exact h1
    · rw [e2]; exact add_mem (mul_mem hdV h2) (mul_mem hkV (pow_mem h1 2))
    · rw [e3]; exact mul_mem hdV h3
    · rw [e4]; exact add_mem (mul_mem (pow_mem hdV 2) h4)
        (mul_mem (mul_mem (mul_mem (mul_mem h2V hkV) hdV) h1) h3)
    · rw [e6]; exact add_mem (mul_mem (pow_mem hdV 3) h6)
        (mul_mem (mul_mem hkV (pow_mem hdV 2)) (pow_mem h3 2))
  · have eΔ : (C' • shortTwist d a₄ a₆).Δ = d ^ 6 * (C • W₀).Δ := by
      rw [variableChange_Δ, variableChange_Δ]
      simp only [C', W₀, shortTwist, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    rw [eΔ, map_mul, map_mul, hΔ]

end GlobalTheory.CMModel
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelAt_shortTwist_four_mul_add_one' : ∀ (V : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) (a₄ a₆ D : ℂ) (k : ℤ), a₄ ∈ F → a₆ ∈ F → ModelAt V F ⟨0, 0, 0, a₄, a₆⟩ D → ModelAt V F (shortTwist (4 * (k : ℂ) + 1) a₄ a₆) ((4 * (k : ℂ) + 1) ^ 6 * D) := by
  atlas_forward_decl GlobalTheory.CMModel.modelAt_shortTwist_four_mul_add_one
end

section
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel.LocAll

theorem modelAt_of_val {V : ValuationSubring ℂ} {F : IntermediateField ℚ ℂ} {W : WeierstrassCurve ℂ} {D D' : ℂ}
    (h : ModelAt V F W D) (hv : V.valuation D = V.valuation D') : ModelAt V F W D' := by
  obtain ⟨C, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨C, h1, h2, h3, h4, h5, h6.trans hv⟩

theorem mem_of_isIntegral (V : ValuationSubring ℂ) {y : ℂ} (hy : IsIntegral ℤ y) : y ∈ V := by
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := V) (K := ℂ) (hy.tower_top (A := V))
  exact hz ▸ z.2

theorem short_Δ (d a b : ℂ) : (⟨0, 0, 0, d ^ 2 * a, d ^ 3 * b⟩ : WeierstrassCurve ℂ).Δ =
    d ^ 6 * (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).Δ := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem short_c₄ (d a b : ℂ) : (⟨0, 0, 0, d ^ 2 * a, d ^ 3 * b⟩ : WeierstrassCurve ℂ).c₄ =
    d ^ 2 * (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).c₄ := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

end GlobalTheory.CMModel.LocAll

open GlobalTheory.CMModel.LocAll in

theorem GlobalTheory.CMModel.twist_modelAt_all : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → sqProd p L t ∈ F → ∀ V : ValuationSubring ℂ, ModelAt V F (shortTwist (if p % 8 = 3 then 1 else -(p : ℂ)) (-L.g₂ / 4) (-L.g₃ / 4)) (-(p : ℂ) ^ 3) := by
  intro p F L t hp h4 h3 hD hsq V
  have h27 : (27 : ℂ) ∈ F := by simpa using F.algebraMap_mem (27 : ℚ)
  have h4F : (4 : ℂ) ∈ F := by simpa using F.algebraMap_mem (4 : ℚ)
  have hg2 : -L.g₂ / 4 ∈ F := div_mem (neg_mem hD.g₂_mem) h4F
  have hg3 : -L.g₃ / 4 ∈ F := div_mem (neg_mem hD.g₃_mem) h4F
  have hpF : (p : ℂ) ∈ F := by simpa using F.algebraMap_mem (p : ℚ)
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  by_cases hv : V.valuation (p : ℂ) = 1
  · have hgood : ModelAt V F ⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩ 1 := GlobalTheory.T.weierstrassModel_unit_discriminant_away_from_p p F L t hp h4 h3 hD hsq V hv
    split_ifs with h8
    · have hk := GlobalTheory.T.modelAt_shortTwist_four_mul_add_one' V F (-L.g₂ / 4) (-L.g₃ / 4) 1 0 hg2 hg3 hgood
      have e : (4 * ((0 : ℤ) : ℂ) + 1) = 1 := by simp
      rw [e] at hk
      exact modelAt_of_val hk (by simp [hv])
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, p + 1 = 4 * m := ⟨(p + 1) / 4, by omega⟩
      have hk := GlobalTheory.T.modelAt_shortTwist_four_mul_add_one' V F (-L.g₂ / 4) (-L.g₃ / 4) 1 (-(m : ℤ)) hg2 hg3 hgood
      have hmC : (p : ℂ) + 1 = 4 * m := by exact_mod_cast hm
      have e : (4 * ((-(m : ℤ) : ℤ) : ℂ) + 1) = -(p : ℂ) := by push_cast; linear_combination hmC
      rw [e] at hk
      exact modelAt_of_val hk (by simp [hv])
  · have h6 : V.valuation (6 : ℂ) = 1 := by
      have hc : Nat.Coprime p 6 := by
        have h2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 (by omega)
        have h3' : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
        simpa using Nat.Coprime.mul_right h2 h3'
      rcases GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime V p 6 hc with h | h
      · exact absurd h hv
      · exact_mod_cast h
    obtain ⟨A, hAF, hA0, hA⟩ := GlobalTheory.T.exists_cube_valuation_eq_discriminant p F L t hp h4 h3 hD V
    have hsq8 := GlobalTheory.T.prodDerivWeierstrassPOverSquares_pow_eight_mul p F L t hp h4 h3 hD
    have hΔF : (latticeCurve L).Δ ∈ F := by
      rw [latticeCurve_Δ]
      exact sub_mem (pow_mem hD.g₂_mem 3) (mul_mem h27 (pow_mem hD.g₃_mem 2))
    obtain ⟨u, huF, hu0, hu⟩ := GlobalTheory.T.exists_valuation_pow_twelve_mul_eq p V F (latticeCurve L).Δ A (sqProd p L t) h4 hΔF hAF hsq
      (latticeCurve_Δ_ne_zero L) hA0 hA hsq8
    have him : (sqrtNegNat p).im ≠ 0 := by
      simp [sqrtNegNat]
      exact hp.pos.ne'
    have hj : (latticeCurve L).j ∈ V := mem_of_isIntegral V (GlobalTheory.T.isIntegral_j_of_nonreal_multiplier L (sqrtNegNat p) hD.mul him)
    have hjΔ := GlobalTheory.j_mul_Δ (latticeCurve L)
    have hDV : -(p : ℂ) ^ 3 ∈ V := neg_mem (pow_mem (natCast_mem V p) 3)
    have hvD : V.valuation (-(p : ℂ) ^ 3) = V.valuation (p : ℂ) ^ 3 := by simp
    set d : ℂ := if p % 8 = 3 then 1 else -(p : ℂ) with hd
    show ModelAt V F ⟨0, 0, 0, d ^ 2 * (-L.g₂ / 4), d ^ 3 * (-L.g₃ / 4)⟩ (-(p : ℂ) ^ 3)
    have hjt : (latticeCurve L).j * (⟨0, 0, 0, d ^ 2 * (-L.g₂ / 4), d ^ 3 * (-L.g₃ / 4)⟩ : WeierstrassCurve ℂ).Δ =
        (⟨0, 0, 0, d ^ 2 * (-L.g₂ / 4), d ^ 3 * (-L.g₃ / 4)⟩ : WeierstrassCurve ℂ).c₄ ^ 3 := by
      rw [short_Δ, short_c₄]
      rw [show (⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩ : WeierstrassCurve ℂ) = latticeCurve L from rfl]
      linear_combination d ^ 6 * hjΔ
    by_cases h8 : p % 8 = 3
    · have hd1 : d = 1 := by rw [hd, if_pos h8]
      rw [if_pos h8] at hu
      refine GlobalTheory.T.modelAt_short_of_valuation_six_eq_one V F _ _ _ u _ hj hjt h6 huF hu0 hDV ?_
      rw [short_Δ, hvD, hd1, one_pow, one_mul]
      exact hu
    · have hdp : d = -(p : ℂ) := by rw [hd, if_neg h8]
      rw [if_neg h8] at hu
      refine GlobalTheory.T.modelAt_short_of_valuation_six_eq_one V F _ _ _ (u * p) _ hj hjt h6 (mul_mem huF hpF) (mul_ne_zero hu0 hp0) hDV ?_
      rw [short_Δ, hvD, hdp]
      change V.valuation (u * p) ^ 12 * V.valuation (p : ℂ) ^ 3 = V.valuation ((-(p : ℂ)) ^ 6 * (latticeCurve L).Δ)
      rw [map_mul, map_mul, map_pow, Valuation.map_neg, ← hu, mul_pow]
      rw [show V.valuation (p : ℂ) ^ 9 = V.valuation (p : ℂ) ^ 6 * V.valuation (p : ℂ) ^ 3 by rw [← pow_add],
        show V.valuation (p : ℂ) ^ 12 = V.valuation (p : ℂ) ^ 6 * V.valuation (p : ℂ) ^ 6 by rw [← pow_add]]
      ac_rfl
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadraticTwist_cmCurve_model_discriminant_negPrimeCube : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → sqProd p L t ∈ F → ∀ V : ValuationSubring ℂ, ModelAt V F (shortTwist (if p % 8 = 3 then 1 else -(p : ℂ)) (-L.g₂ / 4) (-L.g₃ / 4)) (-(p : ℂ) ^ 3) := by
  atlas_forward_decl GlobalTheory.CMModel.twist_modelAt_all
end
