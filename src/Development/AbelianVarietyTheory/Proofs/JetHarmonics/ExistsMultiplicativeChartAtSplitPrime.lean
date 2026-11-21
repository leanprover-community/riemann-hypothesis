import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UwEllipticFlow
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLaws
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.NodalSeriesPeriods
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HeightOneOfSplit
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpBinomialPowerSubOneSeriesIntegralityCompositio
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsIsoGmOfMap

section
noncomputable section

namespace GlobalTheory.MomOne.ChordLaw

section Algebra

variable {A B : Type} [CommRing A] [CommRing B]

def eqn (W : WeierstrassCurve A) (u w : A) : A :=
  u ^ 3 + W.a₁ * u * w + W.a₂ * u ^ 2 * w + W.a₃ * w ^ 2 + W.a₄ * u * w ^ 2 + W.a₆ * w ^ 3 - w

def fu (W : WeierstrassCurve A) (u w : A) : A :=
  1 - W.a₁ * u - W.a₂ * u ^ 2 - 2 * W.a₃ * w - 2 * W.a₄ * u * w - 3 * W.a₆ * w ^ 2

def fw (W : WeierstrassCurve A) (u w : A) : A :=
  3 * u ^ 2 + W.a₁ * w + 2 * W.a₂ * u * w + W.a₄ * w ^ 2

def k3 (W : WeierstrassCurve A) (l : A) : A := 1 + W.a₂ * l + W.a₄ * l ^ 2 + W.a₆ * l ^ 3

def k2 (W : WeierstrassCurve A) (l n : A) : A :=
  W.a₁ * l + W.a₂ * n + W.a₃ * l ^ 2 + 2 * W.a₄ * l * n + 3 * W.a₆ * l ^ 2 * n

theorem map_eqn (φ : A →+* B) (W : WeierstrassCurve A) (u w : A) :
    φ (eqn W u w) = eqn (W.map φ) (φ u) (φ w) := by
  simp [eqn]

theorem map_fu (φ : A →+* B) (W : WeierstrassCurve A) (u w : A) :
    φ (fu W u w) = fu (W.map φ) (φ u) (φ w) := by
  simp [fu, map_ofNat]

variable {R : Type} [CommRing R] [Algebra R A]

def Const (D : Derivation R A A) (W : WeierstrassCurve A) : Prop :=
  D W.a₁ = 0 ∧ D W.a₂ = 0 ∧ D W.a₃ = 0 ∧ D W.a₄ = 0 ∧ D W.a₆ = 0

theorem der_two (D : Derivation R A A) : D 2 = 0 := by
  have := D.map_natCast 2
  simpa using this

theorem der_three (D : Derivation R A A) : D 3 = 0 := by
  have := D.map_natCast 3
  simpa using this

theorem der_eqn {D : Derivation R A A} {W : WeierstrassCurve A} (hD : Const D W) {u w : A}
    (h : eqn W u w = 0) : fu W u w * D w = fw W u w * D u := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hD
  have := congrArg D h
  simp only [eqn, map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow, h1, h2, h3, h4, h6,
    smul_eq_mul, nsmul_eq_mul, map_zero] at this
  simp only [fu, fw]
  push_cast at this
  linear_combination -this

theorem third_eqn [IsDomain A] {W : WeierstrassCurve A} {u₀ u₁ u₃ l n : A}
    (h₀ : eqn W u₀ (l * u₀ + n) = 0) (h₁ : eqn W u₁ (l * u₁ + n) = 0) (hne : u₀ ≠ u₁)
    (h₃ : k3 W l * u₃ = -(k3 W l * (u₀ + u₁)) - k2 W l n) :
    eqn W u₃ (l * u₃ + n) = 0 ∧
      fw W u₀ (l * u₀ + n) - l * fu W u₀ (l * u₀ + n) = (u₀ - u₁) * (k3 W l * (u₀ - u₃)) := by
  have hQ : k3 W l * (u₀ ^ 2 + u₀ * u₁ + u₁ ^ 2) + k2 W l n * (u₀ + u₁) +
      (W.a₁ * n + 2 * W.a₃ * l * n + W.a₄ * n ^ 2 + 3 * W.a₆ * l * n ^ 2 - l) = 0 := by
    apply mul_left_cancel₀ (sub_ne_zero.2 hne)
    simp only [eqn, k3, k2] at *
    linear_combination h₀ - h₁
  simp only [eqn, k3, k2, fu, fw] at *
  constructor
  · linear_combination h₀ + (u₃ - u₀) * hQ + (u₃ - u₀) * (u₃ - u₁) * h₃
  · linear_combination hQ + (u₀ - u₁) * h₃

theorem third_flow [IsDomain A] {D : Derivation R A A} {W : WeierstrassCurve A} (hD : Const D W)
    {u₀ u₁ u₃ l n : A}
    (h₀ : eqn W u₀ (l * u₀ + n) = 0) (h₁ : eqn W u₁ (l * u₁ + n) = 0) (hne : u₀ ≠ u₁)
    (h₃ : k3 W l * u₃ = -(k3 W l * (u₀ + u₁)) - k2 W l n) (hk : k3 W l ≠ 0)
    (j₀ : fu W u₀ (l * u₀ + n) ≠ 0) (j₁ : fu W u₁ (l * u₁ + n) ≠ 0)
    (d₀ : D u₀ = fu W u₀ (l * u₀ + n)) (d₁ : D u₁ = 0) :
    D u₃ = -fu W u₃ (l * u₃ + n) := by
  have e₀ : D (l * u₀ + n) = fw W u₀ (l * u₀ + n) := by
    apply mul_left_cancel₀ j₀
    rw [der_eqn hD h₀, d₀, mul_comm]
  have e₁ : D (l * u₁ + n) = 0 := by
    apply mul_left_cancel₀ j₁
    rw [der_eqn hD h₁, d₁, mul_zero, mul_zero]
  simp only [map_add, Derivation.leibniz, smul_eq_mul, d₀, d₁] at e₀ e₁
  have hl : D l = k3 W l * (u₀ - u₃) := by
    apply mul_left_cancel₀ (sub_ne_zero.2 hne)
    linear_combination e₀ - e₁ + (third_eqn h₀ h₁ hne h₃).2
  have hn : D n = -(u₁ * (k3 W l * (u₀ - u₃))) := by
    rw [← hl]; linear_combination e₁
  obtain ⟨h1, h2, h3, h4, h6⟩ := hD
  have hk3 : D (k3 W l) = (W.a₂ + 2 * W.a₄ * l + 3 * W.a₆ * l ^ 2) * D l := by
    simp only [k3, map_add, Derivation.leibniz, Derivation.leibniz_pow, h2, h4, h6,
      smul_eq_mul, nsmul_eq_mul, Derivation.map_one_eq_zero]
    push_cast
    ring
  have hk2 : D (k2 W l n) = (W.a₁ + 2 * W.a₃ * l + 2 * W.a₄ * n + 6 * W.a₆ * l * n) * D l +
      (W.a₂ + 2 * W.a₄ * l + 3 * W.a₆ * l ^ 2) * D n := by
    simp only [k2, map_add, Derivation.leibniz, Derivation.leibniz_pow, h1, h2, h3, h4, h6,
      smul_eq_mul, nsmul_eq_mul, der_two, der_three]
    push_cast
    ring
  have := congrArg D h₃
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul, d₀, d₁, hk3, hk2, hl, hn] at this
  apply mul_left_cancel₀ hk
  generalize k3 W l = κ at *
  simp only [fu] at *
  linear_combination this

theorem neg_eqn [IsDomain A] {W : WeierstrassCurve A} {u w s t : A} (h : eqn W u w = 0)
    (hN : 1 - W.a₁ * u - W.a₃ * w ≠ 0)
    (hs : (1 - W.a₁ * u - W.a₃ * w) * s = -u) (ht : (1 - W.a₁ * u - W.a₃ * w) * t = -w) :
    eqn W s t = 0 := by
  apply mul_left_cancel₀ (pow_ne_zero 3 hN)
  set N := 1 - W.a₁ * u - W.a₃ * w with hNd
  have : N ^ 3 * eqn W s t = (N * s) ^ 3 + W.a₁ * (N * s) * (N * t) * N + W.a₂ * (N * s) ^ 2 * (N * t)
      + W.a₃ * (N * t) ^ 2 * N + W.a₄ * (N * s) * (N * t) ^ 2 + W.a₆ * (N * t) ^ 3 - (N * t) * N ^ 2 := by
    simp only [eqn]; ring
  rw [this, hs, ht, hNd]
  simp only [eqn] at h
  linear_combination -h

theorem neg_flow [IsDomain A] {D : Derivation R A A} {W : WeierstrassCurve A} (hD : Const D W)
    {u w s t : A} (h : eqn W u w = 0) (hN : 1 - W.a₁ * u - W.a₃ * w ≠ 0)
    (hs : (1 - W.a₁ * u - W.a₃ * w) * s = -u) (ht : (1 - W.a₁ * u - W.a₃ * w) * t = -w)
    (j : fu W u w ≠ 0) (d : D u = -fu W u w) : D s = fu W s t := by
  have e : D w = -fw W u w := by
    apply mul_left_cancel₀ j
    rw [der_eqn hD h, d]; ring
  obtain ⟨h1, h2, h3, h4, h6⟩ := hD
  have h' := congrArg D hs
  simp only [map_sub, map_neg, Derivation.leibniz, smul_eq_mul, d, e, h1, h3,
    Derivation.map_one_eq_zero] at h'
  apply mul_left_cancel₀ (pow_ne_zero 2 hN)
  set N := 1 - W.a₁ * u - W.a₃ * w with hNd
  have : N ^ 2 * fu W s t = N ^ 2 - W.a₁ * (N * s) * N - W.a₂ * (N * s) ^ 2
      - 2 * W.a₃ * (N * t) * N - 2 * W.a₄ * (N * s) * (N * t) - 3 * W.a₆ * (N * t) ^ 2 := by
    simp only [fu]; ring
  rw [this, hs, ht]
  have h2 : N ^ 2 * D s = N * fu W u w + u * (W.a₁ * fu W u w + W.a₃ * fw W u w) := by
    linear_combination N * h' - (W.a₁ * fu W u w + W.a₃ * fw W u w) * hs
  rw [h2, hNd]
  simp only [eqn, fu, fw] at *
  linear_combination 3 * W.a₃ * h

end Algebra

section Series

open MvPowerSeries

variable {R : Type} [CommRing R] {σ : Type}

theorem eqn_sub {A : Type} [CommRing A] {W : WeierstrassCurve A} {u₀ w₀ u₁ w₁ : A}
    (h₀ : eqn W u₀ w₀ = 0) (h₁ : eqn W u₁ w₁ = 0) :
    (1 - W.a₁ * u₁ - W.a₂ * u₁ ^ 2 - W.a₃ * (w₀ + w₁) - W.a₄ * u₁ * (w₀ + w₁)
      - W.a₆ * (w₀ ^ 2 + w₀ * w₁ + w₁ ^ 2)) * (w₀ - w₁) =
    (u₀ ^ 2 + u₀ * u₁ + u₁ ^ 2 + W.a₁ * w₀ + W.a₂ * (u₀ + u₁) * w₀ + W.a₄ * w₀ ^ 2) * (u₀ - u₁) := by
  simp only [eqn] at *
  linear_combination h₁ - h₀

theorem eqn_unique {W : WeierstrassCurve (MvPowerSeries σ R)} {u w w' : MvPowerSeries σ R}
    (hu : constantCoeff u = 0) (hw : constantCoeff w = 0) (hw' : constantCoeff w' = 0)
    (h : eqn W u w = 0) (h' : eqn W u w' = 0) : w = w' := by
  have := eqn_sub h h'
  rw [sub_self, mul_zero, IsUnit.mul_right_eq_zero, sub_eq_zero] at this
  · exact this
  · rw [isUnit_iff_constantCoeff]
    simp [hu, hw, hw']

theorem cc_fu {W : WeierstrassCurve (MvPowerSeries σ R)} {u w : MvPowerSeries σ R}
    (hu : constantCoeff u = 0) (hw : constantCoeff w = 0) : constantCoeff (fu W u w) = 1 := by
  simp [fu, hu, hw]

theorem ne_zero_of_cc [Nontrivial R] {f : MvPowerSeries σ R} (h : constantCoeff f = 1) : f ≠ 0 := by
  rintro rfl
  simp at h

theorem exists_div {a b : MvPowerSeries σ R} (ha : constantCoeff a = 1) (hb : constantCoeff b = 0) :
    ∃ c, constantCoeff c = 0 ∧ a * c = b := by
  have hu : IsUnit a := by rw [isUnit_iff_constantCoeff, ha]; exact isUnit_one
  obtain ⟨c, hc⟩ := hu.dvd (a := b)
  refine ⟨c, ?_, hc.symm⟩
  have := congrArg constantCoeff hc
  simpa [ha, hb] using this.symm

abbrev up (σ : Type) (W : WeierstrassCurve R) : WeierstrassCurve (MvPowerSeries σ R) :=
  W.map (C : R →+* MvPowerSeries σ R)

theorem const_smul_pderiv (W : WeierstrassCurve R) (a : MvPowerSeries σ R) (i : σ) :
    Const (a • pderiv R i) (up σ W) := by
  simp [Const, pderiv_C]

theorem eqn_subst (W : WeierstrassCurve R) {g : MvPowerSeries σ R} (hg : constantCoeff g = 0)
    (a b : PowerSeries R) :
    PowerSeries.subst g (eqn (W.map PowerSeries.C) a b) =
      eqn (up σ W) (PowerSeries.subst g a) (PowerSeries.subst g b) ∧
    PowerSeries.subst g (fu (W.map PowerSeries.C) a b) =
      fu (up σ W) (PowerSeries.subst g a) (PowerSeries.subst g b) := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero hg
  have hW : (W.map PowerSeries.C).map (PowerSeries.substAlgHom (R := R) hs).toRingHom = up σ W := by
    rw [WeierstrassCurve.map_map]
    congr 1
    ext1 r
    simp [PowerSeries.coe_substAlgHom, PowerSeries.subst_C]
  have h1 := map_eqn (PowerSeries.substAlgHom (R := R) hs).toRingHom (W.map PowerSeries.C) a b
  have h2 := map_fu (PowerSeries.substAlgHom (R := R) hs).toRingHom (W.map PowerSeries.C) a b
  rw [hW] at h1 h2
  simpa [PowerSeries.coe_substAlgHom] using And.intro h1 h2

theorem exists_law [IsDomain R] (W : WeierstrassCurve R) :
    ∃ (F G : MvPowerSeries (Fin 2) R) (w : Fin 2 → MvPowerSeries (Fin 2) R),
      constantCoeff F = 0 ∧ constantCoeff G = 0 ∧ eqn (up _ W) F G = 0 ∧
      ∀ i, constantCoeff (w i) = 0 ∧ eqn (up _ W) (X i) (w i) = 0 ∧
        fu (up _ W) (X i) (w i) * pderiv R i F = fu (up _ W) F G := by
  haveI : IsDomain (MvPowerSeries (Fin 2) R) := NoZeroDivisors.to_isDomain _
  set V := up (Fin 2) W with hV
  have hw : ∀ i : Fin 2, ∃ w : MvPowerSeries (Fin 2) R, constantCoeff w = 0 ∧ eqn V (X i) w = 0 := by
    intro i
    have hX : constantCoeff (X i : MvPowerSeries (Fin 2) R) = 0 := constantCoeff_X i
    refine ⟨PowerSeries.subst (X i) (GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer W),
      PowerSeries.constantCoeff_subst_eq_zero hX _ (by simp [GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer]), ?_⟩
    have h0 : eqn (W.map PowerSeries.C) PowerSeries.X (GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer W) = 0 := by
      have := GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer_eq W
      simp only [eqn, WeierstrassCurve.map]
      linear_combination -this
    have hs := PowerSeries.HasSubst.of_constantCoeff_zero hX
    have := (eqn_subst W hX PowerSeries.X (GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer W)).1
    rw [h0, PowerSeries.subst_X hs, ← PowerSeries.coe_substAlgHom hs, map_zero,
      PowerSeries.coe_substAlgHom] at this
    exact this.symm
  choose w hw0 hwe using hw
  obtain ⟨l, hl0, hl⟩ := exists_div
    (a := 1 - V.a₁ * X 1 - V.a₂ * X 1 ^ 2 - V.a₃ * (w 0 + w 1) - V.a₄ * X 1 * (w 0 + w 1)
      - V.a₆ * (w 0 ^ 2 + w 0 * w 1 + w 1 ^ 2))
    (b := X 0 ^ 2 + X 0 * X 1 + X 1 ^ 2 + V.a₁ * w 0 + V.a₂ * (X 0 + X 1) * w 0 + V.a₄ * w 0 ^ 2)
    (by simp [hw0]) (by simp only [map_add, map_mul, map_pow, hw0, constantCoeff_X]; ring)
  have hsl : w 0 - w 1 = l * (X 0 - X 1) := by
    have := eqn_sub (hwe 0) (hwe 1)
    rw [← hl] at this
    refine mul_left_cancel₀ ?_ (this.trans (mul_assoc _ _ _))
    exact ne_zero_of_cc (by simp [hw0])
  set n := w 1 - l * X 1 with hn
  have hn0 : constantCoeff n = 0 := by simp [hn, hw0]
  have e : ∀ i, w i = l * X i + n := by
    intro i
    fin_cases i
    · simp only [Fin.zero_eta]; rw [hn]; linear_combination hsl
    · simp only [Fin.mk_one]; rw [hn]; ring
  have hk : constantCoeff (k3 V l) = 1 := by simp [k3, hl0]
  obtain ⟨u, hu0, hu⟩ := exists_div (b := -(k3 V l * (X 0 + X 1)) - k2 V l n) hk
    (by simp [k2, hl0, hn0])
  have hne : (X 0 : MvPowerSeries (Fin 2) R) ≠ X 1 := by
    intro h
    have := congrArg (pderiv R 0) h
    simp [pderiv_X_of_ne] at this
  have he : ∀ i, eqn V (X i) (l * X i + n) = 0 := fun i => e i ▸ hwe i
  have hj : ∀ i, fu V (X i) (l * X i + n) ≠ 0 := fun i =>
    ne_zero_of_cc (cc_fu (by simp) (by simp [hn0]))
  have h3 := (third_eqn (he 0) (he 1) hne hu).1
  have hN : constantCoeff (1 - V.a₁ * u - V.a₃ * (l * u + n)) = 1 := by simp [hu0, hn0]
  obtain ⟨F, hF0, hF⟩ := exists_div (b := -u) hN (by simp [hu0])
  obtain ⟨G, hG0, hG⟩ := exists_div (b := -(l * u + n)) hN (by simp [hu0, hn0])
  have j3 : fu V u (l * u + n) ≠ 0 := ne_zero_of_cc (cc_fu hu0 (by simp [hu0, hn0]))
  refine ⟨F, G, w, hF0, hG0, neg_eqn h3 (ne_zero_of_cc hN) hF hG, fun i => ⟨hw0 i, hwe i, ?_⟩⟩
  have hC := const_smul_pderiv W (fu V (X i) (w i)) i
  have := neg_flow hC h3 (ne_zero_of_cc hN) hF hG j3 ?_
  · simpa using this
  have d : ∀ i, (fu V (X i) (w i) • pderiv R i) (X i) = fu V (X i) (l * X i + n) := by
    intro i; rw [← e]; simp
  fin_cases i
  · refine third_flow hC (he 0) (he 1) hne hu (ne_zero_of_cc hk) (hj 0) (hj 1) ?_ ?_
    · exact d 0
    · simp [pderiv_X_of_ne]
  · refine third_flow hC (he 1) (he 0) hne.symm (by rw [hu, add_comm]) (ne_zero_of_cc hk)
      (hj 1) (hj 0) ?_ ?_
    · exact d 1
    · simp [pderiv_X_of_ne]

end Series

section Log

open MvPowerSeries

variable {k : Type} [CommRing k] {σ τ : Type}

theorem subst_psubst {a : σ → MvPowerSeries τ k} (ha : HasSubst a) {g : MvPowerSeries σ k}
    (hg : constantCoeff g = 0) (f : PowerSeries k) :
    subst a (PowerSeries.subst g f) = PowerSeries.subst (subst a g) f := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero hg
  rw [PowerSeries.subst, subst_comp_subst_apply hs.const ha]
  rfl

theorem psubst_psubst {g : MvPowerSeries σ k} (hg : constantCoeff g = 0) {a : PowerSeries k}
    (ha : PowerSeries.constantCoeff a = 0) (f : PowerSeries k) :
    PowerSeries.subst g (PowerSeries.subst a f) = PowerSeries.subst (PowerSeries.subst g a) f :=
  PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' ha)
    (PowerSeries.HasSubst.of_constantCoeff_zero hg) f

theorem hasSubst_two {g₀ g₁ : MvPowerSeries σ k} (h₀ : constantCoeff g₀ = 0) (h₁ : constantCoeff g₁ = 0) :
    HasSubst ![g₀, g₁] :=
  hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simpa

theorem subst_eq_of_log {U ℓ : PowerSeries k} (hℓ : PowerSeries.constantCoeff ℓ = 0)
    (hUℓ : PowerSeries.subst ℓ U = PowerSeries.X (R := k)) {F : MvPowerSeries (Fin 2) k}
    (hF : constantCoeff F = 0)
    (h : PowerSeries.subst F ℓ = PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) ℓ +
      PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) k) ℓ)
    {g₀ g₁ : MvPowerSeries σ k} (h₀ : constantCoeff g₀ = 0) (h₁ : constantCoeff g₁ = 0) :
    subst ![g₀, g₁] F = PowerSeries.subst (PowerSeries.subst g₀ ℓ + PowerSeries.subst g₁ ℓ) U := by
  have ha := hasSubst_two h₀ h₁
  have e : F = PowerSeries.subst (PowerSeries.subst F ℓ) U := by
    rw [← psubst_psubst hF hℓ, hUℓ, PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hF)]
  have c0 : ∀ i, constantCoeff (PowerSeries.subst (X i : MvPowerSeries (Fin 2) k) ℓ) = 0 := fun i =>
    PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X i) _ hℓ
  rw [e, h, subst_psubst ha (by simp [c0]), subst_add ha, subst_psubst ha (constantCoeff_X 0),
    subst_psubst ha (constantCoeff_X 1), subst_X ha, subst_X ha]
  rfl

theorem assoc_of_log {U ℓ : PowerSeries k} (hU : PowerSeries.constantCoeff U = 0)
    (hℓ : PowerSeries.constantCoeff ℓ = 0)
    (hUℓ : PowerSeries.subst ℓ U = PowerSeries.X (R := k))
    (hℓU : PowerSeries.subst U ℓ = PowerSeries.X (R := k)) {F : MvPowerSeries (Fin 2) k}
    (hF : constantCoeff F = 0)
    (h : PowerSeries.subst F ℓ = PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) ℓ +
      PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) k) ℓ) :
    subst ![subst ![(X 0 : MvPowerSeries (Fin 3) k), X 1] F, X 2] F =
      subst ![(X 0 : MvPowerSeries (Fin 3) k), subst ![(X 1 : MvPowerSeries (Fin 3) k), X 2] F] F := by
  have c0 : ∀ i, constantCoeff (PowerSeries.subst (X i : MvPowerSeries (Fin 3) k) ℓ) = 0 := fun i =>
    PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X i) _ hℓ
  have key : ∀ i j : Fin 3, constantCoeff (subst ![(X i : MvPowerSeries (Fin 3) k), X j] F) = 0 ∧
      PowerSeries.subst (subst ![(X i : MvPowerSeries (Fin 3) k), X j] F) ℓ =
        PowerSeries.subst (X i : MvPowerSeries (Fin 3) k) ℓ +
          PowerSeries.subst (X j : MvPowerSeries (Fin 3) k) ℓ := by
    intro i j
    have hz : constantCoeff (PowerSeries.subst (X i : MvPowerSeries (Fin 3) k) ℓ +
          PowerSeries.subst (X j : MvPowerSeries (Fin 3) k) ℓ) = 0 := by simp [c0]
    rw [subst_eq_of_log hℓ hUℓ hF h (constantCoeff_X i) (constantCoeff_X j)]
    refine ⟨PowerSeries.constantCoeff_subst_eq_zero hz _ hU, ?_⟩
    rw [← psubst_psubst hz hU, hℓU, PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hz)]
  rw [subst_eq_of_log hℓ hUℓ hF h (key 0 1).1 (constantCoeff_X 2),
    subst_eq_of_log hℓ hUℓ hF h (constantCoeff_X 0) (key 1 2).1, (key 0 1).2, (key 1 2).2, add_assoc]

theorem log_deriv {W : WeierstrassCurve k} {U V ℓ : PowerSeries k} {c : k}
    (hV : PowerSeries.constantCoeff V = 0)
    (hℓ : PowerSeries.constantCoeff ℓ = 0)
    (hUℓ : PowerSeries.subst ℓ U = PowerSeries.X (R := k))
    (he : eqn (W.map PowerSeries.C) U V = 0)
    (hd : PowerSeries.derivative k U = PowerSeries.C c * fu (W.map PowerSeries.C) U V)
    {s t : MvPowerSeries σ k} (hs : constantCoeff s = 0) (ht : constantCoeff t = 0)
    (hst : eqn (up σ W) s t = 0) :
    PowerSeries.subst s (PowerSeries.derivative k ℓ) * (C c * fu (up σ W) s t) = 1 := by
  have Hs := PowerSeries.HasSubst.of_constantCoeff_zero hs
  have Hℓ := PowerSeries.HasSubst.of_constantCoeff_zero' hℓ
  have hg : constantCoeff (PowerSeries.subst s ℓ) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hs _ hℓ
  have Hg := PowerSeries.HasSubst.of_constantCoeff_zero hg
  have eU : PowerSeries.subst (PowerSeries.subst s ℓ) U = s := by
    rw [← psubst_psubst hs hℓ, hUℓ, PowerSeries.subst_X Hs]
  obtain ⟨e1, e2⟩ := eqn_subst W hg U V
  rw [he, eU, ← PowerSeries.coe_substAlgHom Hg, map_zero, PowerSeries.coe_substAlgHom] at e1
  have eV : PowerSeries.subst (PowerSeries.subst s ℓ) V = t :=
    eqn_unique hs (PowerSeries.constantCoeff_subst_eq_zero hg _ hV) ht e1.symm hst
  rw [eU, eV] at e2
  have d1 := congrArg (PowerSeries.derivative k) hUℓ
  rw [PowerSeries.derivative_subst Hℓ, PowerSeries.derivative_X] at d1
  have d2 := congrArg (PowerSeries.subst s) d1
  rw [PowerSeries.subst_mul Hs, psubst_psubst hs hℓ, hd, PowerSeries.subst_mul Hg, e2,
    PowerSeries.subst_C, ← PowerSeries.coe_substAlgHom Hs, map_one, PowerSeries.coe_substAlgHom] at d2
  rw [mul_comm]
  exact d2

theorem log_law [IsAddTorsionFree k] {W : WeierstrassCurve k} {U V ℓ : PowerSeries k} {c : k}
    (hV : PowerSeries.constantCoeff V = 0)
    (hℓ : PowerSeries.constantCoeff ℓ = 0)
    (hUℓ : PowerSeries.subst ℓ U = PowerSeries.X (R := k))
    (he : eqn (W.map PowerSeries.C) U V = 0)
    (hd : PowerSeries.derivative k U = PowerSeries.C c * fu (W.map PowerSeries.C) U V)
    {F G : MvPowerSeries (Fin 2) k} {w : Fin 2 → MvPowerSeries (Fin 2) k}
    (hF : constantCoeff F = 0) (hG : constantCoeff G = 0) (hFG : eqn (up _ W) F G = 0)
    (hw : ∀ i, constantCoeff (w i) = 0 ∧ eqn (up _ W) (X i) (w i) = 0 ∧
        fu (up _ W) (X i) (w i) * pderiv k i F = fu (up _ W) F G) :
    PowerSeries.subst F ℓ = PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) ℓ +
      PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) k) ℓ := by
  have HX : ∀ i, PowerSeries.HasSubst (X i : MvPowerSeries (Fin 2) k) := fun i =>
    PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_X i)
  refine GlobalTheory.FormalCalc.ext_of_pderiv_of_coeff (e := id) (fun i => ?_) (fun α hα => ?_)
  · have a1 := log_deriv hV hℓ hUℓ he hd hF hG hFG
    have a2 := log_deriv hV hℓ hUℓ he hd (constantCoeff_X i) (hw i).1 (hw i).2.1
    have a3 := (hw i).2.2
    have a4 : pderiv k i (PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) ℓ +
      PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) k) ℓ) =
        PowerSeries.subst (X i : MvPowerSeries (Fin 2) k) (PowerSeries.derivative k ℓ) := by
      rw [map_add, GlobalTheory.FormalCalc.pderiv_powerSeries_subst (HX 0),
        GlobalTheory.FormalCalc.pderiv_powerSeries_subst (HX 1)]
      fin_cases i <;> simp [pderiv_X_of_ne]
    rw [id, a4, GlobalTheory.FormalCalc.pderiv_powerSeries_subst (PowerSeries.HasSubst.of_constantCoeff_zero hF)]
    set p := PowerSeries.subst F (PowerSeries.derivative k ℓ)
    set r := PowerSeries.subst (X i : MvPowerSeries (Fin 2) k) (PowerSeries.derivative k ℓ)
    linear_combination r * a1 - p * pderiv k i F * a2 + p * r * C c * a3
  · have : α = 0 := Finsupp.ext hα
    subst this
    simp only [coeff_zero_eq_constantCoeff_apply, map_add]
    rw [PowerSeries.constantCoeff_subst_eq_zero hF _ hℓ,
      PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X 0) _ hℓ,
      PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X 1) _ hℓ, add_zero]

end Log

section Main

open MvPowerSeries

theorem exists_formalGroup {R k : Type} [CommRing R] [IsDomain R] [Field k] [CharZero k] (φ : R →+* k)
    (hφ : Function.Injective φ) (W : WeierstrassCurve R) {U V : PowerSeries k} {c : k} (hc : c ≠ 0)
    (hU : PowerSeries.constantCoeff U = 0) (hV : PowerSeries.constantCoeff V = 0)
    (he : eqn ((W.map φ).map PowerSeries.C) U V = 0)
    (hd : PowerSeries.derivative k U = PowerSeries.C c * fu ((W.map φ).map PowerSeries.C) U V) :
    ∃ F : FormalGroup R,
      subst ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) U,
        PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) k) U] (map φ F.toPowerSeries) =
      PowerSeries.subst (X 0 + X 1 : MvPowerSeries (Fin 2) k) U := by
  obtain ⟨F, G, w, hF, hG, hFG, hw⟩ := exists_law W
  have h1 : IsUnit (PowerSeries.coeff 1 U) := by
    have := congrArg PowerSeries.constantCoeff hd
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative] at this
    simp [fu, hU, hV] at this
    rw [this]
    exact hc.isUnit
  set ℓ := U.substInvOfIsUnit h1
  have hℓ : PowerSeries.constantCoeff ℓ = 0 := PowerSeries.constantCoeff_substInvOfIsUnit U h1
  have hUℓ : PowerSeries.subst ℓ U = PowerSeries.X (R := k) :=
    PowerSeries.subst_substInvOfIsUnit_right U hU h1
  have hℓU : PowerSeries.subst U ℓ = PowerSeries.X (R := k) :=
    PowerSeries.subst_substInvOfIsUnit_left U hU h1
  have hup : (up (Fin 2) W).map (map φ) = up (Fin 2) (W.map φ) := by
    simp only [WeierstrassCurve.map_map]
    congr 1
    ext1 r
    simp
  have hF' : constantCoeff (map φ F) = 0 := by rw [constantCoeff_map, hF, map_zero]
  have hlog := log_law (W := W.map φ) hV hℓ hUℓ he hd (F := map φ F) (G := map φ G)
    (w := fun i => map φ (w i)) hF' (by rw [constantCoeff_map, hG, map_zero])
    (by rw [← hup, ← map_eqn, hFG, map_zero]) (fun i => by
      obtain ⟨a1, a2, a3⟩ := hw i
      refine ⟨by rw [constantCoeff_map, a1, map_zero], ?_, ?_⟩
      · rw [← hup, ← map_X φ, ← map_eqn, a2, map_zero]
      · rw [← hup, ← map_X φ, ← map_fu, ← map_fu, GlobalTheory.FormalCalc.pderiv_map, ← map_mul, a3])
  have hlin : ∀ i, coeff (Finsupp.single i 1) F = 1 := by
    intro i
    obtain ⟨a1, -, a3⟩ := hw i
    have := congrArg constantCoeff a3
    rw [map_mul, cc_fu (constantCoeff_X i) a1, cc_fu hF hG, one_mul,
      ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv] at this
    simpa using this
  have hinj : Function.Injective (map φ : MvPowerSeries (Fin 3) R → MvPowerSeries (Fin 3) k) := by
    intro a b h
    ext d
    apply hφ
    simpa using congrArg (coeff d) h
  refine ⟨⟨F, hF, hlin 0, hlin 1, hinj ?_⟩, ?_⟩
  · have e (g₁ g₂ : MvPowerSeries (Fin 3) R) :
        (fun i => (![g₁, g₂] i).map φ) = ![g₁.map φ, g₂.map φ] := by
      ext1 i; fin_cases i <;> simp
    rw [map_subst (HasSubst.cons_subst_zero_left (0 : Fin 3) 1 2 hF),
      map_subst (HasSubst.cons_subst_zero_right (0 : Fin 3) 1 2 hF), e, e,
      map_subst HasSubst.X_X, map_subst HasSubst.X_X, e, e]
    simp only [map_X]
    exact assoc_of_log hU hℓ hUℓ hℓU hF' hlog
  · have c0 : ∀ i, constantCoeff (PowerSeries.subst (X i : MvPowerSeries (Fin 2) k) U) = 0 := fun i =>
      PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X i) _ hU
    have c1 : ∀ i, PowerSeries.subst (PowerSeries.subst (X i : MvPowerSeries (Fin 2) k) U) ℓ =
        (X i : MvPowerSeries (Fin 2) k) := fun i => by
      rw [← psubst_psubst (constantCoeff_X i) hU, hℓU,
        PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_X i))]
    rw [subst_eq_of_log hℓ hUℓ hF' hlog (c0 0) (c0 1), c1, c1]

end Main

section Model

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

def anRing : Subring (ℂ → ℂ) where
  carrier := {f | AnalyticAt ℂ f 0}
  mul_mem' ha hb := AnalyticAt.mul ha hb
  one_mem' := analyticAt_const
  add_mem' ha hb := AnalyticAt.add ha hb
  zero_mem' := analyticAt_const
  neg_mem' ha := AnalyticAt.neg ha

def anConst : ℂ →+* anRing where
  toFun c := ⟨fun _ => c, analyticAt_const⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable {q : ℕ} [Fact q.Prime]

def tayHom (ι : ℂ ≃+* ℂ_[q]) : anRing →+* ℂ_[q]⟦X⟧ where
  toFun f := hat ι X f
  map_one' := by
    exact ((TaylorRead.hat_laws q ι X constantCoeff_X).2.1 1).trans (by simp)
  map_mul' a b := ((TaylorRead.hat_laws q ι X constantCoeff_X).1 a b a.2 b.2).2.1
  map_zero' := by
    exact ((TaylorRead.hat_laws q ι X constantCoeff_X).2.1 0).trans (by simp)
  map_add' a b := ((TaylorRead.hat_laws q ι X constantCoeff_X).1 a b a.2 b.2).1

theorem series_flow (M : Mdl q) (h : M.Ok) :
    constantCoeff (hat M.ι X M.u) = 0 ∧ constantCoeff (hat M.ι X M.w) = 0 ∧
    eqn (M.W.map C) (hat M.ι X M.u) (hat M.ι X M.w) = 0 ∧
    derivative ℂ_[q] (hat M.ι X M.u) = C (M.ι M.c) * fu (M.W.map C) (hat M.ι X M.u) (hat M.ι X M.w) := by
  obtain ⟨-, -, -, -, u0, w0, -, -, hs⟩ := uw_elliptic_flow q M h
  obtain ⟨au, aw, -, -, -, hev⟩ := hs 0 (Or.inl M.L.lattice.zero_mem)
  obtain ⟨l1, l2, -, l4, l5, -⟩ := TaylorRead.hat_laws q M.ι X constantCoeff_X
  set V : WeierstrassCurve anRing := M.W.map (anConst.comp (M.ι.symm : ℂ_[q] →+* ℂ)) with hV
  have hc : ∀ c, tayHom M.ι (anConst c) = C (M.ι c) := l2
  have hmap : V.map (tayHom M.ι) = M.W.map C := by
    rw [hV, WeierstrassCurve.map_map]
    congr 1
    ext1 r
    simp [hc]
  have e1 := map_eqn (tayHom M.ι) V ⟨M.u, au⟩ ⟨M.w, aw⟩
  have e2 := map_fu (tayHom M.ι) V ⟨M.u, au⟩ ⟨M.w, aw⟩
  rw [hmap] at e1 e2
  refine ⟨by rw [l4, u0, map_zero], by rw [l4, w0, map_zero], ?_, ?_⟩
  · refine e1.symm.trans (Eq.trans ?_ (map_zero (tayHom M.ι)))
    refine (l1 _ _ (eqn V ⟨M.u, au⟩ ⟨M.w, aw⟩).2 (0 : anRing).2).2.2.1 ?_
    filter_upwards [nhdsWithin_le_nhds hev] with z hz
    have := hz.1
    simp [eqn, hV, anConst]
    linear_combination -this
  · rw [l5 _ au, derivative_X, one_mul, ← hc]
    refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg _ e2))
    refine (l1 _ _ au.deriv (anConst M.c * fu V ⟨M.u, au⟩ ⟨M.w, aw⟩).2).2.2.1 ?_
    filter_upwards [nhdsWithin_le_nhds hev] with z hz
    exact hz.2.1

theorem exists_formalGroup_add : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q), M.Ok → IsAlgebraic ℚ M.W.a₁ → IsAlgebraic ℚ M.W.a₂ → IsAlgebraic ℚ M.W.a₃ → IsAlgebraic ℚ M.W.a₄ → IsAlgebraic ℚ M.W.a₆ → ∃ F : FormalGroup 𝓞_ℂ_[q], (∃ K : IntermediateField ℚ_[q] ℂ_[q], FiniteDimensional ℚ_[q] K ∧ ∀ m : Fin 2 →₀ ℕ, ((MvPowerSeries.coeff m F.toPowerSeries : 𝓞_ℂ_[q]) : ℂ_[q]) ∈ K) ∧ MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[q]) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)), PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u))] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[q]) (MvPowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F.toPowerSeries) = PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)) := by
  intro q _ M h b₁ b₂ b₃ b₄ b₆
  obtain ⟨hU, hV, he, hd⟩ := series_flow M h
  obtain ⟨hc, n₁, n₂, n₃, n₄, n₆, -⟩ := h
  let S : Set ℂ_[q] := {M.W.a₁, M.W.a₂, M.W.a₃, M.W.a₄, M.W.a₆}
  let K : IntermediateField ℚ_[q] ℂ_[q] := IntermediateField.adjoin ℚ_[q] S
  have hK : FiniteDimensional ℚ_[q] K := by
    haveI : Finite S := by simp only [S]; infer_instance
    refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
    have : IsAlgebraic ℚ x := by
      simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
    exact (this.extendScalars (algebraMap ℚ ℚ_[q]).injective).isIntegral
  let R : Subring 𝓞_ℂ_[q] := K.toSubring.comap (algebraMap 𝓞_ℂ_[q] ℂ_[q])
  have hO : ∀ x : ℂ_[q], ‖x‖ ≤ 1 → x ∈ 𝓞_ℂ_[q] := fun x hx => by
    rw [PadicComplex.norm_eq_norm] at hx
    rw [PadicComplexInt, Valuation.mem_valuationSubring_iff]
    exact Valued.toNormedField.norm_le_one_iff.1 hx
  have hS : ∀ x ∈ S, x ∈ K := fun x hx => IntermediateField.subset_adjoin _ _ hx
  let W₀ : WeierstrassCurve R :=
    ⟨⟨⟨_, hO _ n₁⟩, hS _ (by simp [S])⟩, ⟨⟨_, hO _ n₂⟩, hS _ (by simp [S])⟩,
      ⟨⟨_, hO _ n₃⟩, hS _ (by simp [S])⟩, ⟨⟨_, hO _ n₄⟩, hS _ (by simp [S])⟩,
      ⟨⟨_, hO _ n₆⟩, hS _ (by simp [S])⟩⟩
  let φ : R →+* ℂ_[q] := (algebraMap 𝓞_ℂ_[q] ℂ_[q]).comp R.subtype
  have hφ : Function.Injective φ := Subtype.val_injective.comp Subtype.val_injective
  have hW : W₀.map φ = M.W := rfl
  obtain ⟨F, hF⟩ := exists_formalGroup φ hφ W₀ (c := M.ι M.c) (by simpa using hc) hU hV
    (hW ▸ he) (hW ▸ hd)
  refine ⟨F.map R.subtype, ⟨K, hK, fun m => (MvPowerSeries.coeff m F.toPowerSeries).2⟩, ?_⟩
  simp only [hat, X_subst] at hF
  exact hF

end Model

end GlobalTheory.MomOne.ChordLaw
end
end

section
section
noncomputable section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.SplitChart

open ChordLaw

section Algebra

variable {k : Type} [CommRing k] {σ : Type}

theorem law_two {U : k⟦X⟧} (hU : constantCoeff U = 0) {F : MvPowerSeries (Fin 2) k}
    (H : MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) U,
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) U] : Fin 2 → MvPowerSeries (Fin 2) k) F =
      PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) U)
    {a b : MvPowerSeries σ k} (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.subst (![PowerSeries.subst a U, PowerSeries.subst b U] : Fin 2 → MvPowerSeries σ k) F =
      PowerSeries.subst (a + b) U := by
  have hab := hasSubst_two ha hb
  have c0 : ∀ i, MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) k) U) = 0 :=
    fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ hU
  have h := congrArg (MvPowerSeries.subst ![a, b]) H
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_two (c0 0) (c0 1)) hab, subst_psubst hab (by simp),
    MvPowerSeries.subst_add hab, MvPowerSeries.subst_X hab, MvPowerSeries.subst_X hab] at h
  refine Eq.trans ?_ h
  congr 1
  funext i
  fin_cases i
  · simp [subst_psubst hab (MvPowerSeries.constantCoeff_X 0), MvPowerSeries.subst_X hab]
  · simp [subst_psubst hab (MvPowerSeries.constantCoeff_X 1), MvPowerSeries.subst_X hab]

theorem constantCoeff_mulN {R : Type} [CommRing R] (F : FormalGroup R) (n : ℕ) :
    constantCoeff (JetMomFound.mulN F n) = 0 := by
  induction n with
  | zero => simp [JetMomFound.mulN]
  | succ n ih =>
    refine MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_two ih constantCoeff_X) ?_ F.zero_constantCoeff
    intro i
    fin_cases i
    · exact ih
    · exact constantCoeff_X

theorem map_mulN {R : Type} [CommRing R] (φ : R →+* k) (F : FormalGroup R) {U ℓ : k⟦X⟧}
    (hU : constantCoeff U = 0) (hℓ : constantCoeff ℓ = 0) (hUℓ : PowerSeries.subst ℓ U = (X : k⟦X⟧))
    (H : MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) U,
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) U] : Fin 2 → MvPowerSeries (Fin 2) k)
      (MvPowerSeries.map φ F.toPowerSeries) =
      PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) U) (n : ℕ) :
    PowerSeries.map φ (JetMomFound.mulN F n) = PowerSeries.subst (C (n : k) * ℓ) U := by
  induction n with
  | zero =>
    simp only [JetMomFound.mulN, map_zero, Nat.cast_zero, zero_mul]
    exact (PowerSeries.subst_zero_of_constantCoeff_zero hU).symm
  | succ n ih =>
    have h := law_two hU H (a := (C (n : k) * ℓ : k⟦X⟧)) (b := ℓ)
      (show constantCoeff (C (n : k) * ℓ) = 0 by rw [map_mul, hℓ, mul_zero]) hℓ
    have e : (C ((n + 1 : ℕ) : k) * ℓ : k⟦X⟧) = C (n : k) * ℓ + ℓ := by
      rw [Nat.cast_succ, map_add, map_one]; ring
    rw [e]
    refine Eq.trans ?_ h
    rw [← ih, hUℓ]
    refine (MvPowerSeries.map_subst (hasSubst_two (constantCoeff_mulN F n) constantCoeff_X) _).trans ?_
    congr 1
    funext i
    fin_cases i
    · rfl
    · exact PowerSeries.map_X φ

theorem deriv_of_mul {g : k⟦X⟧}
    (H : PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) g =
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) g +
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) g +
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) g *
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) g) :
    derivative k g = C (coeff 1 g) * (1 + g) := by
  have HX : ∀ i, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) k) := fun i =>
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  have HS : PowerSeries.HasSubst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have h := congrArg (MvPowerSeries.pderiv k 1) H
  simp only [map_add, Derivation.leibniz, smul_eq_mul, GlobalTheory.FormalCalc.pderiv_powerSeries_subst (HX _),
    GlobalTheory.FormalCalc.pderiv_powerSeries_subst HS] at h
  have p0 : MvPowerSeries.pderiv k 1 (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) = 0 := by
    simp [MvPowerSeries.pderiv_X_of_ne]
  have p1 : MvPowerSeries.pderiv k 1 (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) = 1 := by simp
  simp only [p0, p1, zero_add, mul_one, mul_zero, add_zero] at h
  have ha : MvPowerSeries.HasSubst (![(X : k⟦X⟧), 0] : Fin 2 → MvPowerSeries Unit k) :=
    hasSubst_two constantCoeff_X (map_zero _)
  have h2 := congrArg (MvPowerSeries.subst (![(X : k⟦X⟧), 0] : Fin 2 → MvPowerSeries Unit k)) h
  rw [subst_psubst ha (by simp), MvPowerSeries.subst_add ha, MvPowerSeries.subst_add ha,
    MvPowerSeries.subst_mul ha, subst_psubst ha (MvPowerSeries.constantCoeff_X 0),
    subst_psubst ha (MvPowerSeries.constantCoeff_X 1), MvPowerSeries.subst_X ha, MvPowerSeries.subst_X ha] at h2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, add_zero] at h2
  have e : PowerSeries.subst (0 : MvPowerSeries Unit k) (derivative k g) = (C (coeff 1 g) : k⟦X⟧) := by
    rw [PowerSeries.subst_zero_eq_C_constantCoeff, MvPowerSeries.map_C, ← coeff_zero_eq_constantCoeff_apply,
      coeff_derivative]
    simp [PowerSeries.C]
  rw [X_subst, X_subst, e] at h2
  rw [h2]
  ring

theorem subst_log_eq_X [IsAddTorsionFree k] {g L : k⟦X⟧} {γ ω : k} (hγ : γ * ω = 1) (hg : constantCoeff g = 0)
    (hd : derivative k g = C γ * (1 + g)) (hL0 : constantCoeff L = 0) (hL : (1 + X) * derivative k L = 1) :
    PowerSeries.subst (C ω * L) g = (X : k⟦X⟧) := by
  have h0 : constantCoeff (C ω * L) = 0 := by rw [map_mul, hL0, mul_zero]
  have Hs := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hh0 : constantCoeff (PowerSeries.subst (C ω * L) g : k⟦X⟧) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero h0 _ hg
  have hD : derivative k (PowerSeries.subst (C ω * L) g : k⟦X⟧) =
      C γ * (1 + PowerSeries.subst (C ω * L) g) * (C ω * derivative k L) := by
    rw [PowerSeries.derivative_subst Hs, hd, PowerSeries.subst_mul Hs, PowerSeries.subst_add Hs,
      PowerSeries.subst_C, ← PowerSeries.coe_substAlgHom Hs, map_one, Derivation.leibniz, derivative_C]
    simp only [smul_eq_mul, mul_zero, add_zero]
    rfl
  generalize (PowerSeries.subst (C ω * L) g : k⟦X⟧) = h at hh0 hD
  have hC : (C γ : k⟦X⟧) * C ω = 1 := by rw [← map_mul, hγ, map_one]
  set r := derivative k L with hr
  have hr' := congrArg (derivative k) hL
  rw [Derivation.leibniz, map_add, derivative_X, Derivation.map_one_eq_zero] at hr'
  simp only [smul_eq_mul] at hr'
  have hr0 : constantCoeff r = 1 := by simpa using congrArg constantCoeff hL
  have key : (1 + h) * r = 1 := by
    apply derivative.ext
    · rw [Derivation.leibniz, map_add, Derivation.map_one_eq_zero, hD]
      simp only [smul_eq_mul]
      linear_combination (1 + h) * r * hr' - (1 + h) * derivative k r * hL + (1 + h) * r ^ 2 * hC
    · simp [hh0, hr0]
  linear_combination (1 + X) * key - (1 + h) * hL

theorem exists_scale {R K : Type} [CommRing R] [Field K] [CharZero K] (φ : R →+* K) (F : FormalGroup R)
    {U ℓ L : K⟦X⟧} (hU : constantCoeff U = 0) (hℓ : constantCoeff ℓ = 0)
    (hUℓ : PowerSeries.subst ℓ U = (X : K⟦X⟧))
    (H : MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) U,
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) U] : Fin 2 → MvPowerSeries (Fin 2) K)
      (MvPowerSeries.map φ F.toPowerSeries) =
      PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) U)
    {f : R⟦X⟧} (hf : JetMomFound.IsIsoGm F f) (hL0 : constantCoeff L = 0) (hL : (1 + X) * derivative K L = 1) :
    ∃ (ω : K) (e : R⟦X⟧), IsUnit (coeff 1 e) ∧ PowerSeries.subst (C ω * L) U = PowerSeries.map φ e := by
  obtain ⟨f0, f1, hf⟩ := hf
  have HX : ∀ i, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) := fun i =>
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  have c0 : ∀ i, MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) f) = 0 :=
    fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ f0
  have cU : ∀ i, MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) U) = 0 :=
    fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ hU
  have ha := hasSubst_two (c0 0) (c0 1)
  have hb := hasSubst_two (cU 0) (cU 1)
  rw [FormalGroup.𝔾ₘ_toPowerSeries, MvPowerSeries.subst_add ha, MvPowerSeries.subst_add ha,
    MvPowerSeries.subst_mul ha, MvPowerSeries.subst_X ha, MvPowerSeries.subst_X ha] at hf
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hf
  have h1 := congrArg (MvPowerSeries.map φ) hf
  rw [map_add, map_add, map_mul,
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff),
    PowerSeries.map_subst (HX 0), PowerSeries.map_subst (HX 1), MvPowerSeries.map_X, MvPowerSeries.map_X] at h1
  set f' := PowerSeries.map φ f with hf'
  have f0' : constantCoeff f' = 0 := by
    rw [hf', ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, f0, map_zero]
  have h2 := congrArg (MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) U,
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) U] : Fin 2 → MvPowerSeries (Fin 2) K)) h1
  rw [subst_psubst hb (by rw [MvPowerSeries.constantCoeff_map, F.zero_constantCoeff, map_zero]), H,
    MvPowerSeries.subst_add hb, MvPowerSeries.subst_add hb, MvPowerSeries.subst_mul hb,
    subst_psubst hb (MvPowerSeries.constantCoeff_X 0), subst_psubst hb (MvPowerSeries.constantCoeff_X 1),
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb] at h2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h2
  rw [← psubst_psubst (by simp) hU, ← psubst_psubst (MvPowerSeries.constantCoeff_X 0) hU,
    ← psubst_psubst (MvPowerSeries.constantCoeff_X 1) hU] at h2
  have hd := deriv_of_mul h2
  have g0 : constantCoeff (PowerSeries.subst U f' : K⟦X⟧) = 0 := PowerSeries.constantCoeff_subst_eq_zero hU _ f0'
  have hγ : coeff 1 (PowerSeries.subst U f' : K⟦X⟧) ≠ 0 := by
    intro hz
    have hg : (PowerSeries.subst U f' : K⟦X⟧) = 0 := by
      apply derivative.ext
      · rw [hd, hz]; simp
      · rw [g0, map_zero]
    have h3 := psubst_psubst (σ := Unit) hℓ hU f'
    rw [hg, hUℓ, X_subst, ← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' hℓ),
      map_zero] at h3
    have h4 := f1.map φ
    rw [← coeff_map, ← hf', ← h3, map_zero] at h4
    exact not_isUnit_zero h4
  have h5 := subst_log_eq_X (mul_inv_cancel₀ hγ) g0 hd hL0 hL
  set ω := (coeff 1 (PowerSeries.subst U f' : K⟦X⟧))⁻¹
  have h0 : constantCoeff (C ω * L) = 0 := by rw [map_mul, hL0, mul_zero]
  rw [psubst_psubst (σ := Unit) h0 hU] at h5
  have u0 : constantCoeff (PowerSeries.subst (C ω * L) U : K⟦X⟧) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero h0 _ hU
  refine ⟨ω, f.substInvOfIsUnit f1, by rw [coeff_one_substInvOfIsUnit]; exact Units.isUnit _, ?_⟩
  have h6 := congrArg (MvPowerSeries.map φ) (subst_substInvOfIsUnit_left f f0 f1)
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' f0)] at h6
  have h7 : PowerSeries.subst f' (PowerSeries.map φ (f.substInvOfIsUnit f1)) = (X : K⟦X⟧) :=
    h6.trans (PowerSeries.map_X φ)
  have h8 := psubst_psubst (σ := Unit) u0 f0' (PowerSeries.map φ (f.substInvOfIsUnit f1))
  rw [h7, h5, X_subst, PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' u0)] at h8
  exact h8

end Algebra

theorem exists_mChart : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.Ok → IsAlgebraic ℚ M.W.a₁ → IsAlgebraic ℚ M.W.a₂ → IsAlgebraic ℚ M.W.a₃ → IsAlgebraic ℚ M.W.a₄ → IsAlgebraic ℚ M.W.a₆ → ∃ ω : ℂ_[q], M.MChart ω := by
  intro d q _ M hd hd16 hsp hL hOk b₁ b₂ b₃ b₄ b₆
  obtain ⟨F, hfin, H⟩ := exists_formalGroup_add q M hOk b₁ b₂ b₃ b₄ b₆
  obtain ⟨ℓ, hℓ, hUℓ, h1, h2⟩ := height_one_of_split d q M F hd hd16 hsp hL hOk H
  have hU : constantCoeff (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, tay, coeff_mk]
    simp [Mdl.u]
  rw [← map_mulN (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F hU hℓ hUℓ H q] at h1 h2
  obtain ⟨f, hf⟩ := GlobalTheory.ConvSer.HeightOneInt.htOneIsGm q F hfin ⟨h1, h2⟩
  have hL0 : constantCoeff (logS : ℂ_[q]⟦X⟧) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, logS, coeff_mk, if_pos rfl]
  obtain ⟨ω, e, he1, he⟩ := exists_scale (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F hU hℓ hUℓ H hf hL0
    (MulSeries.mulS_laws q).2.2.2.2.1
  have hO : ∀ x : 𝓞_ℂ_[q], ‖algebraMap 𝓞_ℂ_[q] ℂ_[q] x‖ ≤ 1 := fun x => by
    have hx := (Valuation.mem_valuationSubring_iff _ _).1 x.2
    rw [PadicComplex.norm_eq_norm]
    exact Valued.toNormedField.norm_le_one_iff.2 hx
  refine ⟨ω, hOk, by rw [map_mul, hL0, mul_zero], fun n => ?_, ?_⟩
  · rw [hat, he, coeff_map]; exact hO _
  · rw [hat, he, coeff_map]
    obtain ⟨v, hv⟩ := he1.exists_right_inv
    have h3 := congrArg (fun x => ‖algebraMap 𝓞_ℂ_[q] ℂ_[q] x‖) hv
    simp only [map_mul, norm_mul, map_one, norm_one] at h3
    have h4 := hO (coeff 1 e)
    have h5 := hO v
    nlinarith [norm_nonneg (algebraMap 𝓞_ℂ_[q] ℂ_[q] (coeff 1 e)), norm_nonneg (algebraMap 𝓞_ℂ_[q] ℂ_[q] v)]

end GlobalTheory.MomOne.SplitChart
end
end

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multiplicativeChart_at_splitPrime : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.Ok → IsAlgebraic ℚ M.W.a₁ → IsAlgebraic ℚ M.W.a₂ → IsAlgebraic ℚ M.W.a₃ → IsAlgebraic ℚ M.W.a₄ → IsAlgebraic ℚ M.W.a₆ → ∃ ω : ℂ_[q], M.MChart ω := by
  atlas_forward_decl GlobalTheory.MomOne.SplitChart.exists_mChart
end
