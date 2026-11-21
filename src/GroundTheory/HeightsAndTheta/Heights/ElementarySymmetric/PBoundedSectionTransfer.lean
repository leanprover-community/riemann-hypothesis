import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsArithNakaiMoishezon
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Reading
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PConeTrdeg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogXpow

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def ArithNMSmallSection.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (L : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) L → IsConjInvariantH L →
    IsAmpleOnModel y L.a →
    0 < II K ι (mCoordIdeal y) (D + 1) (fun _ => L) →
    ∃ m : ℕ, 1 ≤ m ∧ ∃ s ∈ chartLat y (GroundTheory.Heights₂.Heights.Inter.hermZpow L m).a 1, s ≠ 0 ∧
      ∃ c : ℝ, c < 1 ∧ IsBoundedH (mCoordIdeal y) y (GroundTheory.Heights₂.Heights.Inter.hermZpow L m) 1 c s

end

end GroundTheory.Heights₂.Heights.Targets
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

section Objects

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def IsGenBySmallSections (y : (Σ k, ι k) → Ω) (L : HermLine ι) : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ (q : ℕ) (w : Fin q → Ω),
    (∀ j, w j ∈ chartLat y (GroundTheory.Heights₂.Heights.Inter.hermZpow L n).a 1) ∧
    KH.GeneratesOn y (GroundTheory.Heights₂.Heights.Inter.hermZpow L n).a w ∧
    ∃ c : ℝ, c < 1 ∧
      ∀ j, IsBoundedH (mCoordIdeal y) y (GroundTheory.Heights₂.Heights.Inter.hermZpow L n) 1 c (w j)

end Objects

def ArithNMLift.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (L : HermLine ι) (P0 : Ideal (MRing ι)),
    IsArithVar (mCoordIdeal y) (D + 1) →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) L → IsConjInvariantH L →
    IsAmpleOnModel y L.a →
    (∃ m : ℕ, 1 ≤ m ∧ ∃ s ∈ chartLat y (GroundTheory.Heights₂.Heights.Inter.hermZpow L m).a 1, s ≠ 0 ∧
      ∃ c : ℝ, c < 1 ∧ IsBoundedH (mCoordIdeal y) y (GroundTheory.Heights₂.Heights.Inter.hermZpow L m) 1 c s) →
    (∀ (W : Ideal (MRing ι)) (e : ℕ), IsArithVar W (e + 1) → mCoordIdeal y ≤ W → e < D →
      ∀ (Ω' : Type) [Field Ω'] (y' : (Σ k, ι k) → Ω'), mCoordIdeal y' = W → IsGenBySmallSections y' L) →
    IsGenBySmallSections y L

end

end GroundTheory.Heights₂.Heights.Targets
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def AmpleOnModelRestrict.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω Ω' : Type) [Field Ω] [Field Ω']
    (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι k) → Ω') (a : K → ℤ),
    mCoordIdeal y ≤ mCoordIdeal y' → IsAmpleOnModel y a → IsAmpleOnModel y' a

end

end GroundTheory.Heights₂.Heights.Targets
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace NMPointZero

def line : Geo.HermLine (blockIdx fun _ : Unit ↦ 0) where
  a := 0
  h _ := 2
  pos _ _ := two_pos
  smul c z hc := by simp

theorem isSemipositiveRel (P0 P : Ideal (Geo.MRing (blockIdx fun _ : Unit ↦ 0))) :
    Geo.IsSemipositiveRel P0 P line := by
  refine ⟨contDiffOn_const, fun z _ w _ => ?_⟩
  simp [line, Geo.leviForm]

theorem isAmpleOnModel : IsAmpleOnModel (ι := blockIdx fun _ : Unit ↦ 0) unitPoint line.a := by
  intro e
  refine ⟨0, fun n _ => ⟨1, fun _ => 1, fun _ c _ => ?_, fun c _ => ⟨fun _ => 1, fun _ => one_mem _, ?_⟩⟩⟩
  · simp [unitPoint]
  · simp [unitPoint]

theorem isBoundedH_one :
    IsBoundedH (Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ 0) unitPoint) unitPoint
      (GroundTheory.Heights₂.Heights.Inter.hermZpow line ((1 : ℕ) : ℤ)) 1 (1 / 2) 1 := by
  intro dg dh g h z hg hh hd he _
  have hdd : dg = dh := by
    funext k
    have h1 := hd k
    simp [GroundTheory.Heights₂.Heights.Inter.hermZpow, line] at h1
    exact_mod_cast h1
  subst hdd
  have hgh : g - h = 0 := by
    refine form_eq_zero_of_unitPoint (δ := dg) ?_ ?_
    · exact ((geoMultiHomog_iff g dg).mp hg).sub ((geoMultiHomog_iff h dg).mp hh)
    · rw [map_sub, he, one_mul, sub_self]
  rw [sub_eq_zero.mp hgh]
  simp [GroundTheory.Heights₂.Heights.Inter.hermZpow, line]
  linarith [norm_nonneg (eval z (map (Int.castRingHom ℂ) h))]

def oneSystem : Geo.IntersectionSystem := fun _ _ _ _ _ _ _ => 1

end NMPointZero

theorem ArithNMLift.hyps_inhabited :
    Geo.IsArithVar (Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ 0) unitPoint) (0 + 1) ∧
      (⊥ : Ideal (Geo.MRing (blockIdx fun _ : Unit ↦ 0))) ≤ Geo.mCoordIdeal unitPoint ∧
      Geo.IsSemipositiveRel ⊥ (Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ 0) unitPoint) NMPointZero.line ∧
      Geo.IsConjInvariantH NMPointZero.line ∧
      IsAmpleOnModel (ι := blockIdx fun _ : Unit ↦ 0) unitPoint NMPointZero.line.a ∧
      (∃ m : ℕ, 1 ≤ m ∧ ∃ s ∈ Geo.chartLat (ι := blockIdx fun _ : Unit ↦ 0) unitPoint
          (GroundTheory.Heights₂.Heights.Inter.hermZpow NMPointZero.line m).a 1, s ≠ 0 ∧
        ∃ c : ℝ, c < 1 ∧ IsBoundedH (Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ 0) unitPoint) unitPoint
          (GroundTheory.Heights₂.Heights.Inter.hermZpow NMPointZero.line m) 1 c s) ∧
      (∀ (W : Ideal (Geo.MRing (blockIdx fun _ : Unit ↦ 0))) (e : ℕ), Geo.IsArithVar W (e + 1) →
        Geo.mCoordIdeal unitPoint ≤ W → e < 0 →
        ∀ (Ω' : Type) [Field Ω'] (y' : (Σ k, (blockIdx fun _ : Unit ↦ 0) k) → Ω'),
          Geo.mCoordIdeal y' = W → IsGenBySmallSections y' NMPointZero.line) := by
  refine ⟨unitPoint_isArithVar, bot_le, NMPointZero.isSemipositiveRel _ _, fun _ => rfl, NMPointZero.isAmpleOnModel,
    ⟨1, le_rfl, 1, fun c _ => ?_, one_ne_zero, 1 / 2, by norm_num, NMPointZero.isBoundedH_one⟩,
    fun _ e _ _ he => absurd he (Nat.not_lt_zero e)⟩
  simp [unitPoint]

theorem ArithNMSmallSection.hyps_inhabited :
    Geo.IsArithVar (Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ 0) unitPoint) (0 + 1) ∧
      (⊥ : Ideal (Geo.MRing (blockIdx fun _ : Unit ↦ 0))) ≤ Geo.mCoordIdeal unitPoint ∧
      Geo.IsSemipositiveRel ⊥ (Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ 0) unitPoint) NMPointZero.line ∧
      Geo.IsConjInvariantH NMPointZero.line ∧
      IsAmpleOnModel (ι := blockIdx fun _ : Unit ↦ 0) unitPoint NMPointZero.line.a ∧
      0 < NMPointZero.oneSystem Unit (blockIdx fun _ : Unit ↦ 0)
        (Geo.mCoordIdeal unitPoint) (0 + 1) (fun _ => NMPointZero.line) :=
  ⟨unitPoint_isArithVar, bot_le, NMPointZero.isSemipositiveRel _ _, fun _ => rfl, NMPointZero.isAmpleOnModel,
    one_pos⟩

theorem AmpleOnModelRestrict.hyps_inhabited :
    Geo.mCoordIdeal (ι := ArakelovGeometry.GlobalTheory (Fin 2)) ProjLine.y ≤ Geo.mCoordIdeal (ι := ArakelovGeometry.GlobalTheory (Fin 2)) (fun _ => (1 : ℚ)) ∧
      IsAmpleOnModel (ι := ArakelovGeometry.GlobalTheory (Fin 2)) ProjLine.y ProjLine.fsLine1.a :=
  ⟨by rw [ProjLine.mCoordIdeal_y]; exact bot_le, isAmpleOnModel_projLine⟩

end

end GroundTheory.Heights₂.Heights.Targets
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def BoundedSectionTransfer.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω Ω' : Type) [Field Ω] [Field Ω']
    (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι k) → Ω') (d : ℕ) (A : Geo.HermLine ι) (τ : ℕ) (c : ℝ) (s' : Ω'),
    IsArithVar (mCoordIdeal y) d → mCoordIdeal y' = mCoordIdeal y →
    s' ∈ chartLat y' A.a τ → s' ≠ 0 → IsBoundedH (mCoordIdeal y') y' A τ c s' →
    ∃ s ∈ chartLat y A.a τ, s ≠ 0 ∧ IsBoundedH (mCoordIdeal y) y A τ c s

end

end GroundTheory.Heights₂.Heights.Targets
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace BoundedSectionTransfer

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem isMultiHomog_sub {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by
  rw [sub_eq_add_neg]
  refine isMultiHomog_add hf fun m hm k ↦ hg m ?_ k
  rwa [MvPolynomial.support_neg] at hm

theorem isMultiHomog_C (r : ℤ) : IsMultiHomog (C r : MRing ι) 0 := by
  classical
  intro m hm k
  rw [mem_support_iff, coeff_C] at hm
  split_ifs at hm with h0
  · subst h0; simp
  · exact absurd rfl hm

theorem mem_mCoordIdeal_iff {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) : g ∈ mCoordIdeal y ↔ aeval y g = 0 := by
  rw [mCoordIdeal, RingHom.mem_ker, ConeTrdeg.mConeMap_of_isMultiHomog y hg]
  refine ⟨fun h ↦ C_eq_zero.mp ((mul_eq_zero.mp h).resolve_right
    (Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (X_ne_zero k))), fun h ↦ by rw [h, C_0, zero_mul]⟩

theorem aeval_eq_zero_iff {Ω Ω' : Type} [Field Ω] [Field Ω'] {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → Ω'}
    (hP : mCoordIdeal y' = mCoordIdeal y) {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    aeval y g = 0 ↔ aeval y' g = 0 := by
  rw [← mem_mCoordIdeal_iff y hg, ← mem_mCoordIdeal_iff y' hg, hP]

theorem rel_iff {Ω Ω' : Type} [Field Ω] [Field Ω'] {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → Ω'}
    (hP : mCoordIdeal y' = mCoordIdeal y) {N D g h : MRing ι} {dN dD dg dh : K → ℕ}
    (hN : IsMultiHomog N dN) (hD : IsMultiHomog D dD) (hg : IsMultiHomog g dg) (hh : IsMultiHomog h dh)
    (hdeg : dg + dD = dN + dh) {s : Ω} {s' : Ω'} (hD0 : aeval y D ≠ 0) (hD0' : aeval y' D ≠ 0)
    (hs : aeval y N = s * aeval y D) (hs' : aeval y' N = s' * aeval y' D) :
    aeval y g = s * aeval y h ↔ aeval y' g = s' * aeval y' h := by
  classical
  have e : ∀ {Ω : Type} [Field Ω] (x : (Σ k, ι k) → Ω) (r : Ω), aeval x D ≠ 0 → aeval x N = r * aeval x D →
      (aeval x g = r * aeval x h ↔ aeval x (g * D - N * h) = 0) := by
    intro Ω _ x r hx hr
    rw [map_sub, map_mul, map_mul, hr, sub_eq_zero]
    exact ⟨fun h1 ↦ by rw [h1]; ring, fun h1 ↦ mul_right_cancel₀ hx (by rw [h1]; ring)⟩
  have hgD : IsMultiHomog (g * D - N * h) (dg + dD) :=
    isMultiHomog_sub (ArakelovGeometry.isMultiHomog_mul hg hD) (by rw [hdeg]; exact ArakelovGeometry.isMultiHomog_mul hN hh)
  rw [e y s hD0 hs, e y' s' hD0' hs', aeval_eq_zero_iff hP hgD]

theorem aeval_xpow [DecidableEq K] {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (e : K → ℕ) :
    aeval y (ArakelovGeometry.xpow c e) = ∏ k, y ⟨k, c k⟩ ^ e k := by
  simp [ArakelovGeometry.xpow, map_prod]

theorem exists_form {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {x : Ω}
    (hx : x ∈ chartRingZ y c) :
    ∃ (δ : K → ℕ) (G : MRing ι), IsMultiHomog G δ ∧ aeval y G = x * ∏ k, y ⟨k, c k⟩ ^ δ k := by
  classical
  have hpow : ∀ δ₁ δ₂ : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ (δ₁ + δ₂) k =
      (∏ k, y ⟨k, c k⟩ ^ δ₁ k) * ∏ k, y ⟨k, c k⟩ ^ δ₂ k := fun δ₁ δ₂ ↦ by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ ↦ by rw [Pi.add_apply, pow_add]
  rw [chartRingZ] at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨k, i⟩, rfl⟩ := hx
    refine ⟨Pi.single k 1, X ⟨k, i⟩, ArakelovGeometry.isMultiHomog_X' k i, ?_⟩
    rw [aeval_X, Finset.prod_eq_single k (fun k' _ hk' ↦ by simp [hk']) (by simp)]
    simp [div_mul_cancel₀ _ (hc k)]
  | algebraMap r =>
    exact ⟨0, C r, isMultiHomog_C r, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨δ₁, e₁, h₁, v₁⟩ := hx
    obtain ⟨δ₂, e₂, h₂, v₂⟩ := hz
    refine ⟨δ₁ + δ₂, e₁ * ArakelovGeometry.xpow c δ₂ + e₂ * ArakelovGeometry.xpow c δ₁,
      isMultiHomog_add (ArakelovGeometry.isMultiHomog_mul h₁ (ArakelovGeometry.isMultiHomog_xpow c δ₂)) ?_, ?_⟩
    · rw [add_comm δ₁]
      exact ArakelovGeometry.isMultiHomog_mul h₂ (ArakelovGeometry.isMultiHomog_xpow c δ₁)
    · rw [map_add, map_mul, map_mul, v₁, v₂, aeval_xpow, aeval_xpow, hpow]
      ring
  | mul x z _ _ hx hz =>
    obtain ⟨δ₁, e₁, h₁, v₁⟩ := hx
    obtain ⟨δ₂, e₂, h₂, v₂⟩ := hz
    refine ⟨δ₁ + δ₂, e₁ * e₂, ArakelovGeometry.isMultiHomog_mul h₁ h₂, ?_⟩
    rw [map_mul, v₁, v₂, hpow]
    ring

theorem mem_chartRingZ {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {G : MRing ι} {δ : K → ℕ}
    (hG : IsMultiHomog G δ) : aeval y G * ∏ k, y ⟨k, c k⟩ ^ (-(δ k : ℤ)) ∈ chartRingZ y c := by
  have key : ∀ f : MRing ι, MvPolynomial.eval (fun k ↦ (y ⟨k, c k⟩)⁻¹) (mConeMap y f) =
      aeval (fun p : Σ k, ι k ↦ y p / y ⟨p.1, c p.1⟩) f := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r => simp [mConeMap]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p q hp =>
      simp only [map_mul]
      rw [hp]
      simp [mConeMap, div_eq_mul_inv]
  have h := key G
  rw [ConeTrdeg.mConeMap_of_isMultiHomog y hG] at h
  rw [chartRingZ, Algebra.adjoin_range_eq_range_aeval]
  refine ⟨G, ?_⟩
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← h, map_mul, eval_C, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [map_pow, eval_X, zpow_neg, zpow_natCast, inv_pow]

theorem chart_iff [DecidableEq K] {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (t : K → ℤ) (s : Ω) (G : MRing ι) (δ : K → ℕ) :
    aeval y G = s * (∏ k, y ⟨k, c k⟩ ^ (-t k)) * ∏ k, y ⟨k, c k⟩ ^ δ k ↔
      aeval y (G * ArakelovGeometry.xpow c fun k ↦ (t k).toNat) =
        s * aeval y (ArakelovGeometry.xpow c (δ + fun k ↦ (-t k).toNat)) := by
  have hu : (∏ k, y ⟨k, c k⟩ ^ (t k).toNat) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)
  have hzu : (∏ k, y ⟨k, c k⟩ ^ (-t k)) * ∏ k, y ⟨k, c k⟩ ^ (t k).toNat =
      ∏ k, y ⟨k, c k⟩ ^ (-t k).toNat := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hc k)]
    congr 1
    linarith [Int.toNat_sub_toNat_neg (t k)]
  have hsplit : ∏ k, y ⟨k, c k⟩ ^ (δ + fun k ↦ (-t k).toNat) k =
      (∏ k, y ⟨k, c k⟩ ^ δ k) * ∏ k, y ⟨k, c k⟩ ^ (-t k).toNat := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ ↦ by rw [Pi.add_apply, pow_add]
  rw [map_mul, aeval_xpow, aeval_xpow, hsplit, ← hzu]
  exact ⟨fun h ↦ by rw [h]; ring, fun h ↦ mul_right_cancel₀ hu (by rw [h]; ring)⟩

theorem coord_ne_zero_iff {Ω Ω' : Type} [Field Ω] [Field Ω'] {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → Ω'}
    (hP : mCoordIdeal y' = mCoordIdeal y) (k : K) (i : ι k) : y ⟨k, i⟩ ≠ 0 ↔ y' ⟨k, i⟩ ≠ 0 := by
  classical
  have := aeval_eq_zero_iff hP (ArakelovGeometry.isMultiHomog_X' (ι := ι) k i)
  simp only [aeval_X] at this
  exact this.not

end BoundedSectionTransfer

theorem BoundedSectionTransfer.proof : BoundedSectionTransfer.Statement := by
  intro K _ ι _ Ω Ω' _ _ y y' d A τ c s' hvar hP hs' hs0 hb
  classical
  open BoundedSectionTransfer in
  have hchart : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ k, y' ⟨k, c k⟩ ≠ 0 :=
    fun c hc k ↦ (coord_ne_zero_iff hP k (c k)).1 (hc k)
  have huv : ∀ k, ((((τ : ℤ) * A.a k).toNat : ℕ) : ℤ) = (((-((τ : ℤ) * A.a k)).toNat : ℕ) : ℤ) + τ * A.a k :=
    fun k ↦ by linarith [Int.toNat_sub_toNat_neg ((τ : ℤ) * A.a k)]
  obtain ⟨c0, hc0⟩ : ∃ c0 : ∀ k, ι k, ∀ k, y ⟨k, c0 k⟩ ≠ 0 := by
    have hrel := hvar.2.1.2.2
    refine ⟨fun k ↦ (hrel k).choose, fun k h ↦ (hrel k).choose_spec ?_⟩
    rw [BoundedSectionTransfer.mem_mCoordIdeal_iff y (ArakelovGeometry.isMultiHomog_X' k _), aeval_X]
    exact h
  obtain ⟨δ, G, hG, hGv⟩ :=
    BoundedSectionTransfer.exists_form y' c0 (hchart c0 hc0) (hs' c0 (hchart c0 hc0))
  have hN' := (BoundedSectionTransfer.chart_iff y' c0 (hchart c0 hc0) (fun k ↦ (τ : ℤ) * A.a k) s' G δ).1 hGv
  have hNh := ArakelovGeometry.isMultiHomog_mul hG (ArakelovGeometry.isMultiHomog_xpow c0 fun k ↦ ((τ : ℤ) * A.a k).toNat)
  have hDh := ArakelovGeometry.isMultiHomog_xpow c0 (δ + fun k ↦ (-((τ : ℤ) * A.a k)).toNat)
  have hD0 : ∀ {Ω : Type} [Field Ω] (x : (Σ k, ι k) → Ω), (∀ k, x ⟨k, c0 k⟩ ≠ 0) →
      aeval x (ArakelovGeometry.xpow c0 (δ + fun k ↦ (-((τ : ℤ) * A.a k)).toNat)) ≠ 0 := fun x hx ↦ by
    rw [BoundedSectionTransfer.aeval_xpow]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hx k)
  set s : Ω := aeval y (G * ArakelovGeometry.xpow c0 fun k ↦ ((τ : ℤ) * A.a k).toNat) /
    aeval y (ArakelovGeometry.xpow c0 (δ + fun k ↦ (-((τ : ℤ) * A.a k)).toNat)) with hs_def
  have hNs : aeval y (G * ArakelovGeometry.xpow c0 fun k ↦ ((τ : ℤ) * A.a k).toNat) =
      s * aeval y (ArakelovGeometry.xpow c0 (δ + fun k ↦ (-((τ : ℤ) * A.a k)).toNat)) := by
    rw [hs_def, div_mul_cancel₀ _ (hD0 y hc0)]
  have key : ∀ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg → IsMultiHomog h dh →
      (∀ k, (dg k : ℤ) = dh k + τ * A.a k) → (aeval y g = s * aeval y h ↔ aeval y' g = s' * aeval y' h) := by
    intro dg dh g h hg hh hdeg
    refine BoundedSectionTransfer.rel_iff hP hNh hDh hg hh ?_ (hD0 y hc0) (hD0 y' (hchart c0 hc0)) hNs hN'
    funext k
    have h1 := hdeg k
    have h2 := huv k
    simp only [Pi.add_apply]
    generalize ((τ : ℤ) * A.a k).toNat = a at h2 ⊢
    generalize (-((τ : ℤ) * A.a k)).toNat = b at h2 ⊢
    generalize (τ : ℤ) * A.a k = w at h1 h2
    omega
  refine ⟨s, fun c hc ↦ ?_, fun h0 ↦ ?_, ?_⟩
  · obtain ⟨δc, Gc, hGc, hGcv⟩ :=
      BoundedSectionTransfer.exists_form y' c (hchart c hc) (hs' c (hchart c hc))
    have h1 := (BoundedSectionTransfer.chart_iff y' c (hchart c hc) (fun k ↦ (τ : ℤ) * A.a k) s' Gc δc).1 hGcv
    have h2 := (key _ _ _ _ (ArakelovGeometry.isMultiHomog_mul hGc
      (ArakelovGeometry.isMultiHomog_xpow c fun k ↦ ((τ : ℤ) * A.a k).toNat))
      (ArakelovGeometry.isMultiHomog_xpow c (δc + fun k ↦ (-((τ : ℤ) * A.a k)).toNat)) (fun k ↦ by simp only [Pi.add_apply, Nat.cast_add]; linarith [huv k])).2 h1
    have h3 := (BoundedSectionTransfer.chart_iff y c hc (fun k ↦ (τ : ℤ) * A.a k) s Gc δc).2 h2
    have h4 := BoundedSectionTransfer.mem_chartRingZ y c hGc
    have hone : ∏ k, (y ⟨k, c k⟩ ^ δc k * y ⟨k, c k⟩ ^ (-(δc k : ℤ))) = 1 :=
      Finset.prod_eq_one fun k _ ↦ by rw [zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ (hc k))]
    convert h4 using 1
    rw [h3, mul_assoc (s * _), ← Finset.prod_mul_distrib, hone, mul_one]
  · have h1 : aeval y (G * ArakelovGeometry.xpow c0 fun k ↦ ((τ : ℤ) * A.a k).toNat) = 0 := by rw [hNs, h0, zero_mul]
    rw [BoundedSectionTransfer.aeval_eq_zero_iff hP hNh, hN'] at h1
    exact mul_ne_zero hs0 (hD0 y' (hchart c0 hc0)) h1
  · intro dg dh g h z hg hh hdeg hrel hz
    rw [hP] at hb
    exact hb dg dh g h z hg hh hdeg ((key dg dh g h hg hh hdeg).1 hrel) hz

end

end GroundTheory.Heights₂.Heights.Targets
end
