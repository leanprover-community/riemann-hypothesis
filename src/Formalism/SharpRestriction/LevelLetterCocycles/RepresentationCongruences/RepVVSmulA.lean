import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ImportsAlt
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LiftsAtThickLetterType
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.FilVSep
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsPhiBridge
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.AcoordSumVecMul
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LemGBInImgIff

section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem arc_letter_type_eq_ite [NeZero n] {b w S η : ℕ} {up : ZMod n → Bool} {size : ZMod n → ℕ} (i : ZMod n) :
    (arcOf b w S η up size).ty i = if up i then Formalism.MainNotions.LocalTheoryWindows.LT.up (size i) else Formalism.MainNotions.LocalTheoryWindows.LT.down (size i) :=
  rfl

theorem arc_length_two_reduction [NeZero n] [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (hW₁ : Win W (arcOf b w S η up size) T₁) (hW₂ : Win W (arcOf b w S η up size) T₂)
    (hArc : ArcCore W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hFL : ArcFilLowCore W)
    (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts) {d : ℕ} (bb : Fin d → W.DD T₂)
    (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f)
    (hlen : (arcOf b w S η up size).len c = 2) (hdiff : up (c - 1) ≠ up c)
    (hOK : (arcOf b w S η up size).OK)
    (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hup : up c = false)
    {d₁ : ℕ} (b₁ : Fin d₁ → W.DD T₁) (sol₁ : Fin d₁ → ℕ → Fin d₁ → LL)
    (hb₁ : IsHor W T₁ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) b₁ sol₁) (c₁ : Fin d₁ → O)
    (hlt : dvO W T₁ ((arcOf b w S η up size).len c) b₁ c₁ ∈ FilS W T₁ c 1 (size (c - 1)))
    (hpr : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ ((arcOf b w S η up size).len c) b₁ c₁) =
      ((PD.p : LL) ^ (2 * (arcOf b w S η up size).σ PD.p)) •
        dv W T₂ ((arcOf b w S η up size).len c) bb (Pi.single k₀ 1)) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 9 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  set A := arcOf b w S η up size with hA
  have hup1 : up (c - 1) = true := by
    cases h : up (c - 1) <;> simp_all
  have hty0 : A.ty c = Formalism.MainNotions.LocalTheoryWindows.LT.down (size c) := by
    rw [hA, arc_letter_type_eq_ite, hup]; rfl
  have hty1 : A.ty (c - 1) = Formalism.MainNotions.LocalTheoryWindows.LT.up (size (c - 1)) := by
    rw [hA, arc_letter_type_eq_ite, hup1]; rfl
  have hl5 : 5 ≤ PD.p := by have := hB.1; omega
  have hcase : Formalism.MainNotions.LiftingTheory.CaseA W := hB.2.1.1
  have hthick : ∀ s < A.len c, (A.ty (c - (s : ZMod n))).thick := by
    intro s _
    rw [hA, arc_letter_type_eq_ite]
    split_ifs <;> rfl
  have hden : nnDen W A c = ps W 1 ^ size (c - 1) := by
    simp only [nnDen, prodTy, hlen, Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero,
      sub_zero, Nat.cast_one, hty0, hty1, pow_zero, one_mul]
  obtain ⟨hf1, hf2⟩ := hf
  have hL := liftsAt_thin_letter_type W A F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0 hSec hGL hFL hO hOv hinj hArc
    hW₁ hW₂ hbb ({1} : Finset ℕ) (by
      intro s hs
      rw [Finset.mem_singleton] at hs
      subst hs
      refine ⟨by omega, size (c - 1), ?_⟩
      rw [Nat.cast_one, hty1]) b₁ sol₁ hb₁ c₁ (2 * A.σ PD.p) (by
      intro s hs bs hbs
      rw [Finset.mem_singleton] at hs
      subst hs
      rw [Nat.cast_one, hty1] at hbs
      cases hbs
      exact hlt) hpr f (by
      simpa [Nat.cast_one, hty1, ← hden] using hf1) (by
      intro s hs bs hbs
      obtain ⟨κ, x, hx⟩ := hf2 s hs bs hbs
      refine ⟨κ, x, ?_⟩
      simpa [Nat.cast_one, hty1, ← hden] using hx) (by
      intro s hs hs1 bs hbs
      have hs0 : s = 0 := by
        rw [Finset.mem_singleton] at hs1
        omega
      subst hs0
      rw [Nat.cast_zero, sub_zero, hty0] at hbs
      cases hbs)
  refine ⟨2 * A.σ PD.p + A.σ PD.p, ?_, hL⟩
  push_cast
  linarith

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

open scoped TensorProduct

namespace ArcLengthTwo

variable (W : LocWach PD LL O v n)

theorem φVB_inj {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] :
    Function.Injective (φVB PD (LL := LL) (V := V)) := by
  have h : ∀ y, φVB PD (LL := LL) (V := V) y = ((PD.φ.toLinearMap.restrictScalars Qp).lTensor V) y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [φVB]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hi : Function.Injective (PD.φ.toLinearMap.restrictScalars Qp) := PD.φ_inj
  intro a b hab
  rw [h, h] at hab
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hi hab

theorem crisMap_φ {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] (f : V →ₗ[LL] V') (x : V ⊗[Qp] B) :
    Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B f (φVB PD (LL := LL) (V := V) x) = φVB PD (LL := LL) (V := V') (Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp [Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap, φVB]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem dv_succ (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → LL) :
    dv W T (e + 1) b c₀ = φVB PD (LL := LL) (V := T.V) (dv W T e b c₀) := by
  simp only [dv, map_sum, map_smul, pow_succ', Module.End.mul_apply]

theorem dvO_succ (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → O) :
    dvO W T (e + 1) b c₀ = φVB PD (LL := LL) (V := T.V) (dvO W T e b c₀) :=
  dv_succ W T e b _

theorem dvO_single (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (k : Fin d) :
    dvO W T e b (Pi.single k 1) = dv W T e b (Pi.single k 1) := by
  unfold dvO
  congr 1
  funext m
  by_cases h : m = k
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem dv_eq_sum (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → LL) :
    dv W T e b c₀ = ∑ m, c₀ m • dv W T e b (Pi.single m 1) := by
  unfold dv
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_eq_single m (fun m' _ hm' => by simp [Pi.single_apply, hm']) (by simp)]
  simp

theorem dvO_lin (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) {I : Type} (s : Finset I)
    (a : I → O) (c₀ : I → Fin d → O) :
    dvO W T e b (fun m => ∑ i ∈ s, a i * c₀ i m) = ∑ i ∈ s, algebraMap O LL (a i) • dvO W T e b (c₀ i) := by
  simp only [dvO, dv, map_sum, map_mul, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]

theorem dvO_smul (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (x : O) (c₀ : Fin d → O) :
    dvO W T e b (fun m => x * c₀ m) = algebraMap O LL x • dvO W T e b c₀ := by
  simp only [dvO, dv, map_mul, Finset.smul_sum, smul_smul]

theorem filS_φ (T : LocLat G Qp LL O) {a c : ZMod n} (hac : c - ((1 : ℕ) : ZMod n) = a) {u : ℤ}
    {x : T.V ⊗[Qp] B} (hx : x ∈ FilS W T a 0 u) : φVB PD (LL := LL) (V := T.V) x ∈ FilS W T c 1 u := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨y, ?_, ?_⟩
  · rw [hac]
    simpa using hy
  · simp

theorem filS_φ_inv (T : LocLat G Qp LL O) {a c : ZMod n} (hac : c - ((1 : ℕ) : ZMod n) = a) {u : ℤ}
    {x : T.V ⊗[Qp] B} (hx : φVB PD (LL := LL) (V := T.V) x ∈ FilS W T c 1 u) : x ∈ FilS W T a 0 u := by
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := φVB_inj (by simpa using hyx)
  subst this
  refine ⟨y, ?_, by simp⟩
  rw [← hac]
  simpa using hy

theorem filS_anti (T : LocLat G Qp LL O) (a : ZMod n) (s : ℕ) {u u' : ℤ} (h : u ≤ u') :
    FilS W T a s u' ≤ FilS W T a s u :=
  Submodule.map_mono (inf_le_inf_right _ (Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ h))

theorem RepVV_smulA {T : LocLat G Qp LL O} {c' : ZMod n} {e M : ℕ} {Λ : LetA O n} {d : ℕ}
    {b : Fin d → W.DD T} {sol : Fin d → ℕ → Fin d → LL} {a : LetA O n} (ha : a ∈ W.AΔ) {x : W.DD T}
    {f : Fin d → W.EE} (h : RepVV W T c' e M Λ b sol x f) :
    RepVV W T c' e M Λ b sol (a • x) (fun k => algebraMap (LetA O n) W.EE a * f k) := by
  obtain ⟨κ, κ', H, a', hH, ha', hP⟩ := h
  refine ⟨κ, κ', H, fun k => a * a' k, hH,
    fun k => ⟨mul_mem ha (ha' k).1, ?_⟩, ?_⟩
  · rw [map_mul, ← (ha' k).2]
    ring
  · have hs : ∑ k, (a * a' k) • ((W.φD T) ^ e) (H k) = a • ∑ k, a' k • ((W.φD T) ^ e) (H k) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun k _ => mul_smul _ _ _
    rw [hs]
    have key : lA W ^ κ' • (lA W ^ κ • Λ • (a • x) - a • ∑ k, a' k • ((W.φD T) ^ e) (H k)) =
        a • (lA W ^ κ' • (lA W ^ κ • Λ • x - ∑ k, a' k • ((W.φD T) ^ e) (H k))) := by
      rw [smul_sub, smul_sub, smul_sub, smul_comm a (lA W ^ κ') (lA W ^ κ • Λ • x), smul_comm a (lA W ^ κ) (Λ • x),
        smul_comm a Λ x, smul_comm a (lA W ^ κ')]
    rw [key]
    exact TypesA.inMultiple_smul W ha hP

theorem γD_smulA (T : LocLat G Qp LL O) (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

theorem γA_letE (g : W.Gam) (i : ZMod n) : W.γA g (letE i : LetA O n) = letE i := by
  funext k
  by_cases h : k = i
  · subst h; simp [LocWach.γA, letγ, letE]
  · simp [LocWach.γA, letγ, letE, Pi.single_apply, h]

theorem letE_mul_self (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  funext k
  by_cases h : k = i
  · subst h; simp [letE]
  · simp [letE, Pi.single_apply, h]

theorem avg_props {T : LocLat G Qp LL O} (a : ZMod n) {z : W.DD T} (hz : z ∈ W.N T)
    (hza : (letE a : LetA O n) • z = z) :
    (∑ δ ∈ W.DelF, W.γD T δ z) ∈ W.NΔ T ∧
      (letE a : LetA O n) • (∑ δ ∈ W.DelF, W.γD T δ z) = ∑ δ ∈ W.DelF, W.γD T δ z := by
  refine ⟨⟨Submodule.sum_mem _ fun δ _ => W.N_Γ T δ z hz, fun δ' hδ' => ?_⟩, ?_⟩
  · rw [map_sum]
    refine Finset.sum_nbij' (δ' * ·) (δ'⁻¹ * ·) (fun g hg => TypesA.delF_mul W hδ' hg)
      (fun g hg => TypesA.delF_mul W (TypesA.delF_inv W hδ') hg) (fun g _ => by simp) (fun g _ => by simp)
      (fun g _ => ?_)
    rw [W.γD_mul]
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [← γA_letE W δ a, ← γD_smulA, hza]

end ArcLengthTwo

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end
