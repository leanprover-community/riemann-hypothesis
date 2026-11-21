import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyDeepSubset
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulLeftInvariantVolGL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanAntitone
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableZetaIntegrand

section
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic

namespace GlobalTheory.ShellInt

theorem integrableOn_shell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ) (ν : kˣ →* ℂˣ) (e : ℕ), CondLE ϖ e ν →
    ∀ (a : ℕ) (μ : Measure (GL (Fin a) k)) [μ.IsHaarMeasure] (φ : Matrix (Fin a) (Fin a) k → ℂ),
      φ ∈ SB (Matrix (Fin a) (Fin a) k) → ∀ (n : Fin a → ℤ) (z : ℂ),
        IntegrableOn (fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) (shellSet ϖ n) μ := by
  intro k _ _ _ _ _ _ ϖ ν e hν a μ _ φ hφ n z
  have hcomp : IsCompact (shellSet ϖ n : Set (GL (Fin a) k)) :=
    (isCompact_KO.mul isCompact_singleton).mul isCompact_KO
  let χ : GL (Fin a) k →* ℂ :=
    { toFun := fun g => (ν (gdet g) : ℂ) * apow (gdet g) z
      map_one' := by simp
      map_mul' := fun g h => by simp only [gdet_mul, map_mul, Units.val_mul, apow_mul]; ring }
  have hχ1 : ∀ g ∈ detCong (ϖ ^ e) (Fin a), χ g = 1 := by
    intro g hg
    have h1 : ν (gdet g) = 1 := hν _ hg.2
    have h2 : apow (gdet g) z = 1 := apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg.1) z
    simp [χ, h1, h2]
  have hχc : Continuous χ := by
    refine continuous_of_continuousAt_one χ ?_
    have hev : (fun _ => (1 : ℂ)) =ᶠ[nhds (1 : GL (Fin a) k)] χ := by
      filter_upwards [(isOpen_detCong (ϖ ^ e) (Fin a)).mem_nhds (one_mem _)] with g hg
      exact (hχ1 g hg).symm
    have := (continuousAt_const (x := (1 : GL (Fin a) k)) (y := (1 : ℂ))).congr hev
    simpa using this
  have hcont : Continuous (fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) := by
    have h := (hφ.1.continuous.comp Units.continuous_val).mul hχc
    refine h.congr fun g => ?_
    simp [χ, mul_assoc]
  exact hcont.continuousOn.integrableOn_compact hcomp

end GlobalTheory.ShellInt
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_cartanDoubleCoset_shellIntegrand : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ) (ν : kˣ →* ℂˣ) (e : ℕ), CondLE ϖ e ν →
    ∀ (a : ℕ) (μ : Measure (GL (Fin a) k)) [μ.IsHaarMeasure] (φ : Matrix (Fin a) (Fin a) k → ℂ),
      φ ∈ SB (Matrix (Fin a) (Fin a) k) → ∀ (n : Fin a → ℤ) (z : ℂ),
        IntegrableOn (fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) (shellSet ϖ n) μ := by
  atlas_forward_decl GlobalTheory.ShellInt.integrableOn_shell
end

section
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic

namespace GlobalTheory.ShellCosets

theorem piece_eq_of_mem {G : Type*} [Group G] (K : Subgroup G) {c c' g : G}
    (h1 : c⁻¹ * g ∈ K) (h2 : c'⁻¹ * g ∈ K) :
    {h : G | c⁻¹ * h ∈ K} = {h : G | c'⁻¹ * h ∈ K} := by
  ext h
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hh
    have := K.mul_mem (K.mul_mem h2 (K.inv_mem h1)) hh
    simpa [mul_assoc] using this
  · intro hh
    have := K.mul_mem (K.mul_mem h1 (K.inv_mem h2)) hh
    simpa [mul_assoc] using this

theorem shell_cosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ) (a : ℕ) (n : Fin a → ℤ), ∃ t : Finset (GL (Fin a) k), (∀ x ∈ t, x ∈ KO k (Fin a)) ∧
      shellSet ϖ n = ⋃ x ∈ t, {g : GL (Fin a) k | (x * diagGL (fun i => ϖ ^ n i))⁻¹ * g ∈ KO k (Fin a)} ∧
      (t : Set (GL (Fin a) k)).PairwiseDisjoint
        (fun x => {g : GL (Fin a) k | (x * diagGL (fun i => ϖ ^ n i))⁻¹ * g ∈ KO k (Fin a)}) := by
  intro k _ _ _ _ ϖ a n
  classical
  set d : GL (Fin a) k := diagGL (fun i => ϖ ^ n i) with hd
  set K := KO k (Fin a) with hK
  set P : GL (Fin a) k → Set (GL (Fin a) k) := fun x => {g | (x * d)⁻¹ * g ∈ K} with hP
  have hPo : ∀ x, IsOpen (P x) := fun x =>
    (GlobalTheory.SplitFlip.isOpen_KO (k := k) (n := Fin a)).preimage (continuous_mul_left _)
  have hsub : ∀ x ∈ K, P x ⊆ shellSet ϖ n := by
    intro x hx g hg
    rw [mem_shellSet]
    exact ⟨x, hx, _, hg, by rw [← hd]; group⟩
  have himg : shellSet ϖ n = (fun p : GL (Fin a) k × GL (Fin a) k => p.1 * d * p.2) '' ((K : Set _) ×ˢ (K : Set _)) := by
    ext g
    rw [mem_shellSet]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩; exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
    · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩; exact ⟨x, hx, y, hy, rfl⟩
  have hcomp : IsCompact (shellSet ϖ n) := by
    rw [himg]
    exact (GlobalTheory.SplitFlip.isCompact_KO.prod GlobalTheory.SplitFlip.isCompact_KO).image (by fun_prop)
  have hcov : shellSet ϖ n ⊆ ⋃ x : K, P x := by
    intro g hg
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_shellSet.mp hg
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    show (x * d)⁻¹ * (x * (diagGL fun i => ϖ ^ n i) * y) ∈ K
    rw [← hd]
    convert hy using 1
    group
  obtain ⟨s, hs⟩ := hcomp.elim_finite_subcover (fun x : K => P x) (fun x => hPo x) hcov
  let s' : Finset (GL (Fin a) k) := s.image Subtype.val
  have hs'K : ∀ x ∈ s', x ∈ K := by
    intro x hx; obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx; exact y.2
  let r : Set (GL (Fin a) k) → GL (Fin a) k := Function.invFunOn P (s' : Set _)
  let t : Finset (GL (Fin a) k) := (s'.image P).image r
  have hr : ∀ x ∈ s', r (P x) ∈ s' ∧ P (r (P x)) = P x := fun x hx =>
    ⟨Function.invFunOn_mem ⟨x, hx, rfl⟩, Function.invFunOn_eq ⟨x, hx, rfl⟩⟩
  have ht : ∀ y ∈ t, ∃ x ∈ s', y = r (P x) := by
    intro y hy
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hQ
    exact ⟨x, hx, rfl⟩
  refine ⟨t, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := ht y hy
    exact hs'K _ (hr x hx).1
  · apply Set.Subset.antisymm
    · intro g hg
      obtain ⟨x, hxs, hgx⟩ := Set.mem_iUnion₂.mp (hs hg)
      have hx' : (x : GL (Fin a) k) ∈ s' := Finset.mem_image_of_mem _ hxs
      refine Set.mem_iUnion₂.mpr ⟨r (P x), Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hx'), ?_⟩
      show g ∈ P (r (P x))
      rw [(hr _ hx').2]; exact hgx
    · intro g hg
      obtain ⟨y, hy, hgy⟩ := Set.mem_iUnion₂.mp hg
      obtain ⟨x, hx, rfl⟩ := ht y hy
      exact hsub _ (hs'K _ (hr x hx).1) hgy
  · intro y hy y' hy' hne
    obtain ⟨x, hx, rfl⟩ := ht y hy
    obtain ⟨x', hx', rfl⟩ := ht y' hy'
    rw [Function.onFun, Set.disjoint_left]
    intro g hg hg'
    apply hne
    have := piece_eq_of_mem K hg hg'
    change P (r (P x)) = P (r (P x')) at this
    rw [(hr x hx).2, (hr x' hx').2] at this
    rw [this]

end GlobalTheory.ShellCosets
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartanDoubleCoset_finite_disjoint_leftCosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ) (a : ℕ) (n : Fin a → ℤ), ∃ t : Finset (GL (Fin a) k), (∀ x ∈ t, x ∈ KO k (Fin a)) ∧
      shellSet ϖ n = ⋃ x ∈ t, {g : GL (Fin a) k | (x * diagGL (fun i => ϖ ^ n i))⁻¹ * g ∈ KO k (Fin a)} ∧
      (t : Set (GL (Fin a) k)).PairwiseDisjoint
        (fun x => {g : GL (Fin a) k | (x * diagGL (fun i => ϖ ^ n i))⁻¹ * g ∈ KO k (Fin a)}) := by
  atlas_forward_decl GlobalTheory.ShellCosets.shell_cosets
end

section
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic

noncomputable section

namespace GlobalTheory.ShellPiece

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem val_le_one_of_mem {t : k} (h : t ∈ 𝒪[k]) : valuation k t ≤ 1 := h

theorem diagGL_mem_KO {a : ℕ} (c : Fin a → kˣ) (hc : ∀ j, valuation k (c j : k) = 1) :
    diagGL c ∈ KO k (Fin a) := by
  rw [mem_KO_iff]
  refine ⟨fun r s => ?_, fun r s => ?_⟩
  · show valuation k ((diagGL c).val r s) ≤ 1
    rw [diagGL_val, diagonal_apply]
    split_ifs
    · exact (hc r).le
    · simp
  · show valuation k (((diagGL c)⁻¹ : GL (Fin a) k).val r s) ≤ 1
    rw [show ((diagGL c)⁻¹ : GL (Fin a) k).val = diagonal fun j => (((c j)⁻¹ : kˣ) : k) from rfl, diagonal_apply]
    split_ifs
    · simp [hc r]
    · simp

end GlobalTheory.ShellPiece

open GlobalTheory.ShellPiece in

theorem GlobalTheory.ShellPiece.setIntegral_coset_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ), IsUnif ϖ → ∀ (ν : kˣ →* ℂˣ) (a : ℕ) (μ : Measure (GL (Fin a) k))
    [μ.IsHaarMeasure] (φ : Matrix (Fin a) (Fin a) k → ℂ) (M : ℤ), IsPeriodic ϖ M φ →
    ∀ (n : Fin a → ℤ) (i : Fin a), M ≤ n i → ∀ u : kˣ, valuation k (u : k) = 1 → ν u ≠ 1 →
    ∀ x ∈ KO k (Fin a), ∀ z : ℂ,
      ∫ g in {g : GL (Fin a) k | (x * diagGL (fun i => ϖ ^ n i))⁻¹ * g ∈ KO k (Fin a)},
        φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ = 0 := by
  intro k _ _ _ _ _ _ ϖ hϖ ν a μ _ φ M hφ n i hi u hu hν x hx z
  set d : GL (Fin a) k := diagGL (fun j => ϖ ^ n j) with hd
  set D : GL (Fin a) k := diagGL (Pi.mulSingle i u) with hD
  have hDK : D ∈ KO k (Fin a) := diagGL_mem_KO _ fun j => by
    by_cases h : j = i
    · subst h; simpa using hu
    · simp [Pi.mulSingle_eq_of_ne h]
  have hcomm : Commute d D := Units.ext (by simp [hd, hD, diagonal_mul_diagonal, mul_comm])
  set k0 := x * D * x⁻¹ with hk0
  have hk0K : k0 ∈ KO k (Fin a) := mul_mem (mul_mem hx hDK) (inv_mem hx)
  set S := {g : GL (Fin a) k | (x * d)⁻¹ * g ∈ KO k (Fin a)} with hS
  have key : ∀ g, (x * d)⁻¹ * (k0 * g) = D * ((x * d)⁻¹ * g) := fun g => by
    have h1 : d⁻¹ * D = D * d⁻¹ := (hcomm.inv_left).eq
    calc (x * d)⁻¹ * (k0 * g) = d⁻¹ * D * (x⁻¹ * g) := by rw [hk0]; group
      _ = D * d⁻¹ * (x⁻¹ * g) := by rw [h1]
      _ = D * ((x * d)⁻¹ * g) := by group
  have hpre : (fun g => k0 * g) ⁻¹' S = S := by
    ext g
    simp only [Set.mem_preimage, hS, Set.mem_setOf_eq, key]
    exact Subgroup.mul_mem_cancel_left _ hDK
  have hdetD : gdet D = u := by
    rw [hD, gdet, det_diagGL]
    simp
  have hdetk0 : gdet k0 = u := by
    rw [hk0, gdet_mul, gdet_mul, hdetD, mul_comm (gdet x), mul_assoc, ← gdet_mul, mul_inv_cancel]
    simp

  have hϖ1 : valuation k (ϖ : k) ≤ 1 := hϖ.mem
  have hpow : valuation k ((ϖ ^ n i : kˣ) : k) ≤ valuation k ((ϖ ^ M : kˣ) : k) := by
    have e : ϖ ^ n i = ϖ ^ M * ϖ ^ (n i - M).toNat := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), ← _root_.zpow_add]; congr 1; ring
    rw [e, Units.val_mul, map_mul, Units.val_pow_eq_pow_val, map_pow]
    exact mul_le_of_le_one_right' (pow_le_one₀ zero_le hϖ1)
  have hu1 : valuation k ((u : k) - 1) ≤ 1 :=
    ((valuation k).map_sub _ _).trans (max_le hu.le (by simp))
  have hZ : ∀ y ∈ KO k (Fin a), x.val * ((D.val - 1) * d.val) * y.val ∈ scaledInt ϖ a M := by
    intro y hy r s
    have e1 : (D.val - 1) * d.val = diagonal fun j => ((((Pi.mulSingle i u : Fin a → kˣ) j : kˣ) : k) - 1) * ((ϖ ^ n j : kˣ) : k) := by
      rw [hD, hd, diagGL_val, diagGL_val]
      ext p q
      by_cases hpq : p = q
      · subst hpq; simp [Matrix.mul_apply, diagonal_apply, Matrix.sub_apply, Matrix.one_apply]
      · simp [Matrix.mul_apply, diagonal_apply, Matrix.sub_apply, Matrix.one_apply, hpq]
    rw [e1, Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [mul_diagonal, Pi.mulSingle_eq_same, map_mul, map_mul, map_mul]
      have hx1 := val_le_one_of_mem ((mem_KO_iff x).1 hx |>.1 r i)
      have hy1 := val_le_one_of_mem ((mem_KO_iff y).1 hy |>.1 i s)
      calc _ ≤ 1 * (1 * valuation k ((ϖ ^ n i : kˣ) : k)) * 1 := by gcongr
        _ ≤ _ := by simpa using hpow
    · intro j _ hj
      simp [mul_diagonal, Pi.mulSingle_eq_of_ne hj]
    · simp
  have hF : ∀ g ∈ S, φ (k0 * g).val * (ν (gdet (k0 * g)) : ℂ) * apow (gdet (k0 * g)) z =
      (ν u : ℂ) * (φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) := by
    intro g hg
    set y := (x * d)⁻¹ * g with hy
    have hyK : y ∈ KO k (Fin a) := hg
    have hg' : g = x * d * y := by rw [hy]; group
    have hv : (k0 * g).val = g.val + x.val * ((D.val - 1) * d.val) * y.val := by
      have : k0 * g = x * D * d * y := by rw [hg', hk0]; group
      rw [this, hg']
      simp only [Units.val_mul]
      noncomm_ring
    rw [hv, hφ _ _ (hZ y hyK), gdet_mul, hdetk0, map_mul, Units.val_mul, apow_mul,
      apow_of_valuation_eq_one hu]
    ring
  have hSm : MeasurableSet S :=
    (isOpen_KO.preimage (continuous_const.mul continuous_id)).measurableSet
  have h := (measurePreserving_mul_left μ k0).setIntegral_preimage_emb (measurableEmbedding_mulLeft k0)
    (fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) S
  rw [hpre, setIntegral_congr_fun hSm (fun g hg => hF g hg), integral_const_mul] at h
  have hne : (ν u : ℂ) - 1 ≠ 0 := sub_ne_zero.2 fun e => hν (Units.val_eq_one.1 e)
  have h2 : ((ν u : ℂ) - 1) * ∫ g in S, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ = 0 := by
    rw [sub_mul, h]; ring
  exact (mul_eq_zero.1 h2).resolve_left hne

end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setIntegral_leftCoset_shellIntegrand_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ), IsUnif ϖ → ∀ (ν : kˣ →* ℂˣ) (a : ℕ) (μ : Measure (GL (Fin a) k))
    [μ.IsHaarMeasure] (φ : Matrix (Fin a) (Fin a) k → ℂ) (M : ℤ), IsPeriodic ϖ M φ →
    ∀ (n : Fin a → ℤ) (i : Fin a), M ≤ n i → ∀ u : kˣ, valuation k (u : k) = 1 → ν u ≠ 1 →
    ∀ x ∈ KO k (Fin a), ∀ z : ℂ,
      ∫ g in {g : GL (Fin a) k | (x * diagGL (fun i => ϖ ^ n i))⁻¹ * g ∈ KO k (Fin a)},
        φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ = 0 := by
  atlas_forward_decl GlobalTheory.ShellPiece.setIntegral_coset_eq_zero
end

section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat

noncomputable section
namespace GlobalTheory.ShellVan
open GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic

theorem valuation_unif_zpow {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ϖ : kˣ} (hϖ : IsUnif ϖ) (m : ℤ) : valuation k ((ϖ ^ m : kˣ) : k) = uniformizer k ^ m := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ]

theorem shell_eq_zero_of_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ), IsUnif ϖ → ∀ (ν : kˣ →* ℂˣ) (a : ℕ) (μ : Measure (GL (Fin a) k))
    (φ : Matrix (Fin a) (Fin a) k → ℂ) (M' : ℕ), Function.support φ ⊆ scaledInt ϖ a (-(M' : ℤ)) →
    ∀ n : Fin a → ℤ, ¬ (∀ i, -(M' : ℤ) ≤ n i) → ∀ z : ℂ, shell μ ϖ ν z φ n = 0 := by
  intro k _ _ _ _ _ _ ϖ hϖ ν a μ φ M' hS n hn z
  push_neg at hn
  obtain ⟨i, hi⟩ := hn
  rw [shell]
  refine setIntegral_eq_zero_of_forall_eq_zero fun g hg => ?_
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_shellSet.1 hg
  suffices h : φ (x * diagGL (fun i => ϖ ^ n i) * y).val = 0 by rw [h, zero_mul, zero_mul]
  by_contra hne
  have hmem := hS hne
  have hd : (diagGL (fun i => ϖ ^ n i)).val =
      (x⁻¹).val * (x * diagGL (fun i => ϖ ^ n i) * y).val * (y⁻¹).val := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have hx' := ((mem_KO_iff x).1 hx).2
  have hy' := ((mem_KO_iff y).1 hy).2
  have bound : ∀ r s, valuation k ((diagGL (fun i => ϖ ^ n i)).val r s) ≤
      valuation k (((ϖ ^ (-(M' : ℤ)) : kˣ) : k)) := by
    intro r s
    rw [hd, Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun t _ => ?_
    rw [map_mul, Matrix.mul_apply]
    calc _ ≤ valuation k (((ϖ ^ (-(M' : ℤ)) : kˣ) : k)) * 1 :=
          mul_le_mul' (Valuation.map_sum_le _ fun q _ => by
            rw [map_mul]
            exact (mul_le_of_le_one_left' ((Valuation.mem_integer_iff _ _).1 (hx' r q))).trans (hmem q t))
            ((Valuation.mem_integer_iff _ _).1 (hy' t s))
      _ = _ := mul_one _
  have h1 := bound i i
  simp only [diagGL_val, diagonal_apply_eq] at h1
  rw [valuation_unif_zpow hϖ, valuation_unif_zpow hϖ] at h1
  have hu0 : (0 : ValueGroupWithZero k) < uniformizer k := zero_lt_iff.2 uniformizer_ne_zero
  have h2 := (zpow_le_zpow_iff_right_of_lt_one₀ hu0 uniformizer_lt_one).1 h1
  omega

theorem shell_lemma : ShellLemma := by
  intro k _ _ _ _ _ _ ϖ hϖ ν e hram hcond a μ hμ φ hφ
  have : μ.IsHaarMeasure := hμ
  have hint := GlobalTheory.T.integrableOn_cartanDoubleCoset_shellIntegrand k ϖ ν e hcond a μ φ hφ
  have h2 : ∀ M : ℤ, IsPeriodic ϖ M φ → ∀ n : Fin a → ℤ, (∃ i, M ≤ n i) → ∀ z : ℂ, shell μ ϖ ν z φ n = 0 := by
    rintro M hM n ⟨i, hi⟩ z
    obtain ⟨u, hu1, hu2⟩ : ∃ u : kˣ, valuation k (u : k) = 1 ∧ ν u ≠ 1 := by
      by_contra h
      push_neg at h
      exact hram h
    obtain ⟨t, htK, heq, hdisj⟩ := GlobalTheory.T.cartanDoubleCoset_finite_disjoint_leftCosets k ϖ a n
    rw [shell, heq, integral_biUnion_finset t]
    · exact Finset.sum_eq_zero fun x hx =>
        GlobalTheory.T.setIntegral_leftCoset_shellIntegrand_eq_zero k ϖ hϖ ν a μ φ M hM n i hi u hu1 hu2 x (htK x hx) z
    · intro x _
      exact (isOpen_KO.preimage (continuous_const.mul continuous_id)).measurableSet
    · exact hdisj
    · intro x hx
      refine (hint n z).mono_set ?_
      rw [heq]
      exact Set.subset_biUnion_of_mem (u := fun x => {g : GL (Fin a) k | (x * diagGL (fun i => ϖ ^ n i))⁻¹ * g ∈ KO k (Fin a)}) hx
  have h3 := shell_eq_zero_of_support k ϖ hϖ ν a μ φ
  refine ⟨hint, h2, h3, ?_⟩
  obtain ⟨N, M, hN, hM⟩ := GlobalTheory.SBUniform.exists_bound_period k (Fin a) φ hφ
  have hP : IsPeriodic ϖ (M : ℤ) φ := fun X Z hZ => hM X Z fun i j => by
    have := hZ i j
    rwa [valuation_unif_zpow hϖ] at this
  have hS : Function.support φ ⊆ scaledInt ϖ a (-(N : ℤ)) := fun X hX i j => by
    rw [valuation_unif_zpow hϖ]
    exact hN X hX i j
  refine ((Set.Finite.pi (t := fun _ : Fin a => Set.Ico (-(N : ℤ)) M) fun _ => Set.finite_Ico _ _).preimage
    Subtype.val_injective.injOn).subset ?_
  rintro ⟨n, hn⟩ ⟨z, hz⟩ i -
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hz (h3 N hS n (fun h' => h (h' i)) z)
  · by_contra h
    exact hz (h2 M hP n ⟨i, not_lt.1 h⟩ z)

end GlobalTheory.ShellVan
end
end

section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zetaIntegralShells_vanish_beyondPeriod_ramified : GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic.ShellLemma := by
  atlas_forward_decl GlobalTheory.ShellVan.shell_lemma
end

section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

noncomputable section
namespace GlobalTheory.GJTransfer

theorem det_mem_integer {k : Type} [Field k] [ValuativeRel k] {n : ℕ} (X : Matrix (Fin n) (Fin n) k)
    (hX : X ∈ intM k (Fin n) (Fin n)) : valuation k X.det ≤ 1 := by
  let Y : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨X i j, hX i j⟩
  have e : X.det = (𝒪[k].subtype.mapMatrix Y).det := rfl
  rw [e, ← RingHom.map_det]
  exact (Y.det).2

theorem integrable_volGL_of_lintegral {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (μ : Measure k) [μ.IsAddHaarMeasure]
    (n : ℕ) (σ s : ℝ) (hs : s ≤ σ - n)
    (hI : ∫⁻ X : Matrix (Fin n) (Fin n) k, (intM k (Fin n) (Fin n)).indicator (fun Y => ENNReal.ofReal
      (if h : Y.det = 0 then 0 else nabs k (Units.mk0 Y.det h)) ^ s) X ∂(volM μ (Fin n) (Fin n)) < ⊤) :
    Integrable (fun g : GL (Fin n) k => (intM k (Fin n) (Fin n)).indicator (fun _ => (1 : ℝ)) g.val *
      nabs k (gdet g) ^ σ) (volGL μ (Fin n)) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : BorelSpace (GL (Fin n) k) := borel_GL
  have hE := Model.measurableEmbedding_val (k := k) (Fin n)
  have hd := continuous_density_volGL (k := k) (n := Fin n)
  have hn : IsLocallyConstant fun g : GL (Fin n) k => nabs k (GeneralLinearGroup.det g) :=
    (isLocallyConstant_nabs k).comp_continuous GeneralLinearGroup.continuous_det
  have hO : IsClopen (intM k (Fin n) (Fin n)) := ⟨isCompact_intMatrix.isClosed, isOpen_intMatrix⟩
  have hind : IsLocallyConstant fun g : GL (Fin n) k =>
      (intM k (Fin n) (Fin n)).indicator (fun _ => (1 : ℝ)) g.val :=
    (LocallyConstant.indicator (1 : LocallyConstant _ ℝ) hO).isLocallyConstant.comp_continuous
      Units.continuous_val
  set F : GL (Fin n) k → ℝ := fun g => (intM k (Fin n) (Fin n)).indicator (fun _ => (1 : ℝ)) g.val *
      nabs k (gdet g) ^ σ with hF
  have hFc : Continuous F :=
    hind.continuous.mul (hn.comp fun r : ℝ => r ^ σ).continuous
  refine ⟨hFc.aestronglyMeasurable, ?_⟩
  set I : Matrix (Fin n) (Fin n) k → ENNReal := (intM k (Fin n) (Fin n)).indicator (fun Y => ENNReal.ofReal
      (if h : Y.det = 0 then 0 else nabs k (Units.mk0 Y.det h)) ^ s) with hIdef
  have hpt : ∀ g : GL (Fin n) k, ENNReal.ofReal (nabs k (GeneralLinearGroup.det g) ^ (-(Fintype.card (Fin n) : ℝ)))
      * ‖F g‖ₑ ≤ I g.val := by
    intro g
    have hp := nabs_pos' (GeneralLinearGroup.det g)
    set a := nabs k (GeneralLinearGroup.det g) with ha
    by_cases hg : g.val ∈ intM k (Fin n) (Fin n)
    · have h0 : (g.val).det ≠ 0 := g.det_ne_zero
      have hu : Units.mk0 (g.val).det h0 = GeneralLinearGroup.det g := Units.ext rfl
      have hle : a ≤ 1 := by
        rw [ha, ← hu]
        exact Model.nabs_le_one _ (det_mem_integer _ hg)
      rw [hIdef, Set.indicator_of_mem hg, dif_neg h0, hu, ← ha, ENNReal.ofReal_rpow_of_pos hp]
      have hFg : F g = a ^ σ := by
        rw [hF]; simp only [Set.indicator_of_mem hg, one_mul]; rfl
      rw [hFg, Real.enorm_of_nonneg (Real.rpow_nonneg hp.le _),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hp.le _), ← Real.rpow_add hp, Fintype.card_fin]
      refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hp hle ?_)
      linarith
    · have hFg : F g = 0 := by
        rw [hF]; simp only [Set.indicator_of_notMem hg, zero_mul]
      rw [hFg]; simp
  unfold HasFiniteIntegral volGL
  erw [lintegral_withDensity_eq_lintegral_mul _ hd.measurable hFc.enorm.measurable]
  calc _ ≤ ∫⁻ g : GL (Fin n) k, I g.val ∂((volM μ (Fin n) (Fin n)).comap fun g : GL (Fin n) k => g.val) :=
        lintegral_mono fun g => hpt g
    _ = ∫⁻ X, I X ∂(((volM μ (Fin n) (Fin n)).comap fun g : GL (Fin n) k => g.val).map
          fun g : GL (Fin n) k => g.val) := (hE.lintegral_map I).symm
    _ = ∫⁻ X, I X ∂((volM μ (Fin n) (Fin n)).restrict (Set.range fun g : GL (Fin n) k => g.val)) := by
        erw [hE.map_comap]; rfl
    _ ≤ ∫⁻ X, I X ∂(volM μ (Fin n) (Fin n)) := lintegral_mono' Measure.restrict_le_self le_rfl
    _ < ⊤ := hI

theorem integrable_haarVol_of_lintegral {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : ℕ) (σ s : ℝ) (hs : s ≤ σ - n)
    (hI : ∫⁻ X : Matrix (Fin n) (Fin n) k, (intM k (Fin n) (Fin n)).indicator (fun Y => ENNReal.ofReal
      (if h : Y.det = 0 then 0 else nabs k (Units.mk0 Y.det h)) ^ s) X
        ∂(volM (Measure.addHaar : Measure k) (Fin n) (Fin n)) < ⊤) :
    Integrable (fun g : GL (Fin n) k => (intM k (Fin n) (Fin n)).indicator (fun _ => (1 : ℝ)) g.val *
      nabs k (gdet g) ^ σ) (haarVol (KO k (Fin n))) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : BorelSpace (GL (Fin n) k) := borel_GL
  have : SecondCountableTopology (GL (Fin n) k) := secondCountable_GL
  have : (volGL (Measure.addHaar : Measure k) (Fin n)).IsHaarMeasure := isHaarMeasure_volGL _
  have : (haarVol (KO k (Fin n))).IsHaarMeasure := isHaarMeasure_haarVol_KO
  rw [Measure.isMulLeftInvariant_eq_smul (haarVol (KO k (Fin n))) (volGL (Measure.addHaar : Measure k) (Fin n))]
  exact (integrable_volGL_of_lintegral _ n σ s hs hI).smul_measure_nnreal

end GlobalTheory.GJTransfer
end
end

section
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal

noncomputable section
namespace GlobalTheory.IntShell

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nabs_pow' (u : kˣ) (m : ℕ) : nabs k (u ^ m) = nabs k u ^ m := by
  simp [nabs, map_pow]

theorem exists_unit_nabs_lt_one : ∃ u : kˣ, nabs k u < 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have h0 : (ϖ : k) ≠ 0 := by simpa using hϖ.ne_zero
  refine ⟨Units.mk0 _ h0, ?_⟩
  rw [nabs_uniformiser hϖ rfl]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast one_lt_resCard k)

theorem cball_one : cball (1 : kˣ) = (𝒪[k] : Set k) := by
  ext y; simp [cball, Valuation.mem_integer_iff]

theorem nabs_le_of_mem_cball {u : kˣ} {y : k} (hy : y ≠ 0) (h : y ∈ cball u) :
    nabs k (Units.mk0 y hy) ≤ nabs k u := by
  rw [nabs_le_iff]; exact h

theorem nabs_ge_of_not_mem_cball {u : kˣ} {y : k} (hy : y ≠ 0) (h : y ∉ cball u) :
    nabs k u ≤ nabs k (Units.mk0 y hy) := by
  rw [nabs_le_iff]; exact (not_le.mp h).le

theorem exists_shell {u : kˣ} (hu : nabs k u < 1) {y : k} (hy : y ≠ 0) (hO : y ∈ 𝒪[k]) :
    ∃ m : ℕ, y ∈ cball (u ^ m) ∧ y ∉ cball (u ^ (m + 1)) := by
  have hP : ∃ n : ℕ, y ∉ cball (u ^ n) := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (nabs_pos k (Units.mk0 y hy)) hu
    refine ⟨n, fun h => ?_⟩
    have := nabs_le_of_mem_cball hy h
    rw [nabs_pow'] at this
    linarith
  have h0 : Nat.find hP ≠ 0 := by
    intro h
    have := Nat.find_spec hP
    rw [h, pow_zero, cball_one] at this
    exact this hO
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h0
  refine ⟨m, ?_, ?_⟩
  · have := Nat.find_min hP (show m < Nat.find hP by omega)
    simpa using this
  · have := Nat.find_spec hP
    rwa [hm] at this

section Meas
variable [MeasurableSpace k] [BorelSpace k]

theorem measure_zero_singleton (μ : Measure k) [μ.IsAddHaarMeasure] : μ {0} = 0 := by
  obtain ⟨u, hu⟩ := exists_unit_nabs_lt_one (k := k)
  have hle : ∀ m : ℕ, μ {0} ≤ ENNReal.ofReal (nabs k u) ^ m * μ (𝒪[k] : Set k) := by
    intro m
    have h1 : ({0} : Set k) ⊆ cball (u ^ m) := by
      intro y hy; rw [Set.mem_singleton_iff.mp hy]; simp [cball]
    refine (measure_mono h1).trans (le_of_eq ?_)
    rw [measure_cball, map_pow]
    congr 1
    simp [nabs, ENNReal.ofReal_coe_nnreal]
  have ht : Filter.Tendsto (fun m : ℕ => ENNReal.ofReal (nabs k u) ^ m * μ (𝒪[k] : Set k)) Filter.atTop
      (nhds (0 * μ (𝒪[k] : Set k))) :=
    ENNReal.Tendsto.mul_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by rw [ENNReal.ofReal_lt_one]; exact hu)) (Or.inr (isCompact_int k).measure_lt_top.ne)
  rw [zero_mul] at ht
  exact le_antisymm (ge_of_tendsto' ht hle) bot_le

end Meas

section Main
variable [MeasurableSpace k] [BorelSpace k]

theorem lintegral_int_nabs_rpow_lt_top (μ : Measure k) [μ.IsAddHaarMeasure] (s : ℝ) (hs : -1 < s) :
    ∫⁻ x, (𝒪[k] : Set k).indicator
      (fun y => ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s) x ∂μ < ⊤ := by
  have hO : μ (𝒪[k] : Set k) < ⊤ := (isCompact_int k).measure_lt_top
  rcases le_or_gt 0 s with hs0 | hs0
  · calc _ ≤ ∫⁻ x, (𝒪[k] : Set k).indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ (𝒪[k] : Set k)
          · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
            refine ENNReal.rpow_le_one ?_ hs0
            rw [ENNReal.ofReal_le_one]
            split_ifs with h
            · exact zero_le_one
            · exact Model.nabs_le_one _ hx
          · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      _ = μ (𝒪[k] : Set k) := by rw [lintegral_indicator_const (isOpen_int k).measurableSet, one_mul]
      _ < ⊤ := hO
  ·
    obtain ⟨u, hu⟩ := exists_unit_nabs_lt_one (k := k)
    set R := ENNReal.ofReal (nabs k u) with hRdef
    have hR0 : R ≠ 0 := by rw [hRdef, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact nabs_pos k u
    have hRt : R ≠ ⊤ := ENNReal.ofReal_ne_top
    have hR1 : R ^ s * R < 1 := by
      have e : R ^ s * R = R ^ (s + 1) := by rw [ENNReal.rpow_add _ _ hR0 hRt, ENNReal.rpow_one]
      rw [e]
      exact ENNReal.rpow_lt_one (by rw [hRdef, ENNReal.ofReal_lt_one]; exact hu) (by linarith)
    have hRs : R ^ s < ⊤ := by
      rw [lt_top_iff_ne_top, ne_eq, ENNReal.rpow_eq_top_iff]
      rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact hR0 h
      · exact hRt h
    have hanti : ∀ a b : ℝ≥0∞, a ≤ b → b ^ s ≤ a ^ s := by
      intro a b h
      have hb : b ^ s = (b ^ (-s))⁻¹ := by rw [← ENNReal.rpow_neg, neg_neg]
      have ha : a ^ s = (a ^ (-s))⁻¹ := by rw [← ENNReal.rpow_neg, neg_neg]
      rw [ha, hb]
      exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow h (show (0:ℝ) ≤ -s by linarith))
    have hae : ∀ᵐ y ∂μ, y ∉ ({0} : Set k) := measure_eq_zero_iff_ae_notMem.mp (measure_zero_singleton μ)
    calc _ ≤ ∫⁻ y, ∑' m : ℕ, (cball (u ^ m)).indicator
            (fun _ => ENNReal.ofReal (nabs k u ^ (m + 1)) ^ s) y ∂μ := by
          refine lintegral_mono_ae (hae.mono fun y hy => ?_)
          have hy0 : y ≠ 0 := hy
          by_cases hx : y ∈ (𝒪[k] : Set k)
          · rw [Set.indicator_of_mem hx, dif_neg hy0]
            obtain ⟨m, hm1, hm2⟩ := exists_shell hu hy0 hx
            refine le_trans ?_ (ENNReal.le_tsum m)
            rw [Set.indicator_of_mem hm1]
            refine hanti _ _ (ENNReal.ofReal_le_ofReal ?_)
            have := nabs_ge_of_not_mem_cball hy0 hm2
            rwa [nabs_pow'] at this
          · rw [Set.indicator_of_notMem hx]; exact bot_le
      _ = ∑' m : ℕ, ENNReal.ofReal (nabs k u ^ (m + 1)) ^ s * μ (cball (u ^ m)) := by
          rw [lintegral_tsum fun m => (measurable_const.indicator (isOpen_cball _).measurableSet).aemeasurable]
          congr 1; funext m
          rw [lintegral_indicator_const (isOpen_cball _).measurableSet]
      _ = ∑' m : ℕ, R ^ s * μ (𝒪[k] : Set k) * (R ^ s * R) ^ m := by
          congr 1; funext m
          have hc : ((distribHaarChar k (u ^ m) : NNReal) : ℝ≥0∞) = R ^ m := by
            rw [map_pow, ENNReal.coe_pow, hRdef]
            congr 1
            simp [nabs, ENNReal.ofReal_coe_nnreal]
          have h2 : ENNReal.ofReal (nabs k u ^ (m + 1)) ^ s = (R ^ s) ^ m * R ^ s := by
            rw [ENNReal.ofReal_pow (nabs_pos k u).le, ← hRdef, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
              mul_comm (((m + 1 : ℕ)) : ℝ) s, ENNReal.rpow_mul, ENNReal.rpow_natCast, pow_succ]
          rw [h2, measure_cball, hc, mul_pow]
          ring
      _ = R ^ s * μ (𝒪[k] : Set k) * (1 - R ^ s * R)⁻¹ := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      _ < ⊤ := by
          refine ENNReal.mul_lt_top (ENNReal.mul_lt_top hRs hO) ?_
          rw [ENNReal.inv_lt_top]
          exact tsub_pos_of_lt hR1

end Main

end GlobalTheory.IntShell
end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_abs_pow_integers_finite : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (μ : Measure k) [μ.IsAddHaarMeasure] (s : ℝ), -1 < s →
    ∫⁻ x, (𝒪[k] : Set k).indicator (fun y => ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s) x ∂μ < ⊤ := by
  atlas_forward_decl GlobalTheory.IntShell.lintegral_int_nabs_rpow_lt_top
end

section
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal

namespace GlobalTheory.KSplit

section OneVar

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem absPow_mul_of_ne_zero {s : ℝ} (hs : s < 0) {a : k} (ha : a ≠ 0) (y : k) :
    ENNReal.ofReal (if h : a * y = 0 then 0 else nabs k (Units.mk0 (a * y) h)) ^ s =
      ENNReal.ofReal (nabs k (Units.mk0 a ha)) ^ s *
        ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s := by
  have hpa : ENNReal.ofReal (nabs k (Units.mk0 a ha)) ≠ 0 := by
    simpa using Model.nabs_pos _
  by_cases hy : y = 0
  · subst hy
    have : ENNReal.ofReal (nabs k (Units.mk0 a ha)) ^ s ≠ 0 := by
      simp [ENNReal.rpow_eq_zero_iff, hpa]
    simp [ENNReal.zero_rpow_of_neg hs, ENNReal.mul_top this]
  · have hay : a * y ≠ 0 := mul_ne_zero ha hy
    have hpy : ENNReal.ofReal (nabs k (Units.mk0 y hy)) ≠ 0 := by
      simpa using Model.nabs_pos _
    have e : Units.mk0 (a * y) hay = Units.mk0 a ha * Units.mk0 y hy := Units.ext rfl
    rw [dif_neg hay, dif_neg hy, e, Model.nabs_mul, ENNReal.ofReal_mul (Model.nabs_pos _).le,
      ENNReal.mul_rpow_of_ne_zero hpa hpy]

theorem absPow_le_one_of_notMem [MeasurableSpace k] [BorelSpace k] {s : ℝ} (hs : s < 0) {y : k} (hy : y ∉ 𝒪[k]) :
    ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s ≤ 1 := by
  have h0 : y ≠ 0 := fun h => hy (h ▸ zero_mem _)
  rw [dif_neg h0]
  refine ENNReal.rpow_le_one_of_one_le_of_neg ?_ hs
  have h1 : valuation k y⁻¹ ≤ 1 := ((valuation k).val_le_one_or_val_inv_le_one y).resolve_left hy
  have h2 : nabs k (Units.mk0 y h0)⁻¹ ≤ 1 := Model.nabs_le_one _ (by simpa using h1)
  have h3 : nabs k (Units.mk0 y h0) * nabs k (Units.mk0 y h0)⁻¹ = 1 := by
    rw [← Model.nabs_mul, mul_inv_cancel, Model.nabs_one]
  have h4 := Model.nabs_pos (Units.mk0 y h0)
  rw [ENNReal.one_le_ofReal]
  nlinarith

end OneVar

theorem lintegral_absPow_affine_le (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (μ : Measure k) [μ.IsAddHaarMeasure] (s : ℝ)
    (hs : s < 0) (a b : k) :
    ∫⁻ x, (𝒪[k] : Set k).indicator (fun y => ENNReal.ofReal (if h : a * y + b = 0 then 0 else nabs k (Units.mk0 (a * y + b) h)) ^ s) x ∂μ ≤
      ENNReal.ofReal (if h : a = 0 then 0 else nabs k (Units.mk0 a h)) ^ s *
        (∫⁻ x, (𝒪[k] : Set k).indicator (fun y => ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s) x ∂μ + μ (𝒪[k] : Set k)) := by
  have hO : IsOpen (𝒪[k] : Set k) := Model.isOpen_int
  by_cases ha : a = 0
  · have hpos : μ (𝒪[k] : Set k) ≠ 0 := (hO.measure_pos μ ⟨0, zero_mem _⟩).ne'
    rw [dif_pos ha, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg hs, ENNReal.top_mul]
    · exact le_top
    · exact fun h => hpos (add_eq_zero.1 h).2
  rw [dif_neg ha]
  set P : k → ℝ≥0∞ := fun y => ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s with hP
  set C : ℝ≥0∞ := ENNReal.ofReal (nabs k (Units.mk0 a ha)) ^ s with hC
  have hCt : C ≠ ⊤ := by
    have hpa : ENNReal.ofReal (nabs k (Units.mk0 a ha)) ≠ 0 := by
      simpa using Model.nabs_pos _
    simp [hC, ENNReal.rpow_eq_top_iff, hpa]
  have hpt : ∀ x, (𝒪[k] : Set k).indicator (fun y => P (a * y + b)) x ≤
      C * ((𝒪[k] : Set k).indicator P (x + b / a) + (𝒪[k] : Set k).indicator 1 x) := by
    intro x
    by_cases hx : x ∈ (𝒪[k] : Set k)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      have e : a * x + b = a * (x + b / a) := by field_simp
      have e' : P (a * x + b) = C * P (x + b / a) := by
        rw [e]; exact absPow_mul_of_ne_zero hs ha _
      rw [e']
      gcongr
      by_cases hx' : x + b / a ∈ (𝒪[k] : Set k)
      · rw [Set.indicator_of_mem hx']; exact le_self_add
      · rw [Set.indicator_of_notMem hx', zero_add]; exact absPow_le_one_of_notMem hs hx'
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  calc _ ≤ ∫⁻ x, C * ((𝒪[k] : Set k).indicator P (x + b / a) + (𝒪[k] : Set k).indicator 1 x) ∂μ :=
        lintegral_mono hpt
    _ = _ := by
        rw [lintegral_const_mul' _ _ hCt,
          lintegral_add_right _ (measurable_one.indicator hO.measurableSet),
          lintegral_add_right_eq_self (fun x => (𝒪[k] : Set k).indicator P x),
          lintegral_indicator_one hO.measurableSet]

end GlobalTheory.KSplit
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_affine_abs_pow_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (μ : Measure k) [μ.IsAddHaarMeasure] (s : ℝ), s < 0 → ∀ a b : k,
    ∫⁻ x, (𝒪[k] : Set k).indicator (fun y => ENNReal.ofReal (if h : a * y + b = 0 then 0 else nabs k (Units.mk0 (a * y + b) h)) ^ s) x ∂μ ≤
      ENNReal.ofReal (if h : a = 0 then 0 else nabs k (Units.mk0 a h)) ^ s *
        (∫⁻ x, (𝒪[k] : Set k).indicator (fun y => ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s) x ∂μ + μ (𝒪[k] : Set k)) := by
  atlas_forward_decl GlobalTheory.KSplit.lintegral_absPow_affine_le
end

section
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal

namespace GlobalTheory.KSplit.CornerFubini

theorem lintegral_prod_le_symm {α β : Type} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] (f : α × β → ℝ≥0∞) :
    ∫⁻ z, f z ∂(μ.prod ν) ≤ ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν := by
  rw [← lintegral_prod_swap]
  exact lintegral_prod_le _

theorem lintegral_cons_le {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (n : ℕ)
    (G : (Fin (n + 1) → α) → ℝ≥0∞) :
    ∫⁻ X, G X ∂(Measure.pi fun _ : Fin (n + 1) => μ) ≤
      ∫⁻ u, ∫⁻ x, G (Fin.cons x u) ∂μ ∂(Measure.pi fun _ : Fin n => μ) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
  rw [h.lintegral_map_equiv G _]
  refine (lintegral_prod_le_symm _ _ _).trans (le_of_eq ?_)
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']

theorem lintegral_col_le {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (m n : ℕ)
    (G : (Fin m → Fin (n + 1) → α) → ℝ≥0∞) :
    ∫⁻ X, G X ∂(Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin (n + 1) => μ) ≤
      ∫⁻ M, ∫⁻ v, G (fun i => Fin.cons (v i) (M i)) ∂(Measure.pi fun _ : Fin m => μ)
        ∂(Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => μ) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0).symm
  have h1 : MeasurePreserving (MeasurableEquiv.piCongrRight fun _ : Fin m => e)
      (Measure.pi fun _ : Fin m => μ.prod (Measure.pi fun _ : Fin n => μ))
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin (n + 1) => μ) :=
    measurePreserving_pi _ _ (f := fun _ : Fin m => e) (fun _ => h)
  have h2 := (measurePreserving_arrowProdEquivProdArrow α (Fin n → α) (Fin m) (fun _ => μ)
    (fun _ => Measure.pi fun _ : Fin n => μ)).symm
  rw [h1.lintegral_map_equiv G _, h2.lintegral_map_equiv _ _]
  refine (lintegral_prod_le_symm _ _ _).trans (le_of_eq ?_)
  refine lintegral_congr fun M => lintegral_congr fun v => congrArg G ?_
  funext i
  change e (v i, M i) = _
  simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']

theorem lintegral_volM_le_corner (k : Type) [MeasurableSpace k] (ν : Measure k) [SigmaFinite ν] (n : ℕ)
    (F : Matrix (Fin (n + 1)) (Fin (n + 1)) k → ℝ≥0∞) :
    ∫⁻ X, F X ∂(volM ν (Fin (n + 1)) (Fin (n + 1))) ≤
      ∫⁻ M, ∫⁻ v, ∫⁻ u, ∫⁻ x, F (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k))))
        ∂ν ∂(Measure.pi fun _ : Fin n => ν) ∂(Measure.pi fun _ : Fin n => ν) ∂(volM ν (Fin n) (Fin n)) := by
  refine (lintegral_cons_le (Measure.pi fun _ : Fin (n + 1) => ν) n F).trans ?_
  refine (lintegral_col_le ν n n _).trans ?_
  refine lintegral_mono fun M => lintegral_mono fun v => ?_
  exact lintegral_cons_le ν n
    (fun r => F (Matrix.of (Fin.cons r (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))))

end GlobalTheory.KSplit.CornerFubini
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_matrix_first_row_column : ∀ (k : Type) [MeasurableSpace k] (ν : Measure k) [SigmaFinite ν] (n : ℕ) (F : Matrix (Fin (n + 1)) (Fin (n + 1)) k → ℝ≥0∞),
    ∫⁻ X, F X ∂(volM ν (Fin (n + 1)) (Fin (n + 1))) ≤
      ∫⁻ M, ∫⁻ v, ∫⁻ u, ∫⁻ x, F (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k))))
        ∂ν ∂(Measure.pi fun _ : Fin n => ν) ∂(Measure.pi fun _ : Fin n => ν) ∂(volM ν (Fin n) (Fin n)) := by
  atlas_forward_decl GlobalTheory.KSplit.CornerFubini.lintegral_volM_le_corner
end

section
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal

namespace GlobalTheory.GJInt

theorem det_blk {k : Type} [Field k] {n : ℕ} (x : k) (u v : Fin n → k) (M : Matrix (Fin n) (Fin n) k) :
    (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))).det =
      x * M.det + (Matrix.of (Fin.cons (Fin.cons 0 u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))).det := by
  rw [det_succ_row_zero, det_succ_row_zero (Matrix.of _), Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [Matrix.submatrix]
  exact Or.inl rfl

theorem mem_intM_blk {k : Type} [Field k] [ValuativeRel k] {n : ℕ} (x : k) (u v : Fin n → k) (M : Matrix (Fin n) (Fin n) k) :
    Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k))) ∈ intM k (Fin (n + 1)) (Fin (n + 1)) ↔
      x ∈ 𝒪[k] ∧ (∀ j, u j ∈ 𝒪[k]) ∧ (∀ i, v i ∈ 𝒪[k]) ∧ M ∈ intM k (Fin n) (Fin n) := by
  simp only [intM, Set.mem_setOf_eq, Fin.forall_fin_succ, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, forall_and]
  tauto

theorem det_mem_int {k : Type} [Field k] [ValuativeRel k] {n : ℕ} {X : Matrix (Fin n) (Fin n) k}
    (hX : X ∈ intM k (Fin n) (Fin n)) : X.det ∈ 𝒪[k] := by
  have h1 := (𝒪[k].subtype).map_det (fun i j => (⟨X i j, hX i j⟩ : 𝒪[k]))
  have h2 : (𝒪[k].subtype).mapMatrix (fun i j => (⟨X i j, hX i j⟩ : 𝒪[k])) = X := by ext; rfl
  rw [h2] at h1
  rw [← h1]
  exact SetLike.coe_mem _

theorem intdet : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (μ : Measure k) [μ.IsAddHaarMeasure] (n : ℕ) (s : ℝ), -1 < s →
    ∫⁻ X : Matrix (Fin n) (Fin n) k, (intM k (Fin n) (Fin n)).indicator (fun Y => ENNReal.ofReal (if h : Y.det = 0 then 0 else nabs k (Units.mk0 Y.det h)) ^ s) X ∂(volM μ (Fin n) (Fin n)) < ⊤ := by
  intro k _ _ _ _ _ _ μ _ n s hs
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hOm : MeasurableSet (𝒪[k] : Set k) := GlobalTheory.SplitWeil.Model.isOpen_int.measurableSet
  have hO : μ (𝒪[k] : Set k) ≠ ⊤ := GlobalTheory.SplitWeil.Model.isCompact_int.measure_lt_top.ne
  set P : k → ℝ≥0∞ := fun y => ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s with hP
  show ∫⁻ X, (intM k (Fin n) (Fin n)).indicator (fun Y => P Y.det) X ∂(volM μ (Fin n) (Fin n)) < ⊤
  rcases le_or_gt 0 s with hs0 | hs0
  · have hb : ∀ X : Matrix (Fin n) (Fin n) k, (intM k (Fin n) (Fin n)).indicator (fun Y => P Y.det) X ≤
        (intM k (Fin n) (Fin n)).indicator 1 X := by
      intro X
      by_cases hX : X ∈ intM k (Fin n) (Fin n)
      · rw [Set.indicator_of_mem hX, Set.indicator_of_mem hX]
        have hdet := det_mem_int hX
        simp only [P, Pi.one_apply]
        split_ifs with h
        · rcases hs0.eq_or_lt with h0 | h0
          · simp [← h0]
          · simp [ENNReal.zero_rpow_of_pos h0]
        · exact ENNReal.rpow_le_one (ENNReal.ofReal_le_one.2 (GlobalTheory.SplitWeil.Model.nabs_le_one _ hdet)) hs0
      · simp [Set.indicator_of_notMem hX]
    have hint : intM k (Fin n) (Fin n) = (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => (𝒪[k] : Set k) : Set (Fin n → Fin n → k)) := by
      ext X; exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    have hm : MeasurableSet (intM k (Fin n) (Fin n)) := by
      rw [hint]; exact MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => hOm
    calc _ ≤ ∫⁻ X, (intM k (Fin n) (Fin n)).indicator 1 X ∂(volM μ (Fin n) (Fin n)) := lintegral_mono hb
      _ = volM μ (Fin n) (Fin n) (intM k (Fin n) (Fin n)) := lintegral_indicator_one hm
      _ < ⊤ := by
        rw [hint, volM]; erw [Measure.pi_pi]
        simp only [Measure.pi_pi]
        exact ENNReal.prod_lt_top fun _ _ => ENNReal.prod_lt_top fun _ _ => hO.lt_top
  · set K : ℝ≥0∞ := ∫⁻ x, (𝒪[k] : Set k).indicator P x ∂μ + μ (𝒪[k] : Set k) with hK
    have hKt : K ≠ ⊤ := ENNReal.add_ne_top.2 ⟨(GlobalTheory.T.lintegral_abs_pow_integers_finite k μ s hs).ne, hO⟩
    induction n with
    | zero =>
      calc _ ≤ ∫⁻ X, 1 ∂(volM μ (Fin 0) (Fin 0)) := lintegral_mono fun X => ?_
        _ < ⊤ := by rw [lintegral_one, volM]; erw [Measure.pi_univ]; simp
      by_cases hX : X ∈ intM k (Fin 0) (Fin 0)
      · rw [Set.indicator_of_mem hX]
        simp [P, GlobalTheory.SplitWeil.Model.nabs_one]
      · simp [Set.indicator_of_notMem hX]
    | succ n ih =>
      let U : Set (Fin n → k) := Set.univ.pi fun _ => (𝒪[k] : Set k)
      have hU : MeasurableSet U := MeasurableSet.univ_pi fun _ => hOm
      have hUv : (Measure.pi fun _ : Fin n => μ) U = μ 𝒪[k] ^ n := by simp [U, Measure.pi_pi]
      have hUt : μ 𝒪[k] ^ n ≠ ⊤ := ENNReal.pow_ne_top hO
      set I := fun M : Matrix (Fin n) (Fin n) k => (intM k (Fin n) (Fin n)).indicator (fun Y => P Y.det) M with hI
      have inner : ∀ M v u, ∫⁻ x, (intM k (Fin (n + 1)) (Fin (n + 1))).indicator (fun Y => P Y.det)
          (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))) ∂μ ≤
          U.indicator (fun _ => U.indicator (fun _ => K * I M) v) u := by
        intro M v u
        by_cases h : u ∈ U ∧ v ∈ U ∧ M ∈ intM k (Fin n) (Fin n)
        · obtain ⟨hu, hv, hM⟩ := h
          rw [Set.indicator_of_mem hu, Set.indicator_of_mem hv]
          simp only [I, Set.indicator_of_mem hM]
          have he : ∀ x, (intM k (Fin (n + 1)) (Fin (n + 1))).indicator (fun Y => P Y.det)
              (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))) =
              (𝒪[k] : Set k).indicator (fun y => P (M.det * y + (Matrix.of (Fin.cons (Fin.cons 0 u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))).det)) x := by
            intro x
            by_cases hx : x ∈ (𝒪[k] : Set k)
            · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((mem_intM_blk x u v M).2 ⟨hx, fun j => hu j trivial, fun i => hv i trivial, hM⟩), det_blk, mul_comm x]
            · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((mem_intM_blk x u v M).1 h).1)]
          simp_rw [he]
          refine (GlobalTheory.T.lintegral_affine_abs_pow_bound k μ s hs0 M.det _).trans (le_of_eq ?_)
          rw [mul_comm]
        · rw [show (fun x => (intM k (Fin (n + 1)) (Fin (n + 1))).indicator (fun Y => P Y.det)
              (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k))))) = fun _ => 0 from ?_]
          · simp
          funext x
          refine Set.indicator_of_notMem (fun hx => h ?_) _
          obtain ⟨_, hu, hv, hM⟩ := (mem_intM_blk x u v M).1 hx
          exact ⟨fun j _ => hu j, fun i _ => hv i, hM⟩
      calc _ ≤ _ := GlobalTheory.T.lintegral_matrix_first_row_column k μ n _
        _ ≤ ∫⁻ M, ∫⁻ v, ∫⁻ u, U.indicator (fun _ => U.indicator (fun _ => K * I M) v) u
              ∂(Measure.pi fun _ : Fin n => μ) ∂(Measure.pi fun _ : Fin n => μ) ∂(volM μ (Fin n) (Fin n)) :=
            lintegral_mono fun M => lintegral_mono fun v => lintegral_mono fun u => inner M v u
        _ = ∫⁻ M, K * I M * (μ 𝒪[k] ^ n * μ 𝒪[k] ^ n) ∂(volM μ (Fin n) (Fin n)) := by
            refine lintegral_congr fun M => ?_
            simp_rw [lintegral_indicator_const hU, hUv]
            rw [lintegral_mul_const' _ _ hUt, lintegral_indicator_const hU, hUv, mul_assoc]
        _ = K * (∫⁻ M, I M ∂(volM μ (Fin n) (Fin n))) * (μ 𝒪[k] ^ n * μ 𝒪[k] ^ n) := by
            rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top hUt hUt), lintegral_const_mul' _ _ hKt]
        _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hKt.lt_top ih) (ENNReal.mul_lt_top hUt.lt_top hUt.lt_top)

end GlobalTheory.GJInt
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_det_pow_integer_matrices_finite : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (μ : Measure k) [μ.IsAddHaarMeasure] (n : ℕ) (s : ℝ), -1 < s →
    ∫⁻ X : Matrix (Fin n) (Fin n) k, (intM k (Fin n) (Fin n)).indicator (fun Y => ENNReal.ofReal (if h : Y.det = 0 then 0 else nabs k (Units.mk0 Y.det h)) ^ s) X ∂(volM μ (Fin n) (Fin n)) < ⊤ := by
  atlas_forward_decl GlobalTheory.GJInt.intdet
end

section
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

noncomputable section
namespace GlobalTheory.GJTransfer

theorem integrable_indicator_intM_mul_nabs_rpow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : ℕ) (σ : ℝ), (n : ℝ) - 1 < σ →
    Integrable (fun g : GL (Fin n) k => (intM k (Fin n) (Fin n)).indicator (fun _ => (1 : ℝ)) g.val * nabs k (gdet g) ^ σ) (haarVol (KO k (Fin n))) := by
  intro k _ _ _ _ _ _ n σ hσ
  have hint : ∀ (μ : Measure k) [μ.IsAddHaarMeasure] (s : ℝ), -1 < s →
      ∫⁻ X : Matrix (Fin n) (Fin n) k, (intM k (Fin n) (Fin n)).indicator (fun Y => ENNReal.ofReal
        (if h : Y.det = 0 then 0 else nabs k (Units.mk0 Y.det h)) ^ s) X ∂(volM μ (Fin n) (Fin n)) < ⊤ := by
    intro μ _ s hs
    exact GlobalTheory.T.lintegral_det_pow_integer_matrices_finite k μ n s hs
  exact integrable_haarVol_of_lintegral n σ (min (σ - n) 0) (min_le_left _ _)
    (hint _ _ (lt_min (by linarith) (by norm_num)))

end GlobalTheory.GJTransfer
end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_det_pow_indicator_integer_gl : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : ℕ) (σ : ℝ), (n : ℝ) - 1 < σ →
    Integrable (fun g : GL (Fin n) k => (intM k (Fin n) (Fin n)).indicator (fun _ => (1 : ℝ)) g.val * nabs k (gdet g) ^ σ) (haarVol (KO k (Fin n))) := by
  atlas_forward_decl GlobalTheory.GJTransfer.integrable_indicator_intM_mul_nabs_rpow
end

section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit

noncomputable section
namespace GlobalTheory.GJIntegrable

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_unit_bound {m : ℕ} {K : Set (Matrix (Fin m) (Fin m) k)} (hK : IsCompact K) :
    ∃ c : kˣ, ∀ X ∈ K, ∀ i j, valuation k (X i j) ≤ valuation k (c : k) := by
  obtain ⟨y, hy⟩ := hK.elim_directed_cover
    (fun y : kˣ => {X : Matrix (Fin m) (Fin m) k | ∀ i j, X i j ∈ cball y})
    (fun y => by
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        (isOpen_cball y).preimage ((continuous_apply j).comp (continuous_apply i)))
    (fun X _ => by
      let f : Option (Fin m × Fin m) → k := fun p => match p with
        | none => 1
        | some q => X q.1 q.2
      obtain ⟨p, hp⟩ := Finite.exists_max fun q => valuation k (f q)
      have h1 : valuation k (f p) ≠ 0 := by
        have := hp none
        simp only [f, map_one] at this
        exact ne_of_gt (lt_of_lt_of_le zero_lt_one this)
      have h0 : f p ≠ 0 := fun h => h1 (by rw [h, map_zero])
      exact Set.mem_iUnion.2 ⟨Units.mk0 _ h0, fun i j => by
        show valuation k (X i j) ≤ valuation k (f p)
        exact hp (some (i, j))⟩)
    (fun a b => by
      rcases le_total (valuation k (a : k)) (valuation k (b : k)) with h | h
      · exact ⟨b, fun X hX i j => le_trans (show valuation k (X i j) ≤ _ from hX i j) h, subset_rfl⟩
      · exact ⟨a, subset_rfl, fun X hX i j => le_trans (show valuation k (X i j) ≤ _ from hX i j) h⟩)
  exact ⟨y, fun X hX i j => hy hX i j⟩

theorem isLocallyConstant_char {ν : kˣ →* ℂˣ} (hν : IsOpen (ν.ker : Set kˣ)) :
    IsLocallyConstant fun x : kˣ => ((ν x : ℂˣ) : ℂ) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x0 => ?_
  have hn : (fun x => x0⁻¹ * x) ⁻¹' (ν.ker : Set kˣ) ∈ nhds x0 :=
    (hν.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  filter_upwards [hn] with x hx
  have hx' : ν (x0⁻¹ * x) = 1 := hx
  rw [map_mul, map_inv, inv_mul_eq_one] at hx'
  rw [hx']

theorem nabs_pos_unit (x : kˣ) : 0 < nabs k x := NNReal.coe_pos.mpr distribHaarChar_pos

theorem nabs_pow (x : kˣ) (m : ℕ) : nabs k (x ^ m) = nabs k x ^ m := by
  induction m with
  | zero => simp [nabs]
  | succ m ih => rw [pow_succ, nabs_mul, ih, pow_succ]

theorem integrable_gjIntegrand : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : ℕ) (ν : kˣ →* ℂˣ) (z : ℂ), IsSmU ν → (n : ℝ) - 1 < z.re →
    ∀ φ ∈ SB (Matrix (Fin n) (Fin n) k), Integrable (fun g : GL (Fin n) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) (haarVol (KO k (Fin n))) := by
  intro k _ _ _ _ _ _ n ν z hν hz φ hφ
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : BorelSpace (GL (Fin n) k) := borel_GL
  have : MeasurableMul (GL (Fin n) k) := inferInstance
  have : (haarVol (KO k (Fin n))).IsHaarMeasure := isHaarMeasure_haarVol_KO
  obtain ⟨hl, hK⟩ : IsLocallyConstant φ ∧ HasCompactSupport φ := hφ
  obtain ⟨C, hC⟩ := hl.continuous.bounded_above_of_compact_support hK
  obtain ⟨c, hc⟩ := exists_unit_bound (k := k) hK.isCompact
  set s : GL (Fin n) k := Units.map (algebraMap k (Matrix (Fin n) (Fin n) k)).toMonoidHom c⁻¹ with hs
  have hsv : ∀ g : GL (Fin n) k, (s * g).val = ((c⁻¹ : kˣ) : k) • g.val := by
    intro g
    simp [hs, Algebra.smul_def]
  have hsd : ∀ g : GL (Fin n) k, gdet g = c ^ n * gdet (s * g) := by
    intro g
    ext
    simp only [gdet, Units.val_mul, Units.val_pow_eq_pow_val, GeneralLinearGroup.val_det_apply, hsv,
      Matrix.det_smul, Fintype.card_fin, ← mul_assoc, ← mul_pow]
    simp
  set T : GL (Fin n) k → ℝ := fun g =>
    (intM k (Fin n) (Fin n)).indicator (fun _ => (1 : ℝ)) g.val * nabs k (gdet g) ^ z.re with hT
  have hTi : Integrable T (haarVol (KO k (Fin n))) := GlobalTheory.T.integrable_det_pow_indicator_integer_gl k n z.re hz
  have hT0 : ∀ g, 0 ≤ T g := fun g =>
    mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (Real.rpow_nonneg (nabs_pos_unit _).le _)
  set D : ℝ := |C| * (nabs k c ^ n) ^ z.re with hD
  have hcont : Continuous fun g : GL (Fin n) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z := by
    refine ((hl.continuous.comp Units.continuous_val).mul
      ((isLocallyConstant_char hν.1).continuous.comp GeneralLinearGroup.continuous_det)).mul ?_
    exact (((isLocallyConstant_nabs k).comp fun r : ℝ => (r : ℂ) ^ z).continuous).comp
      GeneralLinearGroup.continuous_det
  refine ((hTi.comp_mul_left s).const_mul D).mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => ?_)
  have hp := nabs_pos_unit (gdet g)
  have hu : ‖((ν (gdet g) : ℂˣ) : ℂ)‖ = 1 := hν.2 _
  rw [norm_mul, norm_mul, hu, mul_one, apow, Complex.norm_cpow_eq_rpow_re_of_pos hp]
  by_cases h0 : φ g.val = 0
  · rw [h0, norm_zero, zero_mul]
    exact mul_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (pow_nonneg (nabs_pos_unit c).le _) _)) (hT0 _)
  have hmem : (s * g).val ∈ intM k (Fin n) (Fin n) := by
    intro i j
    rw [hsv, Matrix.smul_apply, smul_eq_mul, Valuation.mem_integer_iff, map_mul]
    have h1 := hc g.val (subset_tsupport _ h0) i j
    have h2 : valuation k ((c⁻¹ : kˣ) : k) * valuation k (c : k) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    calc valuation k ((c⁻¹ : kˣ) : k) * valuation k (g.val i j)
        ≤ valuation k ((c⁻¹ : kˣ) : k) * valuation k (c : k) := by gcongr
      _ = 1 := h2
  have hTs : T (s * g) = nabs k (gdet (s * g)) ^ z.re := by
    simp only [hT, Set.indicator_of_mem hmem, one_mul]
  show _ ≤ D * T (s * g)
  rw [hTs, hsd g, nabs_mul, nabs_pow, Real.mul_rpow (pow_nonneg (nabs_pos_unit c).le _) (nabs_pos_unit _).le, hD]
  have hq := Real.rpow_nonneg (pow_nonneg (nabs_pos_unit c).le n) z.re
  have hr := Real.rpow_nonneg (nabs_pos_unit (gdet (s * g))).le z.re
  calc ‖φ g.val‖ * ((nabs k c ^ n) ^ z.re * nabs k (gdet (s * g)) ^ z.re)
      ≤ |C| * ((nabs k c ^ n) ^ z.re * nabs k (gdet (s * g)) ^ z.re) :=
        mul_le_mul_of_nonneg_right ((hC _).trans (le_abs_self C)) (mul_nonneg hq hr)
    _ = _ := by ring

end GlobalTheory.GJIntegrable
end
end

section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_zeta_integral_matrix_schwartz : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : ℕ) (ν : kˣ →* ℂˣ) (z : ℂ), IsSmU ν → (n : ℝ) - 1 < z.re →
    ∀ φ ∈ SB (Matrix (Fin n) (Fin n) k), Integrable (fun g : GL (Fin n) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) (haarVol (KO k (Fin n))) := by
  first | exact @GlobalTheory.GJIntegrable.integrable_gjIntegrand | exact GlobalTheory.GJIntegrable.integrable_gjIntegrand | (intros; apply GlobalTheory.GJIntegrable.integrable_gjIntegrand <;> assumption)
end

section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit

noncomputable section
namespace GlobalTheory.GJForm

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem isEqv_integral (n : ℕ) (ν : kˣ →* ℂˣ) (z : ℂ) (hν : IsSmU ν) (hz : (n : ℝ) - 1 < z.re) :
    IsEqv ν z (fun φ : Matrix (Fin n) (Fin n) k → ℂ =>
      ∫ g : GL (Fin n) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol (KO k (Fin n)))) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : BorelSpace (GL (Fin n) k) := borel_GL
  have : MeasurableMul (GL (Fin n) k) := inferInstance
  have : (haarVol (KO k (Fin n))).IsHaarMeasure := isHaarMeasure_haarVol_KO
  refine ⟨fun φ hφ φ' hφ' => ?_, fun c φ hφ => ?_, fun g₁ g₂ φ hφ => ?_⟩
  · dsimp only
    rw [← integral_add (GlobalTheory.T.integrable_zeta_integral_matrix_schwartz k n ν z hν hz φ hφ) (GlobalTheory.T.integrable_zeta_integral_matrix_schwartz k n ν z hν hz φ' hφ')]
    congr 1; funext g; simp only [Pi.add_apply]; ring
  · dsimp only
    rw [← integral_const_mul]; congr 1; funext g; simp only [Pi.smul_apply, smul_eq_mul]; ring
  · set F : GL (Fin n) k → ℂ := fun g => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z with hF
    set d := gdet g₁ * gdet g₂ with hd'
    have hd : (ν d : ℂ) * apow d z ≠ 0 := mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)
    have key : ∀ g : GL (Fin n) k, φ (g₁.val * g.val * g₂.val) * (ν (gdet g) : ℂ) * apow (gdet g) z
        = ((ν d : ℂ) * apow d z)⁻¹ * F (g₁ * (g * g₂)) := by
      intro g
      have e : gdet (g₁ * (g * g₂)) = gdet g * d := by
        rw [gdet_mul, gdet_mul, hd', mul_left_comm]
      have ha := apow_ne_zero d z
      have hn : (ν d : ℂ) ≠ 0 := Units.ne_zero _
      simp only [hF, e, map_mul, Units.val_mul, apow_mul, Matrix.mul_assoc]
      field_simp
    simp_rw [key]
    rw [integral_const_mul]
    have h1 : ∫ g, F (g₁ * (g * g₂)) ∂(haarVol (KO k (Fin n))) = ∫ g, F g ∂(haarVol (KO k (Fin n))) := by
      have h2 := integral_mul_right_eq_self (μ := haarVol (KO k (Fin n))) (fun g => F (g₁ * g)) g₂
      exact h2.trans (integral_mul_left_eq_self (μ := haarVol (KO k (Fin n))) F g₁)
    rw [h1, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]

theorem exists_integral_ne_zero (n : ℕ) (ν : kˣ →* ℂˣ) (z : ℂ) (hν : IsSmU ν) :
    ∃ φ ∈ SB (Matrix (Fin n) (Fin n) k),
      ∫ g : GL (Fin n) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol (KO k (Fin n))) ≠ 0 := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : BorelSpace (GL (Fin n) k) := borel_GL
  have : MeasurableMul (GL (Fin n) k) := inferInstance
  have : (haarVol (KO k (Fin n))).IsHaarMeasure := isHaarMeasure_haarVol_KO
  set H : Subgroup (GL (Fin n) k) := KO k (Fin n) ⊓ (ν.comp Matrix.GeneralLinearGroup.det).ker with hH
  have hHo : IsOpen (H : Set (GL (Fin n) k)) := by
    rw [hH, Subgroup.coe_inf]
    exact isOpen_KO.inter (hν.1.preimage Matrix.GeneralLinearGroup.continuous_det)
  have hHc : IsCompact (H : Set (GL (Fin n) k)) :=
    isCompact_KO.of_isClosed_subset (H.isClosed_of_isOpen hHo) fun x hx => hx.1
  have hemb : Topology.IsOpenEmbedding (fun g : GL (Fin n) k => g.val) := by
    refine { toIsEmbedding := isEmbedding_val_GL, isOpen_range := ?_ }
    have e : Set.range (fun g : GL (Fin n) k => g.val) = {A | A.det ≠ 0} := by
      ext A
      refine ⟨?_, fun h => ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A h, rfl⟩⟩
      rintro ⟨g, rfl⟩
      exact g.det_ne_zero
    rw [e]
    exact isOpen_ne_fun (continuous_id.matrix_det) continuous_const
  set S : Set (Matrix (Fin n) (Fin n) k) := (fun g : GL (Fin n) k => g.val) '' H with hS
  have hSc : IsCompact S := hHc.image Units.continuous_val
  have hSo : IsClopen S := ⟨hSc.isClosed, hemb.isOpenMap _ hHo⟩
  refine ⟨S.indicator 1, ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hSo).isLocallyConstant,
    HasCompactSupport.intro hSc fun x hx => Set.indicator_of_notMem hx _⟩, ?_⟩
  have hfun : (fun g : GL (Fin n) k => S.indicator 1 g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) =
      (H : Set (GL (Fin n) k)).indicator (fun _ => (1 : ℂ)) := by
    funext g
    by_cases hg : g ∈ H
    · have h1 : g.val ∈ S := ⟨g, hg, rfl⟩
      have h2 : ν (gdet g) = 1 := hg.2
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem (show g ∈ (H : Set _) from hg), h2,
        apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg.1)]
      simp
    · have h1 : g.val ∉ S := by
        rintro ⟨g', hg', e⟩
        exact hg (Units.ext e ▸ hg')
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem (show g ∉ (H : Set _) from hg)]
      simp
  simp only [hfun]
  have hI := integral_indicator_const (μ := haarVol (KO k (Fin n))) (1 : ℂ) hHo.measurableSet
  have hpos := hHo.measure_pos (haarVol (KO k (Fin n))) ⟨1, H.one_mem⟩
  have hfin := hHc.measure_lt_top (μ := haarVol (KO k (Fin n)))
  erw [hI]
  rw [Complex.real_smul, mul_one, Complex.ofReal_ne_zero, measureReal_def]
  exact (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'

theorem isEqv_integral_and_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : ℕ) (ν : kˣ →* ℂˣ) (z : ℂ), IsSmU ν → (n : ℝ) - 1 < z.re →
    IsEqv ν z (fun φ : Matrix (Fin n) (Fin n) k → ℂ => ∫ g : GL (Fin n) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol (KO k (Fin n)))) ∧
    ∃ φ ∈ SB (Matrix (Fin n) (Fin n) k), ∫ g : GL (Fin n) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol (KO k (Fin n))) ≠ 0 :=
  fun _ _ _ _ _ _ _ n ν z hν hz => ⟨isEqv_integral n ν z hν hz, exists_integral_ne_zero n ν z hν⟩

end GlobalTheory.GJForm
end
end

section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeta_integral_equivariant_nonzero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : ℕ) (ν : kˣ →* ℂˣ) (z : ℂ), IsSmU ν → (n : ℝ) - 1 < z.re →
    IsEqv ν z (fun φ : Matrix (Fin n) (Fin n) k → ℂ => ∫ g : GL (Fin n) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol (KO k (Fin n)))) ∧
    ∃ φ ∈ SB (Matrix (Fin n) (Fin n) k), ∫ g : GL (Fin n) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol (KO k (Fin n))) ≠ 0 := by
  first | exact @GlobalTheory.GJForm.isEqv_integral_and_ne_zero | exact GlobalTheory.GJForm.isEqv_integral_and_ne_zero | (intros; apply GlobalTheory.GJForm.isEqv_integral_and_ne_zero <;> assumption)
end

section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

noncomputable section
namespace GlobalTheory.ShellSumEqv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_unique_shell {ϖ : kˣ} (hϖ : IsUnif ϖ) {a : ℕ} (g : GL (Fin a) k) :
    ∃! m : {m : Fin a → ℤ // Antitone m}, g ∈ shellSet ϖ m.1 := by
  obtain ⟨m, hm, x, hx, y, hy, e⟩ := GlobalTheory.SortedCartan.cartan_antitone k a ϖ hϖ g
  have ht : ∀ m : Fin a → ℤ, GlobalTheory.GLDoubling.torusElt k (Fin a) ϖ m = diagGL fun i => ϖ ^ m i :=
    fun m => Units.ext (by rw [GlobalTheory.GLDoubling.val_torusElt, diagGL_val]; simp [Units.val_zpow_eq_zpow_val])
  refine ⟨⟨m, hm⟩, mem_shellSet.2 ⟨x, hx, y, hy, by rw [e, ht]⟩, ?_⟩
  rintro ⟨m', hm'⟩ hmem
  obtain ⟨x', hx', y', hy', e'⟩ := mem_shellSet.1 hmem
  have E : (x'⁻¹ * x) * diagGL (fun i => ϖ ^ m i) * (y * y'⁻¹) = diagGL fun i => ϖ ^ m' i := by
    have h1 : x * diagGL (fun i => ϖ ^ m i) * y = x' * diagGL (fun i => ϖ ^ m' i) * y' := by
      rw [← ht, ← e]; exact e'
    calc _ = x'⁻¹ * (x * diagGL (fun i => ϖ ^ m i) * y) * y'⁻¹ := by group
      _ = _ := by rw [h1]; group
  have E' := congrArg Units.val E
  simp only [Units.val_mul, diagGL_val, Units.val_zpow_eq_zpow_val] at E'
  exact Subtype.ext (Formalism.UG.P.cartan_unique_gen 𝒪[k] (valuation k) (fun _ => Iff.rfl) (ϖ : k) ϖ.ne_zero
    (hϖ ▸ uniformizer_lt_one) m m' hm hm' (x'⁻¹ * x) (mul_mem (inv_mem hx') hx) (y * y'⁻¹)
    (mul_mem hy (inv_mem hy')) (by simpa only [Units.val_mul] using E')).symm

theorem isOpen_shellSet (ϖ : kˣ) {a : ℕ} (m : Fin a → ℤ) : IsOpen (shellSet ϖ m : Set (GL (Fin a) k)) := by
  have : shellSet ϖ m = ⋃ x ∈ (KO k (Fin a) : Set (GL (Fin a) k)),
      (fun g => (x * diagGL (fun i => ϖ ^ m i))⁻¹ * g) ⁻¹' (KO k (Fin a) : Set _) := by
    ext g
    simp only [mem_shellSet, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨x, hx, by simpa [mul_assoc] using hy⟩
    · rintro ⟨x, hx, hy⟩
      exact ⟨x, hx, _, hy, by group⟩
  rw [this]
  exact isOpen_biUnion fun x _ => isOpen_KO.preimage (continuous_const.mul continuous_id)

theorem apow_of_mem_shellSet {ϖ : kˣ} {a : ℕ} {m : Fin a → ℤ} {g : GL (Fin a) k} (hg : g ∈ shellSet ϖ m)
    (w : ℂ) : apow (gdet g) w = apow (gdet (diagGL fun i => ϖ ^ m i)) w := by
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_shellSet.1 hg
  rw [gdet_mul, gdet_mul, apow_mul, apow_mul, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hx),
    apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hy)]
  ring

theorem continuous_char_det {a : ℕ} {ν : kˣ →* ℂˣ} (hν : IsSmU ν) :
    Continuous fun g : GL (Fin a) k => ((ν (gdet g) : ℂˣ) : ℂ) := by
  set χ : GL (Fin a) k →* ℂˣ := ν.comp Matrix.GeneralLinearGroup.det with hχd
  have hcd : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin a) k → kˣ) :=
    Units.continuous_iff.2 ⟨Units.continuous_val.matrix_det, Units.continuous_coe_inv.matrix_det⟩
  have hχ : IsOpen (χ.ker : Set (GL (Fin a) k)) := hν.1.preimage hcd
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).mpr fun g0 => ?_)
  have hn : (fun g => g0⁻¹ * g) ⁻¹' (χ.ker : Set (GL (Fin a) k)) ∈ nhds g0 :=
    (hχ.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  filter_upwards [hn] with g hg
  have hg' : χ (g0⁻¹ * g) = 1 := hg
  have e : χ g = χ g0 := by
    have := congrArg (χ g0 * ·) hg'
    simp only [← map_mul, mul_inv_cancel_left, mul_one] at this
    exact this
  exact congrArg (fun u : ℂˣ => (u : ℂ)) e

variable [MeasurableSpace k] [BorelSpace k]

theorem exists_integrable {a : ℕ} {ν : kˣ →* ℂˣ} (hν : IsSmU ν) {φ : Matrix (Fin a) (Fin a) k → ℂ}
    (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k)) : ∃ B : ℝ, ∀ w : ℂ, B < w.re →
      Integrable (fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) w)
        (haarVol (KO k (Fin a))) := by
  obtain ⟨b, hb⟩ := GlobalTheory.ZetaConvergence.integrable_zetaIntegrand k Measure.addHaar (Fin a)
    (fun g => ((ν (gdet g) : ℂˣ) : ℂ)) 0 (continuous_char_det hν)
    (fun N => ⟨1, fun g _ => by simp [hν.2]⟩) φ hφ
  refine ⟨b + ((a : ℝ) - 1) / 2, fun w hw => ?_⟩
  have h1 := hb (w - ((a : ℂ) - 1) / 2) (by
    have : (((a : ℂ) - 1) / 2).re = ((a : ℝ) - 1) / 2 := by simp
    rw [Complex.sub_re, this]; linarith)
  have hfun : GlobalTheory.InertSupp.zetaIntegrand φ (fun g => ((ν (gdet g) : ℂˣ) : ℂ)) (w - ((a : ℂ) - 1) / 2) =
      fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) w := by
    funext g
    simp [GlobalTheory.InertSupp.zetaIntegrand, GlobalTheory.SmGL.val_absPow, apow]
  rw [hfun] at h1
  haveI := isHaarMeasure_volGL (k := k) (n := Fin a) Measure.addHaar
  rw [Measure.isMulLeftInvariant_eq_smul (haarVol (KO k (Fin a))) (volGL Measure.addHaar (Fin a))]
  exact h1.smul_measure_nnreal

section Shells
variable {ϖ : kˣ} {ν : kˣ →* ℂˣ} {e : ℕ}

theorem finite_shells (hϖ : IsUnif ϖ) (hram : ¬ IsUnram ν) (hcond : CondLE ϖ e ν) {a : ℕ}
    {φ : Matrix (Fin a) (Fin a) k → ℂ} (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k)) :
    {m : {m : Fin a → ℤ // Antitone m} | ∃ z : ℂ, shell (haarVol (KO k (Fin a))) ϖ ν z φ m.1 ≠ 0}.Finite :=
  (GlobalTheory.T.zetaIntegralShells_vanish_beyondPeriod_ramified k ϖ hϖ ν e hram hcond a (haarVol (KO k (Fin a))) φ hφ).2.2.2

theorem integrableOn_shell (hϖ : IsUnif ϖ) (hram : ¬ IsUnram ν) (hcond : CondLE ϖ e ν) {a : ℕ}
    {φ : Matrix (Fin a) (Fin a) k → ℂ} (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k)) (m : Fin a → ℤ) (w : ℂ) :
    IntegrableOn (fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) w) (shellSet ϖ m)
      (haarVol (KO k (Fin a))) :=
  (GlobalTheory.T.zetaIntegralShells_vanish_beyondPeriod_ramified k ϖ hϖ ν e hram hcond a (haarVol (KO k (Fin a))) φ hφ).1 m w

theorem support_finite (hϖ : IsUnif ϖ) (hram : ¬ IsUnram ν) (hcond : CondLE ϖ e ν) {a : ℕ}
    {φ : Matrix (Fin a) (Fin a) k → ℂ} (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k)) (w : ℂ) :
    (Function.support fun m : {m : Fin a → ℤ // Antitone m} =>
      shell (haarVol (KO k (Fin a))) ϖ ν w φ m.1).Finite :=
  (finite_shells hϖ hram hcond hφ).subset fun m hm => ⟨w, hm⟩

theorem integral_eq_shellSum (hϖ : IsUnif ϖ) (hram : ¬ IsUnram ν) (hcond : CondLE ϖ e ν) {a : ℕ}
    {φ : Matrix (Fin a) (Fin a) k → ℂ} (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k)) {w : ℂ}
    (hint : Integrable (fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) w)
      (haarVol (KO k (Fin a)))) :
    ∫ g, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) w ∂(haarVol (KO k (Fin a))) =
      shellSum (haarVol (KO k (Fin a))) ϖ ν w φ := by
  set S : {m : Fin a → ℤ // Antitone m} → Set (GL (Fin a) k) := fun m => shellSet ϖ m.1 with hS
  have hU : ⋃ m, S m = Set.univ :=
    Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 (exists_unique_shell hϖ g).exists
  have hd : Pairwise (Function.onFun Disjoint S) := fun m m' hne =>
    Set.disjoint_left.2 fun g h1 h2 => hne ((exists_unique_shell hϖ g).unique h1 h2)
  haveI : BorelSpace (GL (Fin a) k) := borel_GL
  have hm : ∀ m, MeasurableSet (S m) := fun m => (isOpen_shellSet ϖ m.1).measurableSet
  calc _ = ∫ g in ⋃ m, S m, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) w ∂(haarVol (KO k (Fin a))) := by
        rw [hU, Measure.restrict_univ]
    _ = ∑' m, ∫ g in S m, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) w ∂(haarVol (KO k (Fin a))) :=
        integral_iUnion hm hd hint.integrableOn
    _ = ∑ᶠ m, ∫ g in S m, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) w ∂(haarVol (KO k (Fin a))) :=
        tsum_eq_finsum (support_finite hϖ hram hcond hφ w)
    _ = _ := rfl

theorem shell_eq_mul [BorelSpace k] {a : ℕ} (μ : Measure (GL (Fin a) k)) (φ : Matrix (Fin a) (Fin a) k → ℂ) (m : Fin a → ℤ)
    (w : ℂ) : shell μ ϖ ν w φ m = (∫ g in shellSet ϖ m, φ g.val * (ν (gdet g) : ℂ) ∂μ) *
      apow (gdet (diagGL fun i => ϖ ^ m i)) w := by
  unfold shell
  rw [← integral_mul_const]
  haveI : BorelSpace (GL (Fin a) k) := borel_GL
  exact setIntegral_congr_fun (isOpen_shellSet ϖ m).measurableSet fun g hg => by
    simp only [apow_of_mem_shellSet hg]

theorem differentiable_shellSum (hϖ : IsUnif ϖ) (hram : ¬ IsUnram ν) (hcond : CondLE ϖ e ν) {a : ℕ}
    {φ : Matrix (Fin a) (Fin a) k → ℂ} (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k)) :
    Differentiable ℂ fun w => shellSum (haarVol (KO k (Fin a))) ϖ ν w φ := by
  set F := (finite_shells hϖ hram hcond hφ).toFinset
  have h : (fun w => shellSum (haarVol (KO k (Fin a))) ϖ ν w φ) =
      fun w => ∑ m ∈ F, shell (haarVol (KO k (Fin a))) ϖ ν w φ m.1 := by
    funext w
    refine finsum_eq_sum_of_support_subset _ fun m hm => ?_
    simpa [F] using (⟨w, hm⟩ : ∃ z : ℂ, shell (haarVol (KO k (Fin a))) ϖ ν z φ m.1 ≠ 0)
  rw [h]
  refine Differentiable.fun_sum fun m _ => ?_
  show Differentiable ℂ fun w => shell (haarVol (KO k (Fin a))) ϖ ν w φ m.1
  rw [funext fun w => shell_eq_mul (ϖ := ϖ) (ν := ν) (haarVol (KO k (Fin a))) φ m.1 w]
  refine Differentiable.const_mul ?_ _
  have hp := nabs_pos' (gdet (diagGL fun i => ϖ ^ m.1 i))
  exact differentiable_id.const_cpow (Or.inl (by exact_mod_cast hp.ne'))

end Shells

section Main
variable {ϖ : kˣ} {ν : kˣ →* ℂˣ} {e : ℕ}

theorem differentiable_apow (x : kˣ) : Differentiable ℂ fun w => apow x w := by
  have hp := nabs_pos' x
  unfold apow
  exact differentiable_id.const_cpow (Or.inl (by exact_mod_cast hp.ne'))

theorem shellSum_add (hϖ : IsUnif ϖ) (hram : ¬ IsUnram ν) (hcond : CondLE ϖ e ν) {a : ℕ}
    {φ φ' : Matrix (Fin a) (Fin a) k → ℂ} (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k))
    (hφ' : φ' ∈ SB (Matrix (Fin a) (Fin a) k)) (w : ℂ) :
    shellSum (haarVol (KO k (Fin a))) ϖ ν w (φ + φ') =
      shellSum (haarVol (KO k (Fin a))) ϖ ν w φ + shellSum (haarVol (KO k (Fin a))) ϖ ν w φ' := by
  unfold shellSum
  rw [← finsum_add_distrib (support_finite hϖ hram hcond hφ w) (support_finite hϖ hram hcond hφ' w)]
  refine finsum_congr fun m => ?_
  unfold shell
  rw [← integral_add (integrableOn_shell hϖ hram hcond hφ m.1 w) (integrableOn_shell hϖ hram hcond hφ' m.1 w)]
  congr 1
  funext g
  simp only [Pi.add_apply]
  ring

theorem shellSum_eqv (hϖ : IsUnif ϖ) (hν : IsSmU ν) (hram : ¬ IsUnram ν) (hcond : CondLE ϖ e ν) {a : ℕ}
    (g₁ g₂ : GL (Fin a) k) {φ : Matrix (Fin a) (Fin a) k → ℂ} (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k)) (z : ℂ) :
    (ν (gdet g₁ * gdet g₂) : ℂ) * apow (gdet g₁ * gdet g₂) z *
      shellSum (haarVol (KO k (Fin a))) ϖ ν z (fun X => φ (g₁.val * X * g₂.val)) =
      shellSum (haarVol (KO k (Fin a))) ϖ ν z φ := by
  have hφ' := comp_mul_mem_SB g₁ g₂ hφ
  obtain ⟨B₁, h₁⟩ := exists_integrable hν hφ
  obtain ⟨B₂, h₂⟩ := exists_integrable hν hφ'
  set B := max (max B₁ B₂) ((a : ℝ) - 1) with hB
  have hL : Differentiable ℂ fun w => (ν (gdet g₁ * gdet g₂) : ℂ) * apow (gdet g₁ * gdet g₂) w *
      shellSum (haarVol (KO k (Fin a))) ϖ ν w (fun X => φ (g₁.val * X * g₂.val)) :=
    ((differentiable_apow _).const_mul _).mul (differentiable_shellSum hϖ hram hcond hφ')
  have hR := differentiable_shellSum hϖ hram hcond hφ
  have ho : IsOpen {w : ℂ | B < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hE := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (fun w _ => hL.analyticAt w)
    (fun w _ => hR.analyticAt w) isPreconnected_univ (Set.mem_univ (((B + 1 : ℝ)) : ℂ)) (by
      filter_upwards [ho.mem_nhds (show B < (((B + 1 : ℝ)) : ℂ).re by simp)] with w hw
      have hw : B < w.re := hw
      have hB1 : B₁ < w.re := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hw
      have hB2 : B₂ < w.re := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hw
      have hB3 : (a : ℝ) - 1 < w.re := lt_of_le_of_lt (le_max_right _ _) hw
      rw [← integral_eq_shellSum hϖ hram hcond hφ (h₁ w hB1),
        ← integral_eq_shellSum hϖ hram hcond hφ' (h₂ w hB2)]
      exact (GlobalTheory.T.zeta_integral_equivariant_nonzero k a ν w hν hB3).1.2.2 g₁ g₂ φ hφ)
  exact hE (Set.mem_univ z)

theorem exists_ne_zero (hϖ : IsUnif ϖ) (hcond : CondLE ϖ e ν) {a : ℕ} (z : ℂ) :
    ∃ φ ∈ SB (Matrix (Fin a) (Fin a) k), shellSum (haarVol (KO k (Fin a))) ϖ ν z φ ≠ 0 := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  haveI : BorelSpace (GL (Fin a) k) := borel_GL
  set D := detCong (ϖ ^ e) (Fin a) with hDdef
  have hDo : IsOpen (D : Set (GL (Fin a) k)) := isOpen_detCong _ _
  have hDc : IsClosed (D : Set (GL (Fin a) k)) := D.isClosed_of_isOpen hDo
  have hDK : (D : Set (GL (Fin a) k)) ⊆ KO k (Fin a) := fun g hg => hg.1
  have hDk : IsCompact (D : Set (GL (Fin a) k)) := isCompact_KO.of_isClosed_subset hDc hDK
  have hoe : Topology.IsOpenEmbedding (fun g : GL (Fin a) k => g.val) := by
    refine ⟨isEmbedding_val_GL, ?_⟩
    have : Set.range (fun g : GL (Fin a) k => g.val) = {x : Matrix (Fin a) (Fin a) k | x.det ≠ 0} := by
      ext x
      simp only [Set.mem_range, Set.mem_setOf_eq]
      rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
      rfl
    rw [this]
    exact isOpen_ne_fun (continuous_id.matrix_det) continuous_const
  set T : Set (Matrix (Fin a) (Fin a) k) := (fun g : GL (Fin a) k => g.val) '' D with hTdef
  have hTk : IsCompact T := hDk.image hoe.continuous
  have hTo : IsOpen T := hoe.isOpenMap _ hDo
  have hT : ∀ g : GL (Fin a) k, g.val ∈ T ↔ g ∈ D := fun g =>
    ⟨by rintro ⟨g', hg', h⟩; exact (Units.ext h : g' = g) ▸ hg', fun h => ⟨g, h, rfl⟩⟩
  have hSB : T.indicator (1 : Matrix (Fin a) (Fin a) k → ℂ) ∈ SB (Matrix (Fin a) (Fin a) k) :=
    ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) ⟨hTk.isClosed, hTo⟩).isLocallyConstant,
      HasCompactSupport.intro hTk fun x hx => Set.indicator_of_notMem hx _⟩
  refine ⟨_, hSB, ?_⟩
  have h0 : ∀ m : {m : Fin a → ℤ // Antitone m}, m ≠ ⟨0, antitone_const⟩ →
      shell (haarVol (KO k (Fin a))) ϖ ν z (T.indicator 1) m.1 = 0 := by
    intro m hm
    unfold shell
    refine setIntegral_eq_zero_of_forall_eq_zero fun g hg => ?_
    have hgT : g.val ∉ T := fun h => hm ((exists_unique_shell hϖ g).unique hg
      (show g ∈ shellSet ϖ (0 : Fin a → ℤ) by rw [shellSet_zero]; exact hDK ((hT g).1 h)))
    simp [Set.indicator_of_notMem hgT]
  rw [shellSum, finsum_eq_single _ ⟨0, antitone_const⟩ h0]
  show shell (haarVol (KO k (Fin a))) ϖ ν z (T.indicator 1) (0 : Fin a → ℤ) ≠ 0
  unfold shell
  rw [shellSet_zero]
  have hval : ∫ g in (KO k (Fin a) : Set (GL (Fin a) k)),
      T.indicator 1 g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol (KO k (Fin a))) =
      ∫ g in (KO k (Fin a) : Set (GL (Fin a) k)), (D : Set (GL (Fin a) k)).indicator (fun _ => (1 : ℂ)) g
        ∂(haarVol (KO k (Fin a))) := by
    refine setIntegral_congr_fun isOpen_KO.measurableSet fun g hg => ?_
    by_cases hgD : g ∈ D
    · rw [Set.indicator_of_mem ((hT g).2 hgD), Set.indicator_of_mem hgD,
        apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg), hcond (gdet g) hgD.2]
      simp
    · rw [Set.indicator_of_notMem (fun h => hgD ((hT g).1 h)), Set.indicator_of_notMem hgD]
      simp
  rw [hval]
  have hmD : MeasurableSet (D : Set (GL (Fin a) k)) := hDo.measurableSet
  erw [integral_indicator hmD, Measure.restrict_restrict hmD, setIntegral_const, Set.inter_eq_left.2 hDK]
  have hpos : haarVol (KO k (Fin a)) (D : Set (GL (Fin a) k)) ≠ 0 := (hDo.measure_pos _ ⟨1, one_mem D⟩).ne'
  have hfin : haarVol (KO k (Fin a)) (D : Set (GL (Fin a) k)) ≠ ⊤ := hDk.measure_lt_top.ne
  simp only [Measure.real]
  rw [Complex.real_smul, mul_one, Complex.ofReal_ne_zero]
  exact (ENNReal.toReal_pos hpos hfin).ne'

theorem shellSum_isEqv_and_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ) (n e : ℕ) (ν : kˣ →* ℂˣ) (z : ℂ),
    IsUnif ϖ → IsSmU ν → ¬ IsUnram ν → CondLE ϖ e ν →
    IsEqv ν z (shellSum (haarVol (KO k (Fin n))) ϖ ν z) ∧
    ∃ φ ∈ SB (Matrix (Fin n) (Fin n) k), shellSum (haarVol (KO k (Fin n))) ϖ ν z φ ≠ 0 := by
  intro k _ _ _ _ _ _ ϖ n e ν z hϖ hν hram hcond
  refine ⟨⟨fun φ hφ φ' hφ' => shellSum_add hϖ hram hcond hφ hφ' z, fun c φ _ => ?_,
    fun g₁ g₂ φ hφ => shellSum_eqv hϖ hν hram hcond g₁ g₂ hφ z⟩, exists_ne_zero hϖ hcond z⟩
  exact shellSum_smul _ ϖ ν z c φ

end Main

end GlobalTheory.ShellSumEqv
end
end
