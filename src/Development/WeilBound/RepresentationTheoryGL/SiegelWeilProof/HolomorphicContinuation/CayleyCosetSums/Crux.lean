import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CanonicalPsiNeZeroOfPathBasis
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FdProps
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.InverseFirstBlockMulUnipotentDomain
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecondUnitaryBlockOfPair
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.NormDetFirstBlockCompact

section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CrxMa

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem continuous_matrix_lower_left_block : Continuous (fun M : M2 n => M.toBlocks₂₁) := by
  have : (fun M : M2 n => M.toBlocks₂₁) = fun M => M.submatrix Sum.inr Sum.inl := by funext M; rfl
  rw [this]; exact continuous_id.matrix_submatrix _ _

theorem continuous_matrix_lower_right_block : Continuous (fun M : M2 n => M.toBlocks₂₂) := by
  have : (fun M : M2 n => M.toBlocks₂₂) = fun M => M.submatrix Sum.inr Sum.inr := by funext M; rfl
  rw [this]; exact continuous_id.matrix_submatrix _ _

theorem continuous_cayley_first_block : Continuous (fun M : M2 n => u1 M) := by
  unfold u1
  exact ((continuous_const : Continuous fun _ : M2 n => Complex.I).smul continuous_matrix_lower_left_block).add continuous_matrix_lower_right_block

theorem continuous_cayley_second_block : Continuous (fun M : M2 n => u2 M) := by
  unfold u2
  exact ((continuous_const : Continuous fun _ : M2 n => Complex.I).smul continuous_matrix_lower_left_block).neg.add continuous_matrix_lower_right_block

theorem isOpen_OmZ (hFz : FzHol) (Kg : Type) [TopologicalSpace Kg] [CompactSpace Kg] (ι : Kg → M2 n)
    (hι : Continuous ι) : IsOpen {x : M2 n | ∀ k, ι k * x ∈ DomZ n} :=
  isOpen_setK (hFz n 0 0).1 Kg ι hι

theorem gset_sub_OmZ (hFz : FzHol) {Kg : Type} (ι : Kg → M2 n) (hιG : ∀ k, InG (ι k)) :
    GSet n ⊆ {x : M2 n | ∀ k, ι k * x ∈ DomZ n} :=
  fun _g hg k => (hFz n 0 0).2.1 (inG_mul (hιG k) hg)

theorem continuousOn_vacuum_at_zero (hFz : FzHol) (m : ℕ) : ContinuousOn (fun x : M2 n => fz m 0 0 x) (DomZ n) := by
  intro x hx
  have hA := (hFz n m 0).2.2 ((0 : ℂ), x) ⟨Set.mem_univ _, hx⟩
  have hmk : Continuous fun y : M2 n => ((0 : ℂ), y) := by fun_prop
  exact (hA.continuousAt.comp hmk.continuousAt).continuousWithinAt

theorem continuous_rhoP (hFz : FzHol) (m : ℕ) {Kg : Type} [TopologicalSpace Kg] (ι : Kg → M2 n)
    (hι : Continuous ι) (hιG : ∀ k, InG (ι k)) (Y : Matrix (Fin n) (Fin n) ℂ) : Continuous (rhoP ι m 0 Y) := by
  unfold rhoP
  have hfz : Continuous fun k => fz m 0 0 (ι k) :=
    (continuousOn_vacuum_at_zero hFz m).comp_continuous hι (fun k => (hFz n m 0).2.1 (hιG k))
  have hinv : Continuous fun k => (u2 (ι k))⁻¹ := by
    have e : (fun k => (u2 (ι k))⁻¹) = fun k => (u2 (ι k)).det⁻¹ • (u2 (ι k)).adjugate := by
      funext k; rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [e]
    have hd := (continuous_cayley_second_block.comp hι).matrix_det
    exact (hd.inv₀ (fun k => det_second_cayley_block_ne_zero (hιG k))).smul ((continuous_cayley_second_block.comp hι).matrix_adjugate)
  exact (hfz.mul (((hinv.matrix_mul continuous_const).matrix_mul (continuous_cayley_first_block.comp hι)).matrix_trace)).star

theorem contDiffOn_PhiZ (hFd : FdProps) (hFz : FzHol) (m : ℕ) (Kg : Type) [TopologicalSpace Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [IsFiniteMeasure μ] (ι : Kg → M2 n) (hι : Continuous ι)
    (c : Kg → ℂ) (hc : Continuous c) :
    ContDiffOn ℂ ∞ (fun x => ∫ k, Fd m (ι k * x) * c k ∂μ) {x : M2 n | ∀ k, ι k * x ∈ DomZ n} := by
  have hF : ContDiffOn ℂ ∞ (Fd (n := n) m) (DomZ n) := (hFd n m).1.of_le le_top
  exact (PositivityTheory.Rg.Sw.LVs.holInt n Kg μ _ (fun k x => Fd m (ι k * x) * c k) (isOpen_OmZ hFz Kg ι hι)
    (fun N => continuousOn_iteratedFDeriv_translate (Fd m) (DomZ n) (hFz n 0 0).1 hF Kg ι hι c hc N)
    (fun k => (hF.comp (contDiff_mulLeft (ι k)).contDiffOn
      (fun x (hx : x ∈ {x : M2 n | ∀ k, ι k * x ∈ DomZ n}) => hx k)).mul contDiffOn_const)).1

theorem fubini_gen (F : M2 n → ℂ) (U : Set (M2 n)) (hF : ContinuousOn F U) (hGU : GSet n ⊆ U)
    (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
    (hιG : ∀ k, InG (ι k)) (ρ : Kg → ℂ) (hρ : Continuous ρ) (a b : M2 n) (ha : InG a) (hb : InG b)
    (ψ : (Fin n → Fin n → ℝ) → ℂ) (hψ : IsSingTest ψ) :
    ∫ t, (∫ k, F (ι k * (a * nU (herm t) * b)) * ρ k ∂μ) * ψ t =
      ∫ k, ρ k * (∫ t, F (1 * ι k * a * nU (herm t) * b) * ψ t) ∂μ := by
  have hherm : Continuous (herm (n := n)) := by
    unfold herm; fun_prop
  have hnU : Continuous fun x : Fin n → Fin n → ℝ => nU (herm x) := by
    unfold nU; exact Continuous.matrix_fromBlocks continuous_const hherm continuous_const continuous_const
  have hmap : Continuous fun z : Kg × (Fin n → Fin n → ℝ) => ι z.1 * a * nU (herm z.2) * b :=
    (((hι.comp continuous_fst).mul continuous_const).mul (hnU.comp continuous_snd)).mul continuous_const
  set Fp : Kg × (Fin n → Fin n → ℝ) → ℂ := fun z => F (ι z.1 * a * nU (herm z.2) * b) * ψ z.2 * ρ z.1 with hFpdef
  have hFc : Continuous Fp :=
    ((hF.comp_continuous hmap (fun z => hGU (inG_mul (inG_mul (inG_mul (hιG z.1) ha) (inG_nU_herm z.2)) hb))).mul
      (hψ.1.comp continuous_snd)).mul (hρ.comp continuous_fst)
  have hFs : HasCompactSupport Fp := by
    refine IsCompact.of_isClosed_subset (isCompact_univ.prod hψ.2.1) (isClosed_tsupport Fp) ?_
    refine closure_minimal (fun z hz => ⟨Set.mem_univ _, subset_tsupport ψ ?_⟩)
      (isClosed_univ.prod (isClosed_tsupport ψ))
    intro h0; apply hz; simp [hFpdef, h0]
  have hFi : Integrable Fp (μ.prod volume) := hFc.integrable_of_hasCompactSupport hFs
  have e1 : ∀ k, ρ k * (∫ t, F (1 * ι k * a * nU (herm t) * b) * ψ t) = ∫ t, Fp (k, t) := by
    intro k; rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hFpdef, Matrix.one_mul]; ring
  have e2 : ∀ t, (∫ k, F (ι k * (a * nU (herm t) * b)) * ρ k ∂μ) * ψ t = ∫ k, Fp (k, t) ∂μ := by
    intro t; rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [hFpdef, Matrix.mul_assoc]; ring
  simp_rw [e1, e2]
  exact (integral_integral_swap (f := fun k x => Fp (k, x)) hFi).symm

theorem stepA_Z (hFd : FdProps) (hFz : FzHol) (m : ℕ) (Kg : Type) [Group Kg] [TopologicalSpace Kg]
    [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg)
    [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι) (hK : ∀ g, InK g ↔ ∃ k, ι k = g)
    (hneg : ∀ (P : Matrix (Fin n) (Fin n) ℂ) (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b x : M2 n), IsSingTest ψ → InG a →
      InG b → InG x → deriv (fun z => tOp μ ι (rhoP ι m 0 P) ψ a b (fz m 0 z) x) 0 = 0)
    (Y : Matrix (Fin n) (Fin n) ℂ) (a b : M2 n) (ha : InG a) (hb : InG b) :
    detD (fun H => ∫ k, Fd m (ι k * (a * nU H * b)) * rhoP ι m 0 Y k ∂μ) = 0 := by
  have hιG : ∀ k, InG (ι k) := fun k => ((hK (ι k)).2 ⟨k, rfl⟩).1
  have hΩo := isOpen_OmZ hFz Kg ι hι
  have hGΩ := gset_sub_OmZ hFz ι hιG
  have hρ := continuous_rhoP hFz m ι hι hιG Y
  have hΦ := contDiffOn_PhiZ hFd hFz m Kg μ ι hι _ hρ
  have hpre : IsOpen {H : Matrix (Fin n) (Fin n) ℂ | a * nU H * b ∈ {x : M2 n | ∀ k, ι k * x ∈ DomZ n}} :=
    hΩo.preimage (contDiff_nU_sandwich a b).continuous
  have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ∈
      {H : Matrix (Fin n) (Fin n) ℂ | a * nU H * b ∈ {x : M2 n | ∀ k, ι k * x ∈ DomZ n}} := by
    show a * nU 0 * b ∈ {x : M2 n | ∀ k, ι k * x ∈ DomZ n}
    have : nU (0 : Matrix (Fin n) (Fin n) ℂ) = 1 := by simp [nU, Matrix.fromBlocks_one]
    rw [this, mul_one]; exact hGΩ (inG_mul ha hb)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hpre 0 h0
  refine singToDiff n (fun H => ∫ k, Fd m (ι k * (a * nU H * b)) * rhoP ι m 0 Y k ∂μ) r hr
    (hΦ.comp (contDiff_nU_sandwich a b).contDiffOn (fun H hH => hball hH)) ?_
  intro ψ hψ
  have h1 := hneg Y ψ a b 1 hψ ha hb inG_one
  rw [(hFd n m).2 Kg μ ι hι hK (rhoP ι m 0 Y) ψ a b 1 hρ hψ.1 hψ.2.1 ha hb inG_one] at h1
  rw [← h1]
  have hFc : ContinuousOn (Fd (n := n) m) (DomZ n) := (hFd n m).1.continuousOn
  exact fubini_gen (Fd m) (DomZ n) hFc (hFz n 0 0).2.1 Kg μ ι hι hιG _ hρ a b ha hb ψ hψ

end PositivityTheory.Rg.Sw.HSt.CrxMa
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.Cx3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem stepD (j : ℕ) (p q : ℤ) {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [IsFiniteMeasure μ] [IsFiniteMeasureOnCompacts μ]
    (ι : Kg → M2 n) (hι : Continuous ι) (hιG : ∀ k, InG (ι k)) (ρ : Kg → ℂ) (hρ : Continuous ρ)
    (hC : ∀ g, InG g → ∫ k, hF j p q (ι k * g) * ρ k ∂μ = 0) :
    ∀ (N : ℕ) (W : Fin N → M2 n) (g : M2 n), InG g →
      ∫ k, iteratedFDeriv ℂ N (hF j p q) (ι k * g) (fun i => ι k * g * W i) * ρ k ∂μ = 0 := by
  intro N W g hg
  set Ω : Set (M2 n) := {x | ∀ k, ι k * x ∈ Dom n} with hΩ
  have hΩo : IsOpen Ω := isOpen_domK Kg ι hι
  have hGΩ : GSet n ⊆ Ω := fun x hx k => gset_sub_dom (inG_mul (hιG k) hx)
  have hF0 : ContDiffOn ℂ ∞ (hF (n := n) j p q) (Dom n) := contDiffOn_hF j p q
  have hsm : ∀ k, ContDiffOn ℂ ∞ (fun x => hF j p q (ι k * x) * ρ k) Ω := fun k =>
    (hF0.comp (contDiff_mulLeft (ι k)).contDiffOn (fun x (hx : x ∈ Ω) => hx k)).mul contDiffOn_const
  have hH := holInt n Kg μ Ω (fun k x => hF j p q (ι k * x) * ρ k) hΩo
    (fun N => continuousOn_iteratedFDeriv_translate (hF j p q) (Dom n) isOpen_dom hF0 Kg ι hι ρ hρ N) hsm
  have hz := holZero n Ω (fun x => ∫ k, hF j p q (ι k * x) * ρ k ∂μ) hΩo hGΩ hH.1
    (fun g hg => hC g hg) N g hg
  have key := hH.2 N g (fun i => g * W i) (hGΩ hg)
  rw [hz] at key
  simp only [_root_.zero_apply] at key
  rw [key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  have hk : ι k * g ∈ Dom n := hGΩ hg k
  show iteratedFDeriv ℂ N (hF j p q) (ι k * g) (fun i => ι k * g * W i) * ρ k =
    iteratedFDeriv ℂ N (fun x => hF j p q (ι k * x) * ρ k) g (fun i => g * W i)
  rw [iteratedFDeriv_mul_const_of (fun x => hF j p q (ι k * x)) Ω hΩo
    (hF0.comp (contDiff_mulLeft (ι k)).contDiffOn (fun x (hx : x ∈ Ω) => hx k)) (ρ k) g (hGΩ hg) N,
    iteratedFDeriv_left_mul (hF j p q) (Dom n) isOpen_dom hF0 (ι k) g hk N]
  simp only [mul_assoc]

theorem stepC (hFd : FdProps) (hDj : DjFd) (hSph : SphU) (hFz : FzHol) (m j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n)
    (ha1 : deriv (fun z : ℂ => (∏ i ∈ Finset.range j, ((i : ℂ) - z)) *
      (∏ i ∈ Finset.range (n - j), ((i : ℂ) - m - z))) 0 ≠ 0)
    {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [IsFiniteMeasure μ] [IsFiniteMeasureOnCompacts μ]
    (ι : Kg → M2 n) (hι : Continuous ι) (hιG : ∀ k, InG (ι k)) (ρ : Kg → ℂ) (hρ : Continuous ρ)
    (hB : ∀ g, InG g → detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
      ∫ k, Fd m (ι k * (g * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)) * ρ k ∂μ)) = 0) :
    ∀ g, InG g → ∫ k, hF j (m : ℤ) 0 (ι k * g) * ρ k ∂μ = 0 := by
  intro g hg
  have hGZ : GSet n ⊆ DomZ n := (hFz n m 0).2.1
  have hkg : ∀ k, ι k * g ∈ DomZ n := fun k => hGZ (inG_mul (hιG k) hg)
  have hFdc : ContDiffOn ℂ ⊤ (Fd (n := n) m) (DomZ n) := (hFd n m).1
  have hS := hSph n (Fd m) (DomZ n) (hFz n m 0).1 hFdc μ ι hι ρ hρ (LQ (blkA j)) (LR (blkB j))
    (fun M x T => by rw [LQ_apply, LQ_apply, mul_assoc]) (fun M x S => by rw [LR_apply, LR_apply, mul_assoc]) g hkg
  have e1 : (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
      ∫ k, Fd m (ι k * (g * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)) * ρ k ∂μ)) =
      fun T => detD (fun S => ∫ k, Fd m (ι k * (g + LQ (blkA j) g T + LR (blkB j) g S)) * ρ k ∂μ) := by
    funext T; congr 1; funext S
    rw [mul_mX, LQ_apply, LR_apply]
  have e2 : ∀ k, detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
      Fd m (ι k * g + LQ (blkA j) (ι k * g) T + LR (blkB j) (ι k * g) S))) * ρ k =
      deriv (fun z : ℂ => (∏ i ∈ Finset.range j, ((i : ℂ) - z)) *
        (∏ i ∈ Finset.range (n - j), ((i : ℂ) - m - z))) 0 * (hF j (m : ℤ) 0 (ι k * g) * ρ k) := by
    intro k
    have r : (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
        Fd m (ι k * g + LQ (blkA j) (ι k * g) T + LR (blkB j) (ι k * g) S))) =
        fun T => detD (fun S => Fd m ((ι k * g) * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)) := by
      funext T; congr 1; funext S
      rw [mul_mX, LQ_apply, LR_apply]
    rw [r, hDj n m j (ι k * g) hj1 hjn (hkg k)]
    ring
  have h := hB g hg
  rw [e1, hS, integral_congr_ae (Filter.Eventually.of_forall e2), integral_const_mul] at h
  exact (mul_eq_zero.1 h).resolve_left ha1

end PositivityTheory.Rg.Sw.HSt.Cx3
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem vacuum_nonvanishing_of_facts (hFd : FdProps) (hDj : DjFd) (hKS : KSplit) (hSph : SphU) (hFz : FzHol) : Crux0 := by
  intro n m hmn Kg _ _ _ _ _ _ μ _ ι hι hK
  by_contra hneg
  push Not at hneg
  set j : ℕ := n - m with hjdef
  have hjn : j ≤ n := Nat.sub_le n m
  have hj1 : 1 ≤ j := by omega
  have hιG : ∀ k, InG (ι k) := fun k => ((hK (ι k)).2 ⟨k, rfl⟩).1
  have hιK : ∀ k, InK (ι k) := fun k => (hK (ι k)).2 ⟨k, rfl⟩

  set ΩZ : Set (M2 n) := {x | ∀ k, ι k * x ∈ DomZ n} with hΩZdef
  have hΩZo : IsOpen ΩZ := isOpen_setK (hFz n m 0).1 Kg ι hι
  have hGΩZ : GSet n ⊆ ΩZ := fun g hg k => (hFz n m 0).2.1 (inG_mul (hιG k) hg)
  have hDZ : ∀ y ∈ DomZ n, y ∈ Dom n := fun y hy => hy.1
  have hFdCD : ContDiffOn ℂ ∞ (Fd (n := n) m) (DomZ n) := ((hFd n m).1).of_le le_top

  set ρ : Matrix (Fin n) (Fin n) ℂ → Kg → ℂ := fun Y => rhoP ι m 0 Y with hρdef
  have hρc : ∀ Y, Continuous (ρ Y) := fun Y => CrxMa.continuous_rhoP hFz m ι hι hιG Y
  set Φ : Matrix (Fin n) (Fin n) ℂ → M2 n → ℂ := fun Y x => ∫ k, Fd m (ι k * x) * ρ Y k ∂μ with hΦdef
  have hΦ : ∀ Y, ContDiffOn ℂ ∞ (Φ Y) ΩZ := fun Y =>
    (holInt n Kg μ ΩZ (fun k x => Fd m (ι k * x) * ρ Y k) hΩZo
      (fun N => (continuousOn_iteratedFDeriv_translate (Fd m) (DomZ n) (hFz n m 0).1 hFdCD Kg ι hι _ (hρc Y) N).mono
        (Set.prod_mono subset_rfl (fun x hx => hx)))
      (fun k => (hFdCD.comp (contDiff_mulLeft (ι k)).contDiffOn (fun x (hx : x ∈ ΩZ) => hx k)).mul contDiffOn_const)).1

  have stepA : ∀ Y a b, InG a → InG b → detD (fun H => Φ Y (a * nU H * b)) = 0 :=
    fun Y a b ha hb => CrxMa.stepA_Z hFd hFz m Kg μ ι hι hK hneg Y a b ha hb

  have stepB : ∀ Y g, InG g → detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
      Φ Y (g * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1))) = 0 := by
    intro Y
    refine topComp n j (Φ Y) ΩZ hΩZo hGΩZ (hΦ Y) ?_ (stepA Y)
    intro x P' S' hxM hx hP hS
    simp only [hΦdef]
    congr 1; funext k
    rw [← mul_assoc, Fd_kpart m j (ι k * x) (hDZ _ (hx k)) P' S' hP hS]

  set a1 : ℂ := deriv (fun z : ℂ => (∏ i ∈ Finset.range j, ((i : ℂ) - z)) * (∏ i ∈ Finset.range (n - j), ((i : ℂ) - m - z))) 0
  have ha1 : a1 ≠ 0 := deriv_prod_range_sub_mul_prod_ne_zero n m hmn
  set Ψ : Matrix (Fin n) (Fin n) ℂ → M2 n → ℂ := fun Y x => ∫ k, hF j m 0 (ι k * x) * ρ Y k ∂μ with hΨdef
  have stepC : ∀ Y g, InG g → Ψ Y g = 0 := fun Y g hg =>
    Cx3.stepC hFd hDj hSph hFz m j hj1 hjn ha1 μ ι hι hιG (ρ Y) (hρc Y) (fun g hg => stepB Y g hg) g hg

  have stepD : ∀ Y (N : ℕ) (W : Fin N → M2 n) (g : M2 n), InG g →
      ∫ k, iteratedFDeriv ℂ N (hF j m 0) (ι k * g) (fun i => ι k * g * W i) * ρ Y k ∂μ = 0 := fun Y N W g hg =>
    Cx3.stepD j (m : ℤ) 0 μ ι hι hιG (ρ Y) (hρc Y) (fun g hg => stepC Y g hg) N W g hg

  have stepE : ∀ (N : ℕ) (v : Fin (N + 1) → M2 n) (a0 b0 : Fin n), v 0 = WD 0 (Matrix.single a0 b0 1) →
      (∀ a b, v a * v b = 0) →
      ∫ k, iteratedFDeriv ℂ (N + 1) (hF j (m : ℤ) 0) (ι k) (fun i => ι k * v i) * fV (m : ℤ) 0 (ι k) ∂μ = 0 := by
    intro N v a0 b0 hv0 hv
    have hdom : ∀ k, ι k ∈ Dom n := fun k => gset_sub_dom (hιG k)
    set F1 : M2 n → ℂ := rit (hF j (m : ℤ) 0) N (fun i => v i.succ) with hF1def
    have hF1 : ContDiffOn ℂ ∞ F1 (Dom n) := rit_contDiffOn _ _ isOpen_dom (contDiffOn_hF j (m : ℤ) 0) N _
    have hF1law : ∀ P x, InP P → x ∈ Dom n → F1 (P * x) = c1 (m : ℤ) 0 P * F1 x :=
      rit_law _ (Dom n) isOpen_dom (contDiffOn_hF j (m : ℤ) 0) (c1 (m : ℤ) 0) (fun P x hP hx => mul_mem_dom hP hx)
        (fun P x hP hx => hF_law j (m : ℤ) 0 hP hx) N _
    have e1 : ∀ k, iteratedFDeriv ℂ (N + 1) (hF j (m : ℤ) 0) (ι k) (fun i => ι k * v i) =
        rit F1 1 (fun _ => v 0) (ι k) := by
      intro k
      rw [← rit_eq (hF j (m : ℤ) 0) (Dom n) isOpen_dom (contDiffOn_hF j (m : ℤ) 0) (N + 1) v hv (ι k) (hdom k)]
      rfl
    have hT := rit_transpose infInv F1 (c1 (m : ℤ) 0) (c2 (m : ℤ) 0) hF1 hF1law (fun P hP => modulus_characters_product (m : ℤ) 0 hP)
      Kg μ ι hι hK 1 (fV (m : ℤ) 0) (contDiffOn_fV (m : ℤ) 0) (fun P x hP hx => fV_law (m : ℤ) 0 hP hx)
      (fun _ => v 0) (fun a b => hv 0 0)
    simp_rw [e1]
    rw [hT]
    have e2 : ∀ k, rit (fV (m : ℤ) 0) 1 (fun i => (fun _ : Fin 1 => v 0) (Fin.rev i)) (ι k) =
        ((m : ℂ) - n) * (fV (m : ℤ) 0 (ι k) * ((u1 (ι k))⁻¹ * u2 (ι k)) b0 a0) := by
      intro k
      show fderiv ℂ (fV (m : ℤ) 0) (ι k) (ι k * v 0) = _
      rw [hv0, fderiv_fV_R m (ι k) (hdom k) a0 b0]; ring
    obtain ⟨L, c, kl, hKl⟩ := hKS n m a0 b0 Kg ι hK
    have := GlobalTheory.isMulRightInvariant_of_compactSpace μ
    have hF1c : Continuous fun k => F1 (ι k) := cont_on_K F1 hF1 Kg ι hι hdom
    have e3 : ∀ l, ∫ k, F1 (ι k) * rhoP ι m 0 1 (k * kl l) ∂μ = 0 := by
      intro l
      have h := integral_mul_right_eq_self (μ := μ) (fun k => F1 (ι (k * (kl l)⁻¹)) * rhoP ι m 0 1 k) (kl l)
      simp only [mul_inv_cancel_right] at h
      rw [h]
      have hg : InG (ι (kl l)⁻¹) := hιG _
      have := stepD 1 N (fun i => v i.succ) (ι (kl l)⁻¹) hg
      rw [← this]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [map_mul]
      rw [hF1def, rit_eq (hF j (m : ℤ) 0) (Dom n) isOpen_dom (contDiffOn_hF j (m : ℤ) 0) N _ (fun a b => hv _ _)
        _ (gset_sub_dom (inG_mul (hιG k) hg))]
    have e4 : ∀ k, F1 (ι k) * rit (fV (m : ℤ) 0) 1 (fun i => (fun _ : Fin 1 => v 0) (Fin.rev i)) (ι k) =
        ((m : ℂ) - n) * ∑ l, c l * (F1 (ι k) * rhoP ι m 0 1 (k * kl l)) := by
      intro k; rw [e2, hKl k, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => by ring
    simp_rw [e4]
    rw [integral_const_mul, integral_finsetSum]
    · simp_rw [integral_const_mul, e3, mul_zero, Finset.sum_const_zero]; simp
    · intro l _
      exact Integrable.const_mul (integrable_of_continuous_K μ (hF1c.mul ((hρc 1).comp (continuous_id.mul continuous_const)))) _

  have stepE' : ∀ (K : ℕ) (v : Fin K → M2 n) (i0 : Fin K) (a0 b0 : Fin n), v i0 = WD 0 (Matrix.single a0 b0 1) →
      (∀ a b, v a * v b = 0) →
      ∫ k, iteratedFDeriv ℂ K (hF j (m : ℤ) 0) (ι k) (fun i => ι k * v i) * fV (m : ℤ) 0 (ι k) ∂μ = 0 := by
    intro K v i0 a0 b0 hvi hv
    obtain ⟨N, rfl⟩ : ∃ N, K = N + 1 := ⟨K - 1, by have := i0.2; omega⟩
    set σ : Equiv.Perm (Fin (N + 1)) := Equiv.swap 0 i0 with hσ
    have hsym : ∀ k, iteratedFDeriv ℂ (N + 1) (hF j (m : ℤ) 0) (ι k) (fun i => ι k * v i) =
        iteratedFDeriv ℂ (N + 1) (hF j (m : ℤ) 0) (ι k) (fun i => ι k * (v ∘ σ) i) := by
      intro k
      have := TC.iterSymm (M2 n) (hF j (m : ℤ) 0) (Dom n) isOpen_dom (contDiffOn_hF j (m : ℤ) 0) (ι k)
        (gset_sub_dom (hιG k)) (N + 1) (fun i => ι k * v i) σ
      rw [← this]; rfl
    simp_rw [hsym]
    refine stepE N (v ∘ σ) a0 b0 ?_ (fun a b => hv _ _)
    simp [hσ, hvi]
  have hLRLQ : ∀ (T : Matrix (blkA (n := n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ)
      (T' : Matrix (blkA (n := n) j) (blkA j) ℂ) (S' : Matrix (blkB (n := n) j) (blkB j) ℂ),
      (LR (blkA j) 1 T + LQ (blkB j) 1 S) * (LR (blkA j) 1 T' + LQ (blkB j) 1 S') = 0 := by
    intro T S T' S'
    rw [LR_apply, LQ_apply, LR_apply, LQ_apply, one_mul, one_mul, one_mul, one_mul, add_comm (WD 0 _), ← WD_add,
      add_zero, zero_add, add_comm (WD 0 _), ← WD_add, add_zero, zero_add]
    exact WD_mul_WD_B_A j T S T' S'
  have hDc : ∀ (K : ℕ) (v : Fin K → M2 n), (∀ a b, v a * v b = 0) →
      Continuous (fun k => iteratedFDeriv ℂ K (hF j (m : ℤ) 0) (ι k) (fun i => ι k * v i)) := by
    intro K v hv
    have e : (fun k => iteratedFDeriv ℂ K (hF j (m : ℤ) 0) (ι k) (fun i => ι k * v i)) =
        fun k => rit (hF j (m : ℤ) 0) K v (ι k) := by
      funext k
      rw [rit_eq (hF j (m : ℤ) 0) (Dom n) isOpen_dom (contDiffOn_hF j (m : ℤ) 0) K v hv (ι k) (gset_sub_dom (hιG k))]
    rw [e]
    exact cont_on_K _ (rit_contDiffOn _ _ isOpen_dom (contDiffOn_hF j (m : ℤ) 0) K v) Kg ι hι
      (fun k => gset_sub_dom (hιG k))
  have hfVc : Continuous (fun k => fV (m : ℤ) 0 (ι k)) :=
    cont_on_K _ (contDiffOn_fV (m : ℤ) 0) Kg ι hι (fun k => gset_sub_dom (hιG k))
  have stepF : ∫ k, detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
      hF j (m : ℤ) 0 (ι k + ι k * LR (blkA j) 1 T + ι k * LQ (blkB j) 1 S))) * fV (m : ℤ) 0 (ι k) ∂μ = 0 := by
    have hcA : Fintype.card (blkA (n := n) j) = j := card_blkA hjn
    have e : ∀ k, detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
        hF j (m : ℤ) 0 (ι k + ι k * LR (blkA j) 1 T + ι k * LQ (blkB j) 1 S))) =
        ∑ σ : Equiv.Perm (blkA (n := n) j), ∑ τ : Equiv.Perm (blkB (n := n) j),
          (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
          iteratedFDeriv ℂ (Fintype.card (blkA (n := n) j) + Fintype.card (blkB (n := n) j)) (hF j (m : ℤ) 0) (ι k)
            (fun i => ι k * Fin.append
              (fun i => LR (blkA j) 1 (Matrix.single ((Fintype.equivFin (blkA (n := n) j)).symm i)
                (σ ((Fintype.equivFin (blkA (n := n) j)).symm i)) 1))
              (fun i => LQ (blkB j) 1 (Matrix.single ((Fintype.equivFin (blkB (n := n) j)).symm i)
                (τ ((Fintype.equivFin (blkB (n := n) j)).symm i)) 1)) i) := by
      intro k
      have := detD_detD_comp (hF j (m : ℤ) 0) (Dom n) isOpen_dom (contDiffOn_hF j (m : ℤ) 0) (ι k)
        (gset_sub_dom (hιG k)) ((mulL (ι k)).comp (LR (blkA j) 1)) ((mulL (ι k)).comp (LQ (blkB j) 1))
      simp only [ContinuousLinearMap.comp_apply, mulL_apply] at this
      rw [this]
      refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
      rw [fin_append_mul]
    simp_rw [e, Finset.sum_mul]
    rw [integral_finsetSum]
    · refine Finset.sum_eq_zero fun σ _ => ?_
      rw [integral_finsetSum]
      · refine Finset.sum_eq_zero fun τ _ => ?_
        simp_rw [mul_assoc]
        rw [integral_const_mul, integral_const_mul]
        refine mul_eq_zero_of_right _ (mul_eq_zero_of_right _ ?_)
        have h0 : 0 < Fintype.card (blkA (n := n) j) := by omega
        refine stepE' _ _ (Fin.castAdd _ ⟨0, h0⟩) ((Fintype.equivFin (blkA (n := n) j)).symm ⟨0, h0⟩ : Fin n)
          (σ ((Fintype.equivFin (blkA (n := n) j)).symm ⟨0, h0⟩) : Fin n) ?_ ?_
        · rw [Fin.append_left, LR_apply, one_mul, embOn_single_pf]
        · intro a b
          refine Fin.addCases (fun a => ?_) (fun a => ?_) a <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) b <;>
            simp only [Fin.append_left, Fin.append_right]
          · simpa using hLRLQ _ 0 _ 0
          · simpa using hLRLQ _ 0 0 _
          · simpa using hLRLQ 0 _ _ 0
          · simpa using hLRLQ 0 _ 0 _
      · intro τ _
        refine integrable_of_continuous_K μ (((continuous_const.mul (hDc _ _ ?_)).mul hfVc))
        intro a b
        refine Fin.addCases (fun a => ?_) (fun a => ?_) a <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) b <;>
          simp only [Fin.append_left, Fin.append_right]
        · simpa using hLRLQ _ 0 _ 0
        · simpa using hLRLQ _ 0 0 _
        · simpa using hLRLQ 0 _ _ 0
        · simpa using hLRLQ 0 _ 0 _
    · intro σ _
      refine integrable_finsetSum _ fun τ _ => ?_
      refine integrable_of_continuous_K μ (((continuous_const.mul (hDc _ _ ?_)).mul hfVc))
      intro a b
      refine Fin.addCases (fun a => ?_) (fun a => ?_) a <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) b <;>
        simp only [Fin.append_left, Fin.append_right]
      · simpa using hLRLQ _ 0 _ 0
      · simpa using hLRLQ _ 0 0 _
      · simpa using hLRLQ 0 _ _ 0
      · simpa using hLRLQ 0 _ 0 _

  have hWz : ∀ (T T' : Matrix (blkA (n := n) j) (blkA j) ℂ) (S S' : Matrix (blkB (n := n) j) (blkB j) ℂ),
      (LR (blkA j) 1 T + LQ (blkB j) 1 S) * (LR (blkA j) 1 T' + LQ (blkB j) 1 S') = 0 := by
    intro T T' S S'
    have e : ∀ (T : Matrix (blkA (n := n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ),
        LR (blkA j) 1 T + LQ (blkB j) 1 S = WD (embOn (blkB j) S) (embOn (blkA j) T) := by
      intro T S
      rw [LR_apply, LQ_apply, one_mul, one_mul, add_comm, ← WD_add, add_zero, zero_add]
    rw [e, e]; exact WD_mul_WD_B_A j T S T' S'
  have weight_sum_eq := transpose_detD infInv (hF j (m : ℤ) 0) (fV (m : ℤ) 0) (c1 (m : ℤ) 0) (c2 (m : ℤ) 0)
    (contDiffOn_hF j (m : ℤ) 0) (contDiffOn_fV (m : ℤ) 0)
    (fun P' x hP hx => hF_law j (m : ℤ) 0 hP hx) (fun P' x hP hx => fV_law (m : ℤ) 0 hP hx)
    (fun P' hP => modulus_characters_product (m : ℤ) 0 hP) Kg μ ι hι hK (LR (blkA j) 1) (LQ (blkB j) 1) hWz
  rw [stepF] at weight_sum_eq
  have stepE3 : ∫ k, hF j (m : ℤ) 0 (ι k) * detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ =>
      detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
        fV (m : ℤ) 0 (ι k + ι k * LR (blkA j) 1 T + ι k * LQ (blkB j) 1 S))) ∂μ = 0 := by
    have hs : ((-1 : ℂ) ^ (Fintype.card (blkA (n := n) j) + Fintype.card (blkB (n := n) j))) ≠ 0 :=
      pow_ne_zero _ (by norm_num)
    exact (mul_eq_zero.1 weight_sum_eq.symm).resolve_left hs
  have hcst' : (∏ i ∈ Finset.range j, (((m : ℤ) : ℂ) - n + i)) * (∏ i ∈ Finset.range (n - j), (((0 : ℤ) : ℂ) - n + i)) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · rw [Finset.prod_ne_zero_iff]
      intro i hi
      rw [Finset.mem_range] at hi
      have : ((m : ℤ) : ℂ) - n + i = (((m : ℤ) - n + i : ℤ) : ℂ) := by push_cast; ring
      rw [this]; exact_mod_cast (by omega : (m : ℤ) - n + i ≠ 0)
    · rw [Finset.prod_ne_zero_iff]
      intro i hi
      rw [Finset.mem_range] at hi
      have : ((0 : ℤ) : ℂ) - n + i = (((0 : ℤ) - n + i : ℤ) : ℂ) := by push_cast; ring
      rw [this]; exact_mod_cast (by omega : (0 : ℤ) - n + i ≠ 0)
  have stepG : ∫ k, (((‖minorOn (blkA j) (wM (ι k))‖ ^ 2 * ‖minorOn (blkB j) (wM (ι k))‖ ^ 2 : ℝ)) : ℂ) ∂μ = 0 := by
    have e : ∀ k, hF j (m : ℤ) 0 (ι k) * detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ =>
        detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
          fV (m : ℤ) 0 (ι k + ι k * LR (blkA j) 1 T + ι k * LQ (blkB j) 1 S))) =
        ((∏ i ∈ Finset.range j, (((m : ℤ) : ℂ) - n + i)) * (∏ i ∈ Finset.range (n - j), (((0 : ℤ) : ℂ) - n + i))) *
          (((‖minorOn (blkA j) (wM (ι k))‖ ^ 2 * ‖minorOn (blkB j) (wM (ι k))‖ ^ 2 : ℝ)) : ℂ) := by
      intro k
      have r : (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
          fV (m : ℤ) 0 (ι k + ι k * LR (blkA j) 1 T + ι k * LQ (blkB j) 1 S))) =
          (fun T => detD (fun S => fV (m : ℤ) 0 (ι k * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1))) := by
        funext T; congr 1; funext S
        rw [mul_mX, LR_apply, LQ_apply, one_mul, one_mul, add_assoc, add_assoc, add_comm (ι k * WD 0 _)]
      rw [r, dpDual cayley uAct n j (m : ℤ) 0 (ι k) hjn (hιG k)]
      have hu := wM_mem_unitary (hιK k)
      rw [minorOn_inv_of_unitary hu, hF, minorOn_inv_of_unitary hu]
      have h1 := scalar_section_mul_conjugate_section (hιK k) (m : ℤ) 0
      have ha : minorOn (blkA j) (wM (ι k)) * star (minorOn (blkA j) (wM (ι k))) =
          ((‖minorOn (blkA j) (wM (ι k))‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have hb : minorOn (blkB j) (wM (ι k)) * star (minorOn (blkB j) (wM (ι k))) =
          ((‖minorOn (blkB j) (wM (ι k))‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast at ha hb
      rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_pow]
      linear_combination (((∏ i ∈ Finset.range j, (((m : ℤ) : ℂ) - n + i)) * (∏ i ∈ Finset.range (n - j), (((0 : ℤ) : ℂ) - n + i))) *
        minorOn (blkA j) (wM (ι k)) * star (minorOn (blkA j) (wM (ι k))) * minorOn (blkB j) (wM (ι k)) *
        star (minorOn (blkB j) (wM (ι k)))) * h1 + 0 * ha + 0 * hb +
        (((∏ i ∈ Finset.range j, (((m : ℤ) : ℂ) - n + i)) * (∏ i ∈ Finset.range (n - j), (((0 : ℤ) : ℂ) - n + i))) *
          (minorOn (blkB j) (wM (ι k)) * star (minorOn (blkB j) (wM (ι k))))) * ha +
        (((∏ i ∈ Finset.range j, (((m : ℤ) : ℂ) - n + i)) * (∏ i ∈ Finset.range (n - j), (((0 : ℤ) : ℂ) - n + i))) *
          (‖minorOn (blkA j) (wM (ι k))‖ ^ 2 : ℂ)) * hb
    simp_rw [e, integral_const_mul] at stepE3
    exact (mul_eq_zero.1 stepE3).resolve_left hcst'
  have hpos := pos_int j Kg μ ι hι hK
  rw [integral_complex_ofReal] at stepG
  exact hpos.ne' (by exact_mod_cast stepG)

end PositivityTheory.Rg.Sw.HSt
end
end

section
noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem det_nU (H : Matrix (Fin n) (Fin n) ℂ) : (nU H).det = 1 := by
  simp [nU, Matrix.det_fromBlocks_zero₂₁]

theorem fz_twist (m : ℕ) (e : ℤ) (z : ℂ) (y : M2 n) : fz m e z y = y.det ^ e * fz m 0 z y := by
  simp [fz, mul_assoc]

theorem det_unit_of_inK {k : M2 n} (hk : InK k) : star k.det * k.det = 1 := by
  have h := congrArg Matrix.det hk.2
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
  exact h

theorem rhoP_twist {Kg : Type} (ι : Kg → M2 n) (hK : ∀ k, InK (ι k)) (m : ℕ) (e : ℤ) (Y : Matrix (Fin n) (Fin n) ℂ)
    (k : Kg) : rhoP ι m e Y k * (ι k).det ^ e = rhoP ι m 0 Y k := by
  unfold rhoP
  rw [fz_twist m e 0 (ι k)]
  simp only [star_mul, star_zpow₀]
  have hu : star (ι k).det * (ι k).det = 1 := det_unit_of_inK (hK k)
  have h1 : star (ι k).det ^ e * (ι k).det ^ e = 1 := by
    rw [← mul_zpow, hu, _root_.one_zpow]
  linear_combination (star ((u2 (ι k))⁻¹ * Y * u1 (ι k)).trace * star (fz m 0 0 (ι k))) * h1

theorem tOp_twist {Kg : Type} [MeasurableSpace Kg] (μ : Measure Kg) (ι : Kg → M2 n) (hK : ∀ k, InK (ι k)) (m : ℕ)
    (e : ℤ) (Y : Matrix (Fin n) (Fin n) ℂ) (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b x : M2 n) (z : ℂ) :
    tOp μ ι (rhoP ι m e Y) ψ a b (fz m e z) x =
      (x.det ^ e * a.det ^ e * b.det ^ e) * tOp μ ι (rhoP ι m 0 Y) ψ a b (fz m 0 z) x := by
  unfold tOp
  rw [← integral_const_mul]
  congr 1
  funext k
  have hin : (∫ (t : Fin n → Fin n → ℝ), fz m e z (x * ι k * a * nU (herm t) * b) * ψ t)
      = (x.det ^ e * (ι k).det ^ e * a.det ^ e * b.det ^ e) *
        ∫ (t : Fin n → Fin n → ℝ), fz m 0 z (x * ι k * a * nU (herm t) * b) * ψ t := by
    rw [← integral_const_mul]
    congr 1
    funext t
    rw [fz_twist m e z, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, det_nU, mul_one,
      mul_zpow, mul_zpow, mul_zpow]
    ring
  rw [hin, ← rhoP_twist ι hK m e Y k]
  ring

theorem eRed : ERed := by
  intro h n m e hmn Kg _ _ _ _ _ _ μ _ ι hι hK
  obtain ⟨P, ψ, a, b, x, h1, h2, h3, h4, h5⟩ := h n m hmn Kg μ ι hι hK
  refine ⟨P, ψ, a, b, x, h1, h2, h3, h4, ?_⟩
  have hKk : ∀ k, InK (ι k) := fun k => (hK (ι k)).2 ⟨k, rfl⟩
  have hfun : (fun z : ℂ => tOp μ (⇑ι) (rhoP (⇑ι) m e P) ψ a b (fz m e z) x)
      = fun z : ℂ => (x.det ^ e * a.det ^ e * b.det ^ e) * tOp μ (⇑ι) (rhoP (⇑ι) m 0 P) ψ a b (fz m 0 z) x := by
    funext z
    exact tOp_twist μ ι hKk m e P ψ a b x z
  rw [hfun, deriv_const_mul_field']
  refine mul_ne_zero ?_ h5
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · exact zpow_ne_zero _ (isUnit_det_of_InG h4).ne_zero
  · exact zpow_ne_zero _ (isUnit_det_of_InG h2).ne_zero
  · exact zpow_ne_zero _ (isUnit_det_of_InG h3).ne_zero

end PositivityTheory.Rg.Sw.HSt
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private theorem finiteDimensional_continuousMultilinearMap {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (N : ℕ) : FiniteDimensional ℂ (ContinuousMultilinearMap ℂ (fun _ : Fin N => E) ℂ) :=
  FiniteDimensional.of_injective (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℂ) (A := ℂ))
    (fun _ _ h => ContinuousMultilinearMap.toMultilinearMap_injective h)

private theorem aestronglyMeasurable_of_continuous {Kg : Type} [TopologicalSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
    (μ : Measure Kg) {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (f : Kg → W) (hf : Continuous f) : AEStronglyMeasurable f μ := by
  haveI : ProperSpace W := FiniteDimensional.proper ℂ W
  haveI : SecondCountableTopology W := secondCountable_of_proper
  exact hf.aestronglyMeasurable

private theorem integrable_of_continuous_isFiniteMeasure {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [IsFiniteMeasure μ] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] (f : Kg → W) (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound (aestronglyMeasurable_of_continuous μ f hf) C (Filter.Eventually.of_forall fun k => hC k trivial)

private theorem matrix_mul_comm_of_mul_eq_smul_one_of_ne_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [IsFiniteMeasure μ] (Ω : Set E) (G : Kg → E → ℂ)
    (hΩ : IsOpen Ω)
    (hc : ∀ N : ℕ, ContinuousOn (fun y : Kg × E => iteratedFDeriv ℂ N (G y.1) y.2) (Set.univ ×ˢ Ω))
    (hd : ∀ k, ContDiffOn ℂ ∞ (G k) Ω) :
    (∀ N : ℕ, ∀ x ∈ Ω, iteratedFDeriv ℂ N (fun x => ∫ k, G k x ∂μ) x = ∫ k, iteratedFDeriv ℂ N (G k) x ∂μ) ∧
      ContDiffOn ℂ ∞ (fun x => ∫ k, G k x ∂μ) Ω := by
  haveI : ProperSpace E := FiniteDimensional.proper ℂ E
  have hck : ∀ (N : ℕ) (x : E), x ∈ Ω → Continuous (fun k => iteratedFDeriv ℂ N (G k) x) :=
    fun N x hx => (hc N).comp_continuous (continuous_id.prodMk continuous_const) (fun k => ⟨trivial, hx⟩)
  have hdiff : ∀ (N : ℕ) (k : Kg) (x : E), x ∈ Ω →
      HasFDerivAt (iteratedFDeriv ℂ N (G k)) (fderiv ℂ (iteratedFDeriv ℂ N (G k)) x) x := by
    intro N k x hx
    have h1 := (hd k).differentiableOn_iteratedFDerivWithin (m := N) (by exact_mod_cast WithTop.coe_lt_top _)
      hΩ.uniqueDiffOn
    have h2 : DifferentiableAt ℂ (iteratedFDerivWithin ℂ N (G k) Ω) x :=
      (h1 x hx).differentiableAt (hΩ.mem_nhds hx)
    have h3 : iteratedFDeriv ℂ N (G k) =ᶠ[nhds x] iteratedFDerivWithin ℂ N (G k) Ω :=
      Filter.eventually_of_mem (hΩ.mem_nhds hx) (fun y hy => (iteratedFDerivWithin_of_isOpen N hΩ hy).symm)
    exact (h2.congr_of_eventuallyEq h3).hasFDerivAt
  have hnorm : ∀ (N : ℕ) (k : Kg) (x : E),
      ‖fderiv ℂ (iteratedFDeriv ℂ N (G k)) x‖ = ‖iteratedFDeriv ℂ (N + 1) (G k) x‖ := by
    intro N k x
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, LinearIsometryEquiv.norm_map]
  have hsucc : ∀ (N : ℕ) (k : Kg) (x : E), fderiv ℂ (iteratedFDeriv ℂ N (G k)) x =
      continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (N + 1) => E) ℂ (iteratedFDeriv ℂ (N + 1) (G k) x) := by
    intro N k x
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
  have hstep : ∀ (N : ℕ) (x : E), x ∈ Ω → HasFDerivAt (fun y => ∫ k, iteratedFDeriv ℂ N (G k) y ∂μ)
      (∫ k, fderiv ℂ (iteratedFDeriv ℂ N (G k)) x ∂μ) x := by
    intro N x hx
    haveI := finiteDimensional_continuousMultilinearMap (E := E) N
    haveI := finiteDimensional_continuousMultilinearMap (E := E) (N + 1)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ x hx
    have hcb : Metric.closedBall x (ε / 2) ⊆ Ω :=
      (Metric.closedBall_subset_ball (by linarith)).trans hball
    obtain ⟨C, hC⟩ := (isCompact_univ.prod (isCompact_closedBall x (ε / 2))).exists_bound_of_continuousOn
      ((hc (N + 1)).mono (Set.prod_mono le_rfl hcb))
    have hmeas' : AEStronglyMeasurable (fun k => fderiv ℂ (iteratedFDeriv ℂ N (G k)) x) μ := by
      have : (fun k => fderiv ℂ (iteratedFDeriv ℂ N (G k)) x) = fun k =>
          continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (N + 1) => E) ℂ (iteratedFDeriv ℂ (N + 1) (G k) x) :=
        funext fun k => hsucc N k x
      rw [this]
      exact (LinearIsometryEquiv.continuous _).comp_aestronglyMeasurable (aestronglyMeasurable_of_continuous μ _ (hck (N + 1) x hx))
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (x₀ := x)
      (F := fun y k => iteratedFDeriv ℂ N (G k) y)
      (F' := fun y k => fderiv ℂ (iteratedFDeriv ℂ N (G k)) y) (bound := fun _ => C)
      (Metric.ball_mem_nhds x (half_pos hε))
      (Filter.eventually_of_mem (Metric.ball_mem_nhds x (half_pos hε))
        (fun y hy => aestronglyMeasurable_of_continuous μ _ (hck N y (hcb (Metric.ball_subset_closedBall hy)))))
      (integrable_of_continuous_isFiniteMeasure μ _ (hck N x hx)) hmeas'
      (Filter.Eventually.of_forall fun k y hy => by
        rw [hnorm]
        exact hC (k, y) ⟨trivial, Metric.ball_subset_closedBall hy⟩)
      (integrable_const C)
      (Filter.Eventually.of_forall fun k y hy => hdiff N k y (hcb (Metric.ball_subset_closedBall hy)))
  have key : ∀ N : ℕ, ∀ x ∈ Ω,
      iteratedFDeriv ℂ N (fun x => ∫ k, G k x ∂μ) x = ∫ k, iteratedFDeriv ℂ N (G k) x ∂μ := by
    intro N
    induction N with
    | zero =>
      intro x hx
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
      exact ((continuousMultilinearCurryFin0 ℂ E ℂ).symm.toContinuousLinearEquiv.integral_comp_comm _).symm
    | succ N ih =>
      intro x hx
      have hev : iteratedFDeriv ℂ N (fun x => ∫ k, G k x ∂μ) =ᶠ[nhds x]
          fun y => ∫ k, iteratedFDeriv ℂ N (G k) y ∂μ :=
        Filter.eventually_of_mem (hΩ.mem_nhds hx) ih
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hev.fderiv_eq, (hstep N x hx).fderiv]
      have hcomm := (continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (N + 1) => E) ℂ).symm.toContinuousLinearEquiv.integral_comp_comm
        (μ := μ) (fun k => fderiv ℂ (iteratedFDeriv ℂ N (G k)) x)
      refine hcomm.symm.trans ?_
      congr 1
  have hdΦ : ∀ (N : ℕ) (x : E), x ∈ Ω → DifferentiableAt ℂ (iteratedFDeriv ℂ N (fun x => ∫ k, G k x ∂μ)) x :=
    fun N x hx => (hstep N x hx).differentiableAt.congr_of_eventuallyEq
      (Filter.eventually_of_mem (hΩ.mem_nhds hx) (key N))
  refine ⟨key, ?_⟩
  apply contDiffOn_of_continuousOn_differentiableOn
  · intro m _
    exact ContinuousOn.congr (f := iteratedFDeriv ℂ m (fun x => ∫ k, G k x ∂μ))
      (fun x hx => (hdΦ m x hx).continuousAt.continuousWithinAt) (iteratedFDerivWithin_of_isOpen m hΩ)
  · intro m _
    exact DifferentiableOn.congr (f := iteratedFDeriv ℂ m (fun x => ∫ k, G k x ∂μ))
      (fun x hx => (hdΦ m x hx).differentiableWithinAt) (iteratedFDerivWithin_of_isOpen m hΩ)

private theorem iteratedFDeriv_comp_clm_mul_const {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : E → ℂ) (U : Set E) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (L : E →L[ℂ] E) (a : ℂ) (N : ℕ)
    (y : E) (hy : L y ∈ U) :
    iteratedFDeriv ℂ N (fun y => F (L y) * a) y =
      a • (iteratedFDeriv ℂ N F (L y)).compContinuousLinearMap (fun _ => L) := by
  have hopen : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have hFL : ContDiffOn ℂ ∞ (F ∘ L) (L ⁻¹' U) := hF.comp L.contDiff.contDiffOn (fun _ h => h)
  have hfun : (fun y => F (L y) * a) = ((ContinuousLinearMap.mul ℂ ℂ).flip a) ∘ (F ∘ L) := by
    funext z
    simp [mul_comm]
  rw [← iteratedFDerivWithin_of_isOpen N hopen hy, hfun,
    ((ContinuousLinearMap.mul ℂ ℂ).flip a).iteratedFDerivWithin_comp_left (hFL y hy) hopen.uniqueDiffOn hy
      (by exact_mod_cast (WithTop.coe_lt_top _).le),
    L.iteratedFDerivWithin_comp_right hF hU.uniqueDiffOn hopen.uniqueDiffOn hy
      (by exact_mod_cast (WithTop.coe_lt_top _).le),
    iteratedFDerivWithin_of_isOpen N hU hy]
  ext v
  simp [mul_comm]

private theorem exists_ne_zero_smul_mem_of_mem_span' {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
    (μ : Measure Kg) [IsFiniteMeasure μ] (F : E → ℂ) (U : Set E) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U)
    (L : Kg → E →L[ℂ] E) (hL : Continuous L) (c : Kg → ℂ) (hc : Continuous c) :
    IsOpen {y | ∀ k, L k y ∈ U} ∧
      ContDiffOn ℂ ∞ (fun y => ∫ k, F (L k y) * c k ∂μ) {y | ∀ k, L k y ∈ U} ∧
      (∀ (N : ℕ) (y : E), (∀ k, L k y ∈ U) →
        iteratedFDeriv ℂ N (fun y => ∫ k, F (L k y) * c k ∂μ) y =
          ∫ k, iteratedFDeriv ℂ N (fun y => F (L k y) * c k) y ∂μ) ∧
      ∀ (N : ℕ) (y : E), (∀ k, L k y ∈ U) →
        Integrable (fun k => iteratedFDeriv ℂ N (fun y => F (L k y) * c k) y) μ := by
  have hW : IsOpen {y | ∀ k, L k y ∈ U} := by
    rw [isOpen_iff_mem_nhds]
    intro y0 hy0
    have hcont : Continuous fun z : E × Kg => L z.2 z.1 := (hL.comp continuous_snd).clm_apply continuous_fst
    have h := isCompact_univ.eventually_forall_of_forall_eventually (x₀ := y0) (P := fun y k => L k y ∈ U)
      (fun k _ => hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds (hy0 k)))
    filter_upwards [h] with y hy
    exact fun k => hy k trivial
  have hG : ∀ N : ℕ, ContinuousOn (fun p : Kg × E => iteratedFDeriv ℂ N (fun y => F (L p.1 y) * c p.1) p.2)
      (Set.univ ×ˢ {y | ∀ k, L k y ∈ U}) := by
    intro N
    have hDF : ContinuousOn (iteratedFDeriv ℂ N F) U :=
      (hF.continuousOn_iteratedFDerivWithin (m := N) (by exact_mod_cast (WithTop.coe_lt_top _).le)
        hU.uniqueDiffOn).congr (fun x hx => (iteratedFDerivWithin_of_isOpen N hU hx).symm)
    have h1 : ContinuousOn (fun p : Kg × E => iteratedFDeriv ℂ N F (L p.1 p.2)) (Set.univ ×ˢ {y | ∀ k, L k y ∈ U}) :=
      hDF.comp ((hL.comp continuous_fst).clm_apply continuous_snd).continuousOn (fun p hp => hp.2 p.1)
    have h2 : Continuous (fun p : Kg × E => ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℂ
        (fun _ : Fin N => E) (fun _ => E) ℂ (fun _ => L p.1)) :=
      (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℂ
        (fun _ : Fin N => E) (fun _ => E) ℂ).cont.comp (continuous_pi fun _ => hL.comp continuous_fst)
    refine ContinuousOn.congr (((hc.comp continuous_fst).continuousOn).smul (h2.continuousOn.clm_apply h1)) ?_
    intro p hp
    dsimp only
    rw [iteratedFDeriv_comp_clm_mul_const F U hU hF (L p.1) (c p.1) N p.2 (hp.2 p.1)]
    simp
  have hdG : ∀ k, ContDiffOn ℂ ∞ (fun y => F (L k y) * c k) {y | ∀ k, L k y ∈ U} :=
    fun k => (hF.comp (L k).contDiff.contDiffOn (fun y (hy : ∀ k, L k y ∈ U) => hy k)).mul contDiffOn_const
  obtain ⟨key, hcd⟩ := matrix_mul_comm_of_mul_eq_smul_one_of_ne_zero μ {y | ∀ k, L k y ∈ U} (fun k y => F (L k y) * c k) hW hG hdG
  refine ⟨hW, hcd, fun N y hy => key N y hy, fun N y hy => ?_⟩
  haveI := finiteDimensional_continuousMultilinearMap (E := E) N
  exact integrable_of_continuous_isFiniteMeasure μ _ ((hG N).comp_continuous (continuous_id.prodMk continuous_const) (fun k => ⟨trivial, hy⟩))

private theorem exists_continuous_clm_of_bilinear {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (m : E →ₗ[ℂ] E →ₗ[ℂ] E) : ∃ Lc : E → E →L[ℂ] E, Continuous Lc ∧ ∀ a y, Lc a y = m a y := by
  refine ⟨fun a => LinearMap.toContinuousLinearMap (m a), ?_, fun a y => rfl⟩
  exact LinearMap.continuous_of_finiteDimensional
    ((LinearMap.toContinuousLinearMap : (E →ₗ[ℂ] E) ≃ₗ[ℂ] (E →L[ℂ] E)).toLinearMap ∘ₗ m)

theorem sphU : SphU := by
  intro n F U hU hF Kg _ _ _ _ μ _ _ ι hι c hc ιA ιB _ _ _ _ LA LB hLA hLB g hg
  have hF' : ContDiffOn ℂ ∞ F U := hF.of_le le_top
  obtain ⟨Lc, hLc, hLapp⟩ := exists_continuous_clm_of_bilinear (E := M2 n) (LinearMap.mul ℂ (M2 n))
  simp only [LinearMap.mul_apply'] at hLapp
  obtain ⟨hWo, hΦ, key, hint⟩ := exists_ne_zero_smul_mem_of_mem_span' (E := M2 n) μ F U hU hF' (fun k => Lc (ι k)) (hLc.comp hι) c hc
  simp only [hLapp] at hWo hΦ key hint
  have hgW : ∀ k, ι k * g ∈ U := hg
  have hL := detD_detD_comp (fun y => ∫ k, F (ι k * y) * c k ∂μ) _ hWo hΦ g hgW (LA g) (LB g)
  beta_reduce at hL
  simp only [hLA, hLB, ← mul_add]
  rw [hL, key _ g hgW]
  simp only [ContinuousMultilinearMap.integral_apply (hint _ g hgW)]
  have hR : ∀ k, (detD fun T : Matrix ιA ιA ℂ => detD fun S : Matrix ιB ιB ℂ =>
      F (ι k * (g + (LA g) T + (LB g) S))) * c k =
      ∑ σ : Equiv.Perm ιA, ∑ τ : Equiv.Perm ιB, ↑↑(Equiv.Perm.sign σ) * ↑↑(Equiv.Perm.sign τ) *
        (iteratedFDeriv ℂ (Fintype.card ιA + Fintype.card ιB) (fun y => F (ι k * y) * c k) g)
          (Fin.append (fun i => LA g (single ((Fintype.equivFin ιA).symm i) (σ ((Fintype.equivFin ιA).symm i)) 1))
            (fun i => LB g (single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) := by
    intro k
    have hFk : ContDiffOn ℂ ∞ (fun y => F (ι k * y)) {y : M2 n | ∀ k, ι k * y ∈ U} :=
      (hF'.comp (Lc (ι k)).contDiff.contDiffOn (fun y (hy : ∀ k, ι k * y ∈ U) => by rw [hLapp]; exact hy k)).congr
        (fun y _ => by rw [Function.comp_apply, hLapp])
    have h1 := detD_detD_mul_const (fun y => F (ι k * y)) _ hWo hFk g hgW (LA g) (LB g) (c k)
    have h2 := detD_detD_comp (fun y => F (ι k * y) * c k) _ hWo (hFk.mul contDiffOn_const) g hgW (LA g) (LB g)
    beta_reduce at h1 h2
    rw [← h1, h2]
  simp only [hR]
  rw [integral_finset_sum _ (fun σ _ => ?_)]
  · refine Finset.sum_congr rfl fun σ _ => ?_
    rw [integral_finset_sum _ (fun τ _ => ?_)]
    · refine Finset.sum_congr rfl fun τ _ => ?_
      rw [integral_const_mul]
    · exact ((ContinuousMultilinearMap.apply ℂ _ ℂ _).integrable_comp (hint _ g hgW)).const_mul _
  · exact integrable_finset_sum _ fun τ _ =>
      ((ContinuousMultilinearMap.apply ℂ _ ℂ _).integrable_comp (hint _ g hgW)).const_mul _

end PositivityTheory.Rg.Sw.HSt
end
end

section
noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem deriv_eq_fderiv_pair (U : ℂ × V → ℂ) (z0 : ℂ) (w : V) (hU : DifferentiableAt ℂ U (z0, w)) :
    deriv (fun z => U (z, w)) z0 = fderiv ℂ U (z0, w) (1, 0) := by
  have hl : HasDerivAt (fun z : ℂ => (z, w)) ((1 : ℂ), (0 : V)) z0 := (hasDerivAt_id z0).prodMk (hasDerivAt_const z0 w)
  exact (hU.hasFDerivAt.comp_hasDerivAt z0 hl).deriv

theorem iFD_slice (U : ℂ × V → ℂ) (D : Set V) (hD : IsOpen D) (hU : ContDiffOn ℂ ∞ U (Set.univ ×ˢ D))
    (z : ℂ) (w0 : V) (hw0 : w0 ∈ D) (k : ℕ) (v : Fin k → V) :
    iteratedFDeriv ℂ k (fun w => U (z, w)) w0 v = iteratedFDeriv ℂ k U (z, w0) (fun i => ((0 : ℂ), v i)) := by
  have hs : IsOpen (Set.univ ×ˢ D : Set (ℂ × V)) := isOpen_univ.prod hD
  have hU' : ContDiffOn ℂ ∞ (fun p : ℂ × V => U ((z, 0) + p)) (Set.univ ×ˢ D) :=
    hU.comp (contDiff_const.add contDiff_id).contDiffOn (fun p hp => ⟨trivial, by simpa using hp.2⟩)
  have hpre : (ContinuousLinearMap.inr ℂ ℂ V) ⁻¹' (Set.univ ×ˢ D) = D := by
    ext w
    simp
  have hfun : (fun w => U (z, w)) = (fun p : ℂ × V => U ((z, 0) + p)) ∘ (ContinuousLinearMap.inr ℂ ℂ V) := by
    funext w
    simp
  have hgw : ContinuousLinearMap.inr ℂ ℂ V w0 ∈ (Set.univ ×ˢ D : Set (ℂ × V)) := ⟨trivial, hw0⟩
  have hD' : IsOpen ((ContinuousLinearMap.inr ℂ ℂ V) ⁻¹' (Set.univ ×ˢ D)) := by rw [hpre]; exact hD
  rw [hfun, ← iteratedFDerivWithin_of_isOpen k hD' (by rw [hpre]; exact hw0),
    (ContinuousLinearMap.inr ℂ ℂ V).iteratedFDerivWithin_comp_right hU' hs.uniqueDiffOn hD'.uniqueDiffOn hgw
      (by exact_mod_cast (WithTop.coe_lt_top _).le),
    iteratedFDerivWithin_of_isOpen k hs hgw, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_comp_add_left]
  simp

private theorem natCast_le_infty_withTop (a : ℕ) : ((a : ℕ) : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

private theorem inv_mul_mul_mul_eq_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : E → ℂ) (S : Set E)
    (hS : IsOpen S) (hf : ContDiffOn ℂ ∞ f S) (e : E) (k : ℕ) :
    ∀ y ∈ S, iteratedFDeriv ℂ k (fun p => fderiv ℂ f p e) y = fderiv ℂ (iteratedFDeriv ℂ k f) y e := by
  induction k with
  | zero =>
    intro y hy
    have hd : DifferentiableAt ℂ f y :=
      (hf.contDiffAt (hS.mem_nhds hy)).differentiableAt (by simp)
    rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp, LinearIsometryEquiv.comp_fderiv]
    ext m
    simp
  | succ k ih =>
    intro y hy
    have hev : iteratedFDeriv ℂ k (fun p => fderiv ℂ f p e) =ᶠ[nhds y]
        fun p => fderiv ℂ (iteratedFDeriv ℂ k f) p e :=
      Filter.eventually_of_mem (hS.mem_nhds hy) ih
    have hg : ContDiffAt ℂ 2 (iteratedFDeriv ℂ k f) y :=
      (hf.contDiffAt (hS.mem_nhds hy)).iteratedFDeriv_right (by
        have h : ((2 + k : ℕ) : WithTop ℕ∞) ≤ ∞ := natCast_le_infty_withTop _
        exact_mod_cast h)
    have hsym : IsSymmSndFDerivAt ℂ (iteratedFDeriv ℂ k f) y :=
      hg.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
    have hdg : DifferentiableAt ℂ (fderiv ℂ (iteratedFDeriv ℂ k f)) y :=
      (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    have happ : fderiv ℂ (fun p => fderiv ℂ (iteratedFDeriv ℂ k f) p e) y =
        (ContinuousLinearMap.apply ℂ (ContinuousMultilinearMap ℂ (fun _ : Fin k => E) ℂ) e).comp (fderiv ℂ (fderiv ℂ (iteratedFDeriv ℂ k f)) y) :=
      ((ContinuousLinearMap.apply ℂ (ContinuousMultilinearMap ℂ (fun _ : Fin k => E) ℂ) e).hasFDerivAt.comp y
        hdg.hasFDerivAt).fderiv
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hev.fderiv_eq, happ,
      iteratedFDeriv_succ_eq_comp_left, LinearIsometryEquiv.comp_fderiv]
    ext m
    simp [hsym (m 0) e]

theorem iFD_deriv_comm (U : ℂ × V → ℂ) (D : Set V) (hD : IsOpen D) (hU : ContDiffOn ℂ ∞ U (Set.univ ×ˢ D))
    (w0 : V) (hw0 : w0 ∈ D) (k : ℕ) (v : Fin k → V) :
    iteratedFDeriv ℂ k (fun w => deriv (fun z => U (z, w)) 0) w0 v =
      deriv (fun z => iteratedFDeriv ℂ k (fun w => U (z, w)) w0 v) 0 := by
  have hs : IsOpen (Set.univ ×ˢ D : Set (ℂ × V)) := isOpen_univ.prod hD
  have hdiffU : ∀ p ∈ (Set.univ ×ˢ D : Set (ℂ × V)), DifferentiableAt ℂ U p := fun p hp =>
    (hU.contDiffAt (hs.mem_nhds hp)).differentiableAt (by simp)
  have hU1 : ContDiffOn ℂ ∞ (fun p => fderiv ℂ U p ((1 : ℂ), (0 : V))) (Set.univ ×ˢ D) :=
    (hU.fderiv_of_isOpen hs (m := ∞) (by exact le_of_eq (by rfl))).clm_apply contDiffOn_const
  have hL : (fun w => deriv (fun z => U (z, w)) 0) =ᶠ[nhds w0] fun w => fderiv ℂ U (0, w) ((1 : ℂ), (0 : V)) :=
    Filter.eventually_of_mem (hD.mem_nhds hw0) fun w hw => deriv_eq_fderiv_pair U 0 w (hdiffU (0, w) ⟨trivial, hw⟩)
  rw [((Filter.EventuallyEq.iteratedFDeriv ℂ hL k).eq_of_nhds),
    iFD_slice (fun p => fderiv ℂ U p ((1 : ℂ), (0 : V))) D hD hU1 0 w0 hw0 k v]
  have hR : (fun z => iteratedFDeriv ℂ k (fun w => U (z, w)) w0 v) =
      fun z => iteratedFDeriv ℂ k U (z, w0) (fun i => ((0 : ℂ), v i)) :=
    funext fun z => iFD_slice U D hD hU z w0 hw0 k v
  have hdI : DifferentiableAt ℂ (iteratedFDeriv ℂ k U) (0, w0) :=
    ((hU.contDiffAt (hs.mem_nhds ⟨trivial, hw0⟩)).iteratedFDeriv_right (m := 1) (by
      have h : ((1 + k : ℕ) : WithTop ℕ∞) ≤ ∞ := natCast_le_infty_withTop _
      exact_mod_cast h)).differentiableAt one_ne_zero
  have hdΦ : DifferentiableAt ℂ (fun p => iteratedFDeriv ℂ k U p (fun i => ((0 : ℂ), v i))) (0, w0) :=
    (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => ℂ × V) ℂ (fun i => ((0 : ℂ), v i))).differentiableAt.comp _ hdI
  rw [hR, deriv_eq_fderiv_pair _ 0 w0 hdΦ, inv_mul_mul_mul_eq_mul U _ hs hU _ k (0, w0) ⟨trivial, hw0⟩]
  have h2 : fderiv ℂ (fun p => iteratedFDeriv ℂ k U p (fun i => ((0 : ℂ), v i))) (0, w0) =
      (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => ℂ × V) ℂ (fun i => ((0 : ℂ), v i))).comp
        (fderiv ℂ (iteratedFDeriv ℂ k U) (0, w0)) :=
    ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => ℂ × V) ℂ (fun i => ((0 : ℂ), v i))).hasFDerivAt.comp
      (0, w0) hdI.hasFDerivAt).fderiv
  rw [h2]
  simp

end PositivityTheory.Rg.Sw.HSt
end
end

section
noncomputable section

open Matrix Filter Topology Set

namespace PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem abs_arg_lt_pi {P : ℂ} (hP : P ∈ Complex.slitPlane) : |P.arg| < Real.pi := by
  rw [abs_lt]
  exact ⟨Complex.neg_pi_lt_arg P, lt_of_le_of_ne (Complex.arg_le_pi P) (Complex.slitPlane_arg_ne_pi hP)⟩

theorem cpow_split {P a b : ℂ} (hP : P ∈ Complex.slitPlane) (ha : a ≠ 0) (hb : b ≠ 0)
    (ha' : |a.arg| < (Real.pi - |P.arg|) / 2) (hb' : |b.arg| < (Real.pi - |P.arg|) / 2) (w : ℂ) :
    (P * a * b) ^ w = P ^ w * a ^ w * b ^ w := by
  have hP0 : P ≠ 0 := Complex.slitPlane_ne_zero hP
  have hPpi := abs_arg_lt_pi hP
  have hpos : 0 ≤ Real.pi - |P.arg| := by linarith
  have h1 : P.arg + a.arg ∈ Ioc (-Real.pi) Real.pi := by
    have := abs_add_le P.arg a.arg
    constructor
    · linarith [neg_abs_le (P.arg + a.arg)]
    · linarith [le_abs_self (P.arg + a.arg)]
  have hPa : P * a ≠ 0 := mul_ne_zero hP0 ha
  have harg : (P * a).arg = P.arg + a.arg := by
    have := congrArg Complex.im (Complex.log_mul hP0 ha h1)
    simpa [Complex.log_im] using this
  have h2 : (P * a).arg + b.arg ∈ Ioc (-Real.pi) Real.pi := by
    rw [harg]
    have := abs_add_le (P.arg + a.arg) b.arg
    have := abs_add_le P.arg a.arg
    constructor
    · linarith [neg_abs_le (P.arg + a.arg + b.arg)]
    · linarith [le_abs_self (P.arg + a.arg + b.arg)]
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hPa hb), Complex.log_mul hPa hb h2, Complex.log_mul hP0 ha h1,
    Complex.cpow_def_of_ne_zero hP0, Complex.cpow_def_of_ne_zero ha, Complex.cpow_def_of_ne_zero hb,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

theorem detD_congr {ι : Type} [Fintype ι] [DecidableEq ι] {F G : Matrix ι ι ℂ → ℂ} (h : F =ᶠ[𝓝 0] G) :
    detD F = detD G := by
  unfold detD
  rw [(h.iteratedFDeriv ℂ (Fintype.card ι)).eq_of_nhds]

theorem ev_small {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {c : E → ℂ} (hc : ContinuousAt c 0) (h0 : c 0 = 1)
    {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ T in 𝓝 (0 : E), c T ≠ 0 ∧ |(c T).arg| < δ := by
  have hne : ∀ᶠ T in 𝓝 (0 : E), c T ≠ 0 := hc.eventually_ne (by rw [h0]; exact one_ne_zero)
  have hcont : ContinuousAt (fun T => (c T).arg) 0 :=
    ContinuousAt.comp (f := c) (g := Complex.arg) (Complex.continuousAt_arg (by rw [h0]; exact Complex.one_mem_slitPlane)) hc
  have ht : Tendsto (fun T => (c T).arg) (𝓝 0) (𝓝 0) := by
    have := hcont.tendsto
    simpa [h0, Complex.arg_one] using this
  filter_upwards [hne, ht (Metric.ball_mem_nhds 0 hδ)] with T h1 h2
  refine ⟨h1, ?_⟩
  simpa [Metric.mem_ball, Real.dist_eq] using h2

private theorem mul_toBlocks₂₁' (A B : M2 n) :
    (A * B).toBlocks₂₁ = A.toBlocks₂₁ * B.toBlocks₁₁ + A.toBlocks₂₂ * B.toBlocks₂₁ := by
  ext i j
  simp [Matrix.toBlocks₂₁, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type]

private theorem mul_toBlocks₂₂ (A B : M2 n) :
    (A * B).toBlocks₂₂ = A.toBlocks₂₁ * B.toBlocks₁₂ + A.toBlocks₂₂ * B.toBlocks₂₂ := by
  ext i j
  simp [Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type]

private theorem u1_mul_mX_one_eq_add (x : M2 n) (Q R : Matrix (Fin n) (Fin n) ℂ) :
    u1 (x * mX 1 Q R 1) = u1 x + u2 x * R := by
  have hinv : (Cm n)⁻¹ = Cmi n := Matrix.inv_eq_left_inv cmi_mul_cm
  have hxc21 : (x * Cm n).toBlocks₂₁ = u1 x := by
    rw [mul_toBlocks₂₁', Cm, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁, u1]
    simp [Matrix.mul_smul]
  have hxc22 : (x * Cm n).toBlocks₂₂ = u2 x := by
    rw [mul_toBlocks₂₂, Cm, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂, u2]
    simp [Matrix.mul_smul]
  rw [mX, hinv, show x * (Cm n * fromBlocks 1 Q R 1 * Cmi n) = (x * Cm n * fromBlocks 1 Q R 1) * Cmi n by
    simp only [Matrix.mul_assoc], first_cayley_block_mul_inverse_cayley, mul_toBlocks₂₁', toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁,
    Matrix.mul_one, hxc21, hxc22]

theorem fz_mX {m : ℕ} {e : ℤ} {z : ℂ} {j : ℕ} {x : M2 n} (hx : x ∈ DomZ n)
    (T : Matrix (blkA (n := n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ)
    (h1 : (1 + subOn (blkB j) (wM x)⁻¹ * S).det ≠ 0) (h2 : (1 + subOn (blkA j) (wM x) * T).det ≠ 0)
    (h1' : |((1 + subOn (blkB j) (wM x)⁻¹ * S).det).arg| < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2)
    (h2' : |((1 + subOn (blkA j) (wM x) * T).det).arg| < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2) :
    fz m e z (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1) =
      (fz m e z x * (1 + subOn (blkA j) (wM x) * T).det ^ (-z)) *
        (1 + subOn (blkB j) (wM x)⁻¹ * S).det ^ ((-(m : ℂ)) - z) := by
  obtain ⟨hD, hP⟩ := hx
  have hD' := hD
  obtain ⟨hdet, hu1, hu2, -⟩ := hD'
  obtain ⟨hQR, hRQ⟩ := embOn_mul_embOn_compl j T S
  have hdetM : (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1).det = x.det := by
    rw [Matrix.det_mul, det_mX_one _ _ hRQ, mul_one]
  have hub : (ub1 (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)).det =
      (1 + subOn (blkA j) (wM x) * T).det * (ub1 x).det := by
    rw [inverse_first_block_mul_unipotent_domain x hD _ _ hQR hRQ, Matrix.det_mul, det_one_add_mul_comm, det_one_add_mul_embOn]
  have hw : (wM x)⁻¹ = (u1 x)⁻¹ * u2 x := by
    rw [wM, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hu2)]
  have hu : (u1 (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)).det =
      (u1 x).det * (1 + subOn (blkB j) (wM x)⁻¹ * S).det := by
    rw [u1_mul_mX_one_eq_add, ← det_one_add_mul_embOn, ← Matrix.det_mul]
    congr 1
    rw [hw, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hu1), Matrix.one_mul]
  unfold fz
  rw [hdetM, hu, hub,
    show (u1 x).det * (1 + subOn (blkB j) (wM x)⁻¹ * S).det * ((1 + subOn (blkA j) (wM x) * T).det * (ub1 x).det) =
      (u1 x).det * (ub1 x).det * (1 + subOn (blkA j) (wM x) * T).det * (1 + subOn (blkB j) (wM x)⁻¹ * S).det by ring,
    cpow_split hP h2 h1 h2' h1' (-z), mul_zpow, sub_eq_add_neg, Complex.cpow_add _ _ h1,
    show (-(m : ℂ)) = ((-(m : ℤ) : ℤ) : ℂ) by push_cast; ring, Complex.cpow_intCast]
  ring

private theorem detD_det_one_add_mul_rpow_eq {ι : Type} [Fintype ι] [DecidableEq ι] (W : Matrix ι ι ℂ) (t : ℂ) :
    (detD fun S : Matrix ι ι ℂ => (1 + W * S).det ^ t) =
      W.det * ∏ i ∈ Finset.range (Fintype.card ι), (t + (i : ℂ)) := by
  have hF : AnalyticAt ℂ (fun S : Matrix ι ι ℂ => (1 + S).det ^ t) 0 := analyticAt_det_one_add_cpow t
  have h := CEq.equivar_thm ι (fun S : Matrix ι ι ℂ => (1 + S).det ^ t) W hF
  beta_reduce at h
  rw [h]
  congr 1
  have hG : AnalyticAt ℂ (fun S : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ => (1 + S).det ^ t) 0 :=
    analyticAt_det_one_add_cpow t
  have hr := CEq.reindex_thm ι (Fin (Fintype.card ι)) (Fintype.equivFin ι) _ hG
  beta_reduce at hr
  rw [← kappaC (Fintype.card ι) t, ← hr]
  congr 1
  funext S
  have hS : (1 : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) +
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) S =
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) (1 + S) := by
    ext a b
    simp [Matrix.reindex_apply, Matrix.one_apply]
  rw [hS, Matrix.det_reindex_self]

theorem djZ : DjZ := by
  intro n m e j z x hj hx
  have hx' := hx
  obtain ⟨hD, hP⟩ := hx'
  have hδ : 0 < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2 := by
    have := abs_arg_lt_pi hP
    linarith
  have hcA : ∀ᶠ T in 𝓝 (0 : Matrix (blkA (n := n) j) (blkA j) ℂ),
      (1 + subOn (blkA j) (wM x) * T).det ≠ 0 ∧
        |((1 + subOn (blkA j) (wM x) * T).det).arg| < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2 :=
    ev_small (c := fun T => (1 + subOn (blkA j) (wM x) * T).det)
      ((continuous_const.add (continuous_const.matrix_mul continuous_id)).matrix_det.continuousAt)
      (by simp) hδ
  have hcB : ∀ᶠ S in 𝓝 (0 : Matrix (blkB (n := n) j) (blkB j) ℂ),
      (1 + subOn (blkB j) (wM x)⁻¹ * S).det ≠ 0 ∧
        |((1 + subOn (blkB j) (wM x)⁻¹ * S).det).arg| < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2 :=
    ev_small (c := fun S => (1 + subOn (blkB j) (wM x)⁻¹ * S).det)
      ((continuous_const.add (continuous_const.matrix_mul continuous_id)).matrix_det.continuousAt)
      (by simp) hδ
  have hinner : ∀ T : Matrix (blkA (n := n) j) (blkA j) ℂ,
      ((1 + subOn (blkA j) (wM x) * T).det ≠ 0 ∧
        |((1 + subOn (blkA j) (wM x) * T).det).arg| < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2) →
      (detD fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
          fz m e z (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)) =
        (fz m e z x * (1 + subOn (blkA j) (wM x) * T).det ^ (-z)) *
          ((subOn (blkB j) (wM x)⁻¹).det *
            ∏ i ∈ Finset.range (Fintype.card (blkB (n := n) j)), ((-(m : ℂ)) - z + (i : ℂ))) := by
    intro T hT
    rw [PositivityTheory.Rg.Sw.HSt.detD_congr (G := fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
        (fz m e z x * (1 + subOn (blkA j) (wM x) * T).det ^ (-z)) *
          (1 + subOn (blkB j) (wM x)⁻¹ * S).det ^ ((-(m : ℂ)) - z)) ?_,
      detD_const_mul, detD_det_one_add_mul_rpow_eq]
    filter_upwards [hcB] with S hS
    exact fz_mX hx T S hS.1 hT.1 hS.2 hT.2
  rw [PositivityTheory.Rg.Sw.HSt.detD_congr (G := fun T : Matrix (blkA (n := n) j) (blkA j) ℂ =>
      (fz m e z x * ((subOn (blkB j) (wM x)⁻¹).det *
        ∏ i ∈ Finset.range (Fintype.card (blkB (n := n) j)), ((-(m : ℂ)) - z + (i : ℂ)))) *
        (1 + subOn (blkA j) (wM x) * T).det ^ (-z)) ?_]
  · rw [detD_const_mul, detD_det_one_add_mul_rpow_eq, card_blkA hj, card_blkB hj, minorOn_eq, minorOn_eq]
    have e1 : ∏ i ∈ Finset.range j, (-z + (i : ℂ)) = ∏ i ∈ Finset.range j, ((i : ℂ) - z) :=
      Finset.prod_congr rfl (fun i _ => by ring)
    have e2 : ∏ i ∈ Finset.range (n - j), ((-(m : ℂ)) - z + (i : ℂ)) =
        ∏ i ∈ Finset.range (n - j), ((i : ℂ) - m - z) :=
      Finset.prod_congr rfl (fun i _ => by ring)
    rw [e1, e2]
    ring
  · filter_upwards [hcA] with T hT
    rw [hinner T hT]
    ring

end PositivityTheory.Rg.Sw.HSt
end
end

section
noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem fz_contDiffOn (m : ℕ) : ContDiffOn ℂ ∞ (fun p : ℂ × M2 n => fz m 0 p.1 p.2) (Set.univ ×ˢ DomZ n) :=
  ((fzHol n m 0).2.2).contDiffOn_of_completeSpace

theorem Fd_eq (m : ℕ) {y : M2 n} (hy : y ∈ DomZ n) :
    Fd m y = fderiv ℂ (fun p : ℂ × M2 n => fz m 0 p.1 p.2) (0, y) (1, 0) :=
  deriv_eq_fderiv_pair (fun p : ℂ × M2 n => fz m 0 p.1 p.2) 0 y
    (((fz_contDiffOn m).contDiffAt ((isOpen_univ.prod isOpen_domZ).mem_nhds ⟨Set.mem_univ _, hy⟩)).differentiableAt
      (by simp))

theorem Fd_contDiffOn (m : ℕ) : ContDiffOn ℂ ∞ (Fd (n := n) m) (DomZ n) := by
  have hO : IsOpen (Set.univ ×ˢ DomZ n : Set (ℂ × M2 n)) := isOpen_univ.prod isOpen_domZ
  have h1 : ContDiffOn ℂ ∞ (fun p : ℂ × M2 n => fderiv ℂ (fun p : ℂ × M2 n => fz m 0 p.1 p.2) p (1, 0))
      (Set.univ ×ˢ DomZ n) :=
    ((fz_contDiffOn m).fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  have h2 : ContDiffOn ℂ ∞ (fun y : M2 n => fderiv ℂ (fun p : ℂ × M2 n => fz m 0 p.1 p.2) (0, y) (1, 0)) (DomZ n) :=
    h1.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun y hy => ⟨Set.mem_univ _, hy⟩)
  exact h2.congr fun y hy => Fd_eq m hy

theorem fz_slice_contDiffOn (m : ℕ) (z : ℂ) : ContDiffOn ℂ ∞ (fz (n := n) m 0 z) (DomZ n) := by
  have hl : ContDiff ℂ ∞ (fun y : M2 n => ((z : ℂ), y)) := contDiff_const.prodMk contDiff_id
  have h := (fz_contDiffOn (n := n) m).comp hl.contDiffOn (fun y hy => (⟨Set.mem_univ _, hy⟩ : ((z : ℂ), y) ∈ Set.univ ×ˢ DomZ n))
  exact h

theorem djFd : DjFd := by
  intro n m j x hj1 hj hx
  set U : ℂ × M2 n → ℂ := fun p => fz m 0 p.1 p.2 with hUdef
  have hU : ContDiffOn ℂ ∞ U (Set.univ ×ˢ DomZ n) := fz_contDiffOn m
  have hD : IsOpen (DomZ n) := isOpen_domZ
  have hO : IsOpen (Set.univ ×ˢ DomZ n : Set (ℂ × M2 n)) := isOpen_univ.prod hD
  have expand : ∀ F : M2 n → ℂ, ContDiffOn ℂ ∞ F (DomZ n) →
      detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
        F (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1))) =
      ∑ σ : Equiv.Perm (blkA (n := n) j), ∑ τ : Equiv.Perm (blkB (n := n) j),
        (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card (blkA (n := n) j) + Fintype.card (blkB (n := n) j)) F x
          (Fin.append (fun i => LQ (blkA j) x (Matrix.single ((Fintype.equivFin (blkA (n := n) j)).symm i)
              (σ ((Fintype.equivFin (blkA (n := n) j)).symm i)) 1))
            (fun i => LR (blkB j) x (Matrix.single ((Fintype.equivFin (blkB (n := n) j)).symm i)
              (τ ((Fintype.equivFin (blkB (n := n) j)).symm i)) 1))) := by
    intro F hF
    have hrw : (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
        F (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1))) =
        (fun T => detD (fun S => F (x + LQ (blkA j) x T + LR (blkB j) x S))) := by
      funext T; congr 1; funext S; rw [mul_mX, LQ_apply, LR_apply]
    rw [hrw]
    exact detD_detD_comp F (DomZ n) hD hF x hx (LQ (blkA j) x) (LR (blkB j) x)
  have hcomm : ∀ (k : ℕ) (v : Fin k → M2 n), iteratedFDeriv ℂ k (Fd m) x v =
      deriv (fun z => iteratedFDeriv ℂ k (fz m 0 z) x v) 0 := fun k v =>
    iFD_deriv_comm U (DomZ n) hD hU x hx k v
  have hdiff : ∀ (k : ℕ) (v : Fin k → M2 n), DifferentiableAt ℂ (fun z => iteratedFDeriv ℂ k (fz m 0 z) x v) 0 := by
    intro k v
    have e : (fun z => iteratedFDeriv ℂ k (fz m 0 z) x v) =
        fun z => iteratedFDeriv ℂ k U (z, x) (fun i => ((0 : ℂ), v i)) :=
      funext fun z => iFD_slice U (DomZ n) hD hU z x hx k v
    rw [e]
    have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ k U) (0, x) :=
      (hU.contDiffAt (hO.mem_nhds ⟨Set.mem_univ _, hx⟩)).differentiableAt_iteratedFDeriv
        (by exact_mod_cast ENat.natCast_lt_top k)
    have hl : DifferentiableAt ℂ (fun z : ℂ => (z, x)) 0 := differentiableAt_id.prodMk (differentiableAt_const x)
    exact (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => ℂ × M2 n) ℂ (fun i => ((0 : ℂ), v i))).differentiableAt.comp
      (0 : ℂ) (hd.comp (0 : ℂ) hl)
  rw [expand (Fd m) (Fd_contDiffOn m)]
  simp_rw [hcomm]
  have hsum : deriv (fun z => ∑ σ : Equiv.Perm (blkA (n := n) j), ∑ τ : Equiv.Perm (blkB (n := n) j),
        (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card (blkA (n := n) j) + Fintype.card (blkB (n := n) j)) (fz m 0 z) x
          (Fin.append (fun i => LQ (blkA j) x (Matrix.single ((Fintype.equivFin (blkA (n := n) j)).symm i)
              (σ ((Fintype.equivFin (blkA (n := n) j)).symm i)) 1))
            (fun i => LR (blkB j) x (Matrix.single ((Fintype.equivFin (blkB (n := n) j)).symm i)
              (τ ((Fintype.equivFin (blkB (n := n) j)).symm i)) 1)))) 0 =
      ∑ σ : Equiv.Perm (blkA (n := n) j), ∑ τ : Equiv.Perm (blkB (n := n) j),
        (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        deriv (fun z => iteratedFDeriv ℂ (Fintype.card (blkA (n := n) j) + Fintype.card (blkB (n := n) j)) (fz m 0 z) x
          (Fin.append (fun i => LQ (blkA j) x (Matrix.single ((Fintype.equivFin (blkA (n := n) j)).symm i)
              (σ ((Fintype.equivFin (blkA (n := n) j)).symm i)) 1))
            (fun i => LR (blkB j) x (Matrix.single ((Fintype.equivFin (blkB (n := n) j)).symm i)
              (τ ((Fintype.equivFin (blkB (n := n) j)).symm i)) 1)))) 0 := by
    rw [deriv_fun_sum (fun σ _ => DifferentiableAt.fun_sum (fun τ _ => (hdiff _ _).const_mul _))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [deriv_fun_sum (fun τ _ => (hdiff _ _).const_mul _)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [deriv_const_mul _ (hdiff _ _)]
  rw [← hsum]
  have hfz : (fun z => ∑ σ : Equiv.Perm (blkA (n := n) j), ∑ τ : Equiv.Perm (blkB (n := n) j),
        (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card (blkA (n := n) j) + Fintype.card (blkB (n := n) j)) (fz m 0 z) x
          (Fin.append (fun i => LQ (blkA j) x (Matrix.single ((Fintype.equivFin (blkA (n := n) j)).symm i)
              (σ ((Fintype.equivFin (blkA (n := n) j)).symm i)) 1))
            (fun i => LR (blkB j) x (Matrix.single ((Fintype.equivFin (blkB (n := n) j)).symm i)
              (τ ((Fintype.equivFin (blkB (n := n) j)).symm i)) 1)))) =
      fun z => ((∏ i ∈ Finset.range j, ((i : ℂ) - z)) * (∏ i ∈ Finset.range (n - j), ((i : ℂ) - m - z))) *
        (fz m 0 z x * minorOn (blkA j) (wM x) * minorOn (blkB j) (wM x)⁻¹) := by
    funext z
    rw [← expand (fz m 0 z) (fz_slice_contDiffOn m z), djZ n m 0 j z x hj hx]
    ring
  rw [hfz]
  set A : ℂ → ℂ := fun z => (∏ i ∈ Finset.range j, ((i : ℂ) - z)) * (∏ i ∈ Finset.range (n - j), ((i : ℂ) - m - z))
    with hAdef
  have hA : DifferentiableAt ℂ A 0 := by
    simp only [hAdef]
    exact (DifferentiableAt.fun_finset_prod fun i _ => (differentiableAt_const _).sub differentiableAt_id).mul
      (DifferentiableAt.fun_finset_prod fun i _ => ((differentiableAt_const _).sub differentiableAt_id))
  have hA0 : A 0 = 0 := by
    simp only [hAdef]
    rw [Finset.prod_eq_zero (i := 0) (by simp; omega) (by simp), zero_mul]
  have hg : DifferentiableAt ℂ (fun z => fz m 0 z x * minorOn (blkA j) (wM x) * minorOn (blkB j) (wM x)⁻¹) 0 := by
    have h1 : DifferentiableAt ℂ (fun z : ℂ => ((u1 x).det * (ub1 x).det) ^ (-z)) 0 :=
      (differentiableAt_id.neg).const_cpow (Or.inl (Complex.slitPlane_ne_zero hx.2))
    simp only [fz]
    exact (((differentiableAt_const _).mul h1).mul_const _).mul_const _
  rw [deriv_fun_mul hA hg, hA0, zero_mul, add_zero]
  congr 1
  simp [fz, hF, f0]
end HSt
end Sw
end Rg
end PositivityTheory
end
end

section
noncomputable section

open MeasureTheory Matrix Filter Topology Set
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem Fd_analytic (m : ℕ) : AnalyticOnNhd ℂ (Fd (n := n) m) (DomZ n) := by
  have hU := (fzHol n m 0).2.2
  intro y hy
  have h1 : AnalyticAt ℂ (fun p : ℂ × M2 n => fderiv ℂ (fun p : ℂ × M2 n => fz m 0 p.1 p.2) p (1, 0)) (0, y) :=
    (ContinuousLinearMap.apply ℂ ℂ ((1 : ℂ), (0 : M2 n))).analyticAt _ |>.comp (hU.fderiv (0, y) ⟨Set.mem_univ _, hy⟩)
  have hl : AnalyticAt ℂ (fun w : M2 n => ((0 : ℂ), w)) y := analyticAt_const.prod analyticAt_id
  have h2 := h1.comp hl
  refine h2.congr ?_
  filter_upwards [isOpen_domZ.mem_nhds hy] with w hw
  exact (Fd_eq m hw).symm

theorem fdProps : FdProps := by
  intro n m
  refine ⟨(Fd_analytic m).contDiffOn_of_completeSpace, ?_⟩
  intro Kg _ _ _ _ _ _ μ _ ι hι hK ρ ψ a b x hρ hψ hψs ha hb hx
  have hιG : ∀ k, InG (ι k) := fun k => ((hK (ι k)).2 ⟨k, rfl⟩).1
  set y : Kg × (Fin n → Fin n → ℝ) → M2 n := fun p => x * ι p.1 * a * nU (herm p.2) * b with hydef
  have hherm : Continuous (herm (n := n)) := by unfold herm; fun_prop
  have hnU : Continuous fun t : Fin n → Fin n → ℝ => nU (herm t) := by
    unfold nU; exact Continuous.matrix_fromBlocks continuous_const hherm continuous_const continuous_const
  have hy : Continuous y :=
    (((continuous_const.mul (hι.comp continuous_fst)).mul continuous_const).mul (hnU.comp continuous_snd)).mul
      continuous_const
  have hyD : ∀ p, y p ∈ DomZ n := fun p =>
    gset_sub_domZ (inG_mul (inG_mul (inG_mul (inG_mul hx (hιG p.1)) ha) (inG_nU_herm p.2)) hb)
  set U : ℂ × M2 n → ℂ := fun q => fz m 0 q.1 q.2 with hUdef
  have hU : ContDiffOn ℂ ∞ U (Set.univ ×ˢ DomZ n) := fz_contDiffOn m
  have hO : IsOpen (Set.univ ×ˢ DomZ n : Set (ℂ × M2 n)) := isOpen_univ.prod isOpen_domZ
  set U' : ℂ × M2 n → ℂ := fun q => fderiv ℂ U q (1, 0) with hU'def
  have hU' : ContinuousOn U' (Set.univ ×ˢ DomZ n) :=
    ((hU.fderiv_of_isOpen (m := ∞) hO (by simp)).clm_apply contDiffOn_const).continuousOn
  set F : ℂ → Kg × (Fin n → Fin n → ℝ) → ℂ := fun z p => ρ p.1 * (U (z, y p) * ψ p.2) with hFdef
  set F' : ℂ → Kg × (Fin n → Fin n → ℝ) → ℂ := fun z p => ρ p.1 * (U' (z, y p) * ψ p.2) with hF'def
  set S : Set (Kg × (Fin n → Fin n → ℝ)) := Set.univ ×ˢ tsupport ψ with hSdef
  have hS : IsCompact S := isCompact_univ.prod hψs
  have hzero : ∀ p, p ∉ S → ψ p.2 = 0 := fun p hp =>
    image_eq_zero_of_notMem_tsupport (fun h => hp ⟨Set.mem_univ _, h⟩)
  have hFc : ∀ z, Continuous (F z) := fun z =>
    (hρ.comp continuous_fst).mul ((hU.continuousOn.comp_continuous (continuous_const.prodMk hy)
      (fun p => ⟨Set.mem_univ _, hyD p⟩)).mul (hψ.comp continuous_snd))
  have hF'c : Continuous fun q : ℂ × (Kg × (Fin n → Fin n → ℝ)) => F' q.1 q.2 :=
    (hρ.comp (continuous_fst.comp continuous_snd)).mul ((hU'.comp_continuous (continuous_fst.prodMk
      (hy.comp continuous_snd)) (fun q => ⟨Set.mem_univ _, hyD q.2⟩)).mul (hψ.comp (continuous_snd.comp continuous_snd)))
  have hsupp : ∀ (G : Kg × (Fin n → Fin n → ℝ) → ℂ), Continuous G → (∀ p, p ∉ S → G p = 0) →
      Integrable G (μ.prod volume) := by
    intro G hG h0
    refine hG.integrable_of_hasCompactSupport (IsCompact.of_isClosed_subset hS (isClosed_tsupport G) ?_)
    refine closure_minimal (fun p hp => ?_) (isClosed_univ.prod (isClosed_tsupport ψ))
    by_contra h; exact hp (h0 p h)
  have hFi : ∀ z, Integrable (F z) (μ.prod volume) := fun z =>
    hsupp _ (hFc z) (fun p hp => by simp [hFdef, hzero p hp])
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1 |>.prod hS).exists_bound_of_continuousOn hF'c.continuousOn
  have hbound_int : Integrable (S.indicator fun _ => C) (μ.prod volume) :=
    (integrable_indicator_iff (isClosed_univ.prod (isClosed_tsupport ψ)).measurableSet).2 (integrableOn_const hS.measure_lt_top.ne)
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.prod volume) (F := F) (F' := F')
    (x₀ := (0 : ℂ)) (s := Metric.ball 0 1) (bound := S.indicator fun _ => C) (Metric.ball_mem_nhds 0 one_pos)
    (Filter.Eventually.of_forall fun z => (hFc z).aestronglyMeasurable) (hFi 0)
    ((hF'c.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun p z hz => by
      by_cases hp : p ∈ S
      · rw [Set.indicator_of_mem hp]
        exact hC (z, p) ⟨Metric.ball_subset_closedBall hz, hp⟩
      · rw [Set.indicator_of_notMem hp]
        simp [hF'def, hzero p hp])
    hbound_int
    (Filter.Eventually.of_forall fun p z _ => by
      have hd : DifferentiableAt ℂ U (z, y p) :=
        (hU.contDiffAt (hO.mem_nhds ⟨Set.mem_univ _, hyD p⟩)).differentiableAt (by simp)
      have hl : HasDerivAt (fun z' : ℂ => (z', y p)) ((1 : ℂ), (0 : M2 n)) z :=
        (hasDerivAt_id z).prodMk (hasDerivAt_const z (y p))
      have h1 := hd.hasFDerivAt.comp_hasDerivAt z hl
      exact (h1.mul_const (ψ p.2)).const_mul (ρ p.1))
  have hT : ∀ (G : M2 n → ℂ), (Integrable (fun p : Kg × (Fin n → Fin n → ℝ) => ρ p.1 * (G (y p) * ψ p.2))
      (μ.prod volume)) → tOp μ ι ρ ψ a b G x = ∫ p, ρ p.1 * (G (y p) * ψ p.2) ∂(μ.prod volume) := by
    intro G hG
    rw [integral_prod _ hG]
    unfold tOp
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [hydef]
    exact (integral_const_mul _ _).symm
  have e1 : (fun z => tOp μ ι ρ ψ a b (fz m 0 z) x) = fun z => ∫ p, F z p ∂(μ.prod volume) := by
    funext z; exact hT (fz m 0 z) (hFi z)
  have e2 : ∫ p, F' 0 p ∂(μ.prod volume) = tOp μ ι ρ ψ a b (Fd m) x := by
    have hF'0 : F' 0 = fun p => ρ p.1 * (Fd m (y p) * ψ p.2) := by
      funext p; simp only [hF'def, hU'def, Fd_eq m (hyD p)]; rfl
    rw [hF'0, hT (Fd m) (hF'0 ▸ hderiv.1)]
  rw [e1, hderiv.2.deriv, e2]

end PositivityTheory.Rg.Sw.HSt
end
end

section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem ks_inv_eq {U : Matrix (Fin n) (Fin n) ℂ} (h : U * Uᴴ = 1) : U⁻¹ = Uᴴ := Matrix.inv_eq_right_inv h

theorem ks_trace_single (X : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) : (X * Matrix.single a b 1).trace = X b a := by
  rw [Matrix.trace_mul_single]
  simp

theorem ks_rhoP {Kg : Type} [Group Kg] (ι : Kg →* M2 n) (m : ℕ) (k k1 : Kg) (hk : InK (ι k))
    (N : Matrix (Fin n) (Fin n) ℂ) (hN : N ∈ unitaryGroup (Fin n) ℂ) (h1 : ι k1 = Proj.kM 1 N) :
    rhoP ι m 0 1 (k * k1) = fV (m : ℤ) 0 (ι k) * ((u1 (ι k))⁻¹ * u2 (ι k) * N).trace := by
  obtain ⟨kk, hkk, hmk⟩ := Proj.kM_of_unitary (1 : Matrix (Fin n) (Fin n) ℂ) N (one_mem _) hN
  have hu1 : u1 (ι (k * k1)) = u1 (ι k) := by
    rw [map_mul, h1, ← hmk, first_block_mul_compact (ι k) hkk, hmk, Proj.first_unitary_block_of_pair, Matrix.mul_one]
  have hu2 : u2 (ι (k * k1)) = u2 (ι k) * N := by
    rw [map_mul, h1, ← hmk, second_block_mul_compact (ι k) hkk, hmk, Proj.second_unitary_block_of_pair]
  have U1 : u1 (ι k) * (u1 (ι k))ᴴ = 1 := first_cayley_block_unitary hk
  have U2 : u2 (ι k) * (u2 (ι k))ᴴ = 1 := second_cayley_block_unitary hk
  have UN : N * Nᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hN
    rwa [Matrix.star_eq_conjTranspose] at this
  have hfz : fz m 0 0 (ι (k * k1)) = (u1 (ι k)).det ^ (-(m : ℤ)) := by
    simp only [fz, zpow_zero, one_mul, neg_zero, Complex.cpow_zero, mul_one, hu1]
  have hne : (u1 (ι k)).det ≠ 0 := det_first_cayley_block_ne_zero hk.1
  have hd : star (u1 (ι k)).det = ((u1 (ι k)).det)⁻¹ := by
    have := congrArg Matrix.det U1
    rw [det_mul, det_one, det_conjTranspose] at this
    exact eq_inv_of_mul_eq_one_right this
  have hfV : fV (m : ℤ) 0 (ι k) = star ((u1 (ι k)).det ^ (-(m : ℤ))) := by
    have h := scalar_section_mul_conjugate_section hk (m : ℤ) 0
    have hf0 : f0 (m : ℤ) 0 (ι k) = (u1 (ι k)).det ^ (-(m : ℤ)) := by simp [f0]
    rw [hf0] at h
    rw [star_zpow₀, hd, eq_inv_of_mul_eq_one_right h]
    rw [_root_.zpow_neg, _root_.zpow_neg, _root_.inv_zpow, inv_inv]
  have htr : star ((u2 (ι (k * k1)))⁻¹ * 1 * u1 (ι (k * k1))).trace = ((u1 (ι k))⁻¹ * u2 (ι k) * N).trace := by
    rw [hu1, hu2, Matrix.mul_one, Matrix.mul_inv_rev, ← Matrix.trace_conjTranspose, ks_inv_eq UN, ks_inv_eq U2,
      ks_inv_eq U1]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  unfold rhoP
  rw [star_mul', hfz, htr, hfV]

theorem ks_perm_unitary (a b : Fin n) : (Equiv.swap a b).permMatrix ℂ ∈ unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, conjTranspose_permMatrix,
    PEquiv.toMatrix_toPEquiv_mul]
  ext i j
  simp [PEquiv.toMatrix_apply, Matrix.one_apply]

theorem ks_diag_unitary (b : Fin n) :
    Matrix.diagonal (fun i => if i = b then (1 : ℂ) else -1) ∈ unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases h : i = b <;> simp [h]

theorem ks_single_eq (a b : Fin n) :
    Matrix.single a b (1 : ℂ) = (1 / 2 : ℂ) • (Equiv.swap a b).permMatrix ℂ +
      (1 / 2 : ℂ) • ((Equiv.swap a b).permMatrix ℂ * Matrix.diagonal (fun i => if i = b then (1 : ℂ) else -1)) := by
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.mul_diagonal, Matrix.single_apply]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
    smul_eq_mul]
  by_cases hj : j = b
  · subst hj
    by_cases hi : i = a
    · subst hi
      simp <;> norm_num
    · have : ¬ (Equiv.swap a j i = j) := by
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
        exact hi
      simp [this, Ne.symm hi]
  · simp only [hj, if_false]
    by_cases h : Equiv.swap a b i = j
    · simp only [h, if_true]
      have : ¬ (a = i ∧ b = j) := fun h' => hj h'.2.symm
      rw [if_neg this]
      ring
    · simp only [h, if_false]
      have : ¬ (a = i ∧ b = j) := fun h' => hj h'.2.symm
      rw [if_neg this]
      ring

theorem kSplit : KSplit := by
  intro n m a0 b0 Kg _ ι hK
  classical
  set Pm : Matrix (Fin n) (Fin n) ℂ := (Equiv.swap a0 b0).permMatrix ℂ with hPmdef
  set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun i => if i = b0 then (1 : ℂ) else -1) with hDdef
  have hPm : Pm ∈ unitaryGroup (Fin n) ℂ := ks_perm_unitary a0 b0
  have hD : D ∈ unitaryGroup (Fin n) ℂ := ks_diag_unitary b0
  set Nl : Fin 2 → Matrix (Fin n) (Fin n) ℂ := ![Pm, Pm * D] with hNldef
  have hNl : ∀ l, Nl l ∈ unitaryGroup (Fin n) ℂ := by
    intro l
    fin_cases l
    · exact hPm
    · exact mul_mem hPm hD
  have hex : ∀ l, ∃ k1 : Kg, ι k1 = Proj.kM 1 (Nl l) := fun l => by
    obtain ⟨kk, hkk, hmk⟩ := Proj.kM_of_unitary (1 : Matrix (Fin n) (Fin n) ℂ) (Nl l) (one_mem _) (hNl l)
    have : InK (Proj.kM 1 (Nl l)) := by rw [← hmk]; exact hkk
    exact (hK _).1 this
  choose kl hkl using hex
  refine ⟨2, fun _ => 1 / 2, kl, fun k => ?_⟩
  have hk : InK (ι k) := (hK _).2 ⟨k, rfl⟩
  rw [Fin.sum_univ_two, ks_rhoP ι m k (kl 0) hk _ (hNl 0) (hkl 0), ks_rhoP ι m k (kl 1) hk _ (hNl 1) (hkl 1)]
  rw [← ks_trace_single ((u1 (ι k))⁻¹ * u2 (ι k)) a0 b0, ks_single_eq a0 b0]
  simp only [hNldef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
  ring

end PositivityTheory.Rg.Sw.HSt
end
end

section
namespace PositivityTheory.Rg.Sw.HSt

theorem crux : Crux := eRed (vacuum_nonvanishing_of_facts fdProps djFd kSplit sphU fzHol)

end PositivityTheory.Rg.Sw.HSt
end
