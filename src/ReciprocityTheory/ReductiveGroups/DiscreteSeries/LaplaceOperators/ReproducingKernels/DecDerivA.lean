module

import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamLeOfKTypes
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.EquivariantL2Space
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaF

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ContDiff

namespace ReciprocityTheory.ChartRestriction.DS.Lap.S0.DecDerivA

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem cdom_antisymm {ε : Fin n → Bool} {μ Λ : Fin n → ℝ} (h₁ : Formalism.MainNotions.S.CDom ε μ Λ)
    (h₂ : Formalism.MainNotions.S.CDom ε Λ μ) : μ = Λ := by
  apply Formalism.MainNotions.BridgeLemma.cdom_antisymm <;> assumption

theorem stdGap_of {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} (hlam : S7.IsHCParam lam)
    (hgap : GapAtLeast ε lam h) (hN : hNeed ε < h) : StdGap ε lam := by
  refine ⟨hlam.1, h, hgap, ?_⟩
  have h1 : 2 + max (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ)) ≤ hNeed ε := le_max_left _ _
  have h2 : 1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) ≤ max (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ)) :=
    le_max_right _ _
  linarith

theorem eight_lt_of {ε : Fin n → Bool} {h : ℝ} (hN : hNeed ε < h) : 8 * (n : ℝ) * S7.q0 ε < h := by
  have h1 : 16 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) + 8 * Real.sqrt (2 * (min (pOf ε) (qOf ε) : ℝ)) + 2 ≤ hNeed ε :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hq : ((S7.q0 ε : ℕ) : ℝ) = (min (pOf ε) (qOf ε) : ℝ) := by
    simp [S7.q0, Nat.cast_min]
  rw [hq]
  have : 0 ≤ (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) := by positivity
  have : 0 ≤ Real.sqrt (2 * (min (pOf ε) (qOf ε) : ℝ)) := Real.sqrt_nonneg _
  nlinarith

lemma inUJ_mul {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) :
    a * b ∈ UJset ε := by
  have ha' : aᴴ * Jm ε * a = Jm ε := ha
  have hb' : bᴴ * Jm ε * b = Jm ε := hb
  show (a * b)ᴴ * Jm ε * (a * b) = Jm ε
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [ha', hb']

lemma umat_mem {ε : Fin n → Bool} (y : Formalism.REAL.UJ ε) : Formalism.MainNotions.S.umat y ∈ UJset ε := y.2

section Repro

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

lemma coefficient_mem_lowest_K_submodule (hP : IsPsiFor ε lam T Ψ) (v₀ v : T.V) :
    (⟨uniformisationL2 ε Ψ v₀ v, datumEmbedding_mem_Hlam hP v⟩ : Hlam ε Ψ v₀) ∈ lowKSubLam ε Ψ v₀ := by
  show _ ∈ Submodule.comap _ _
  rw [Submodule.mem_comap, Submodule.mem_map]
  exact ⟨⟨uniformisationL2 ε Ψ v₀ v, datumEmbedding_mem_smooth hP v₀ v⟩, Submodule.mem_comap.2 (Submodule.subset_span ⟨v, rfl⟩), rfl⟩

lemma exists_smooth_convolution_fixing_lowest (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) {v₀ : T.V} (hv₀ : v₀ ≠ 0) :
    ∃ α : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ∞ α ∧ HasCompactSupport α ∧
      ∀ w ∈ lowKSubLam ε Ψ v₀, opConv ε (sigLam ε Ψ v₀) α w = w := by
  have hlow := sigLam_lowK hgap hP hv₀
  have hW := hlow.1
  have hfull : ∀ (μ' : Fin n → ℝ) (S : Submodule ℂ (Hlam ε Ψ v₀)),
      Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ v₀) μ' S →
        (∃ S' ≤ lowKSubLam ε Ψ v₀, Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ v₀) μ' S') → S ≤ lowKSubLam ε Ψ v₀ := by
    intro μ' S hS ⟨S', hS'W, hS'⟩
    have hne : S' ≠ ⊥ := by
      obtain ⟨v, hv, hv0, -⟩ := hS'.2.2.2.1
      intro hb
      rw [hb] at hv
      exact hv0 ((Submodule.mem_bot ℂ).1 hv)
    have hS'eq : S' = lowKSubLam ε Ψ v₀ := (hW.2.2.1 S' hS'W hS'.2.1).resolve_left hne
    obtain ⟨u, hu, hu0, huw⟩ := hW.2.2.2.1
    obtain ⟨v, hv, hv0, hvw⟩ := hS'.2.2.2.1
    have c1 := hS'.2.2.2.2 _ u (by rw [hS'eq]; exact hu) hu0 huw
    have c2 := hW.2.2.2.2 _ v (by rw [← hS'eq]; exact hv) hv0 hvw
    have hμ : μ' = Formalism.QuantumDeterminants.lowK ε lam := cdom_antisymm c2 c1
    subst hμ
    exact (hlow.2 S hS).le
  have hsum : lowKSubLam ε Ψ v₀ ≤
      sSup {S : Submodule ℂ (Hlam ε Ψ v₀) | ∃ μ', Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ v₀) μ' S} :=
    le_sSup ⟨_, hW⟩
  obtain ⟨α, h1, h2, -, -, h5⟩ := sigLam_le_of_kTypes hgap hP hv₀ (lowKSubLam ε Ψ v₀) hW.1 hfull hsum Set.univ
    isOpen_univ (Set.mem_univ _)
  exact ⟨α, h1, h2, h5⟩

theorem repro_real (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) :
    ∃ α : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ∞ α ∧ HasCompactSupport α ∧
      ∀ g ∈ UJset ε, ∀ v₁ v₂ : T.V, ⟪v₂, Ψ g v₁⟫_ℂ =
        ∫ y : Formalism.REAL.UJ ε, α (Formalism.MainNotions.S.umat y) * ⟪v₂, Ψ (g * Formalism.MainNotions.S.umat y) v₁⟫_ℂ ∂(Formalism.REAL.muG ε) := by
  have hv₀ : T.w ≠ 0 := fun h0 => by simpa [h0] using T.w_norm
  obtain ⟨α, hα1, hα2, hα⟩ := exists_smooth_convolution_fixing_lowest hgap hP hv₀
  refine ⟨α, hα1, hα2, fun g hg v₁ v₂ => ?_⟩
  have hc : ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have := datumEmbedding_highest_ne_zero hgap hP hv₀
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.2 this)
  have hF : ∀ x ∈ UJset ε, ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * ⟪v₂, Ψ x v₁⟫_ℂ =
      ⟪(⟨uniformisationL2 ε Ψ T.w v₂, datumEmbedding_mem_Hlam hP v₂⟩ : Hlam ε Ψ T.w),
        sigLam ε Ψ T.w x ⟨uniformisationL2 ε Ψ T.w v₁, datumEmbedding_mem_Hlam hP v₁⟩⟫_ℂ := fun x hx =>
    (formulaF_sigLam hgap hP hv₀ hx v₁ v₂).symm
  have hU := sigLam_isURepOn hgap hP hv₀
  have hfix := hα _ (coefficient_mem_lowest_K_submodule hP T.w v₁)
  have key : ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * ⟪v₂, Ψ g v₁⟫_ℂ =
      ∫ y : Formalism.REAL.UJ ε, α (Formalism.MainNotions.S.umat y) *
        (((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * ⟪v₂, Ψ (g * Formalism.MainNotions.S.umat y) v₁⟫_ℂ) ∂(Formalism.REAL.muG ε) := by
    by_cases hint : Integrable (fun y : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat y) •
        sigLam ε Ψ T.w (Formalism.MainNotions.S.umat y) ⟨uniformisationL2 ε Ψ T.w v₁, datumEmbedding_mem_Hlam hP v₁⟩) (Formalism.REAL.muG ε)
    · rw [hF g hg, ← hfix]
      let Lc : Hlam ε Ψ T.w →L[ℂ] ℂ :=
        (innerSL ℂ (⟨uniformisationL2 ε Ψ T.w v₂, datumEmbedding_mem_Hlam hP v₂⟩ : Hlam ε Ψ T.w)).comp (sigLam ε Ψ T.w g)
      have e1 : ⟪(⟨uniformisationL2 ε Ψ T.w v₂, datumEmbedding_mem_Hlam hP v₂⟩ : Hlam ε Ψ T.w),
          sigLam ε Ψ T.w g (opConv ε (sigLam ε Ψ T.w) α ⟨uniformisationL2 ε Ψ T.w v₁, datumEmbedding_mem_Hlam hP v₁⟩)⟫_ℂ =
          Lc (opConv ε (sigLam ε Ψ T.w) α ⟨uniformisationL2 ε Ψ T.w v₁, datumEmbedding_mem_Hlam hP v₁⟩) := rfl
      rw [e1, opConv]
      refine Eq.trans (Lc.integral_comp_comm hint).symm ?_
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      show ⟪(⟨uniformisationL2 ε Ψ T.w v₂, datumEmbedding_mem_Hlam hP v₂⟩ : Hlam ε Ψ T.w), sigLam ε Ψ T.w g
        (α (Formalism.MainNotions.S.umat y) • sigLam ε Ψ T.w (Formalism.MainNotions.S.umat y) ⟨uniformisationL2 ε Ψ T.w v₁, datumEmbedding_mem_Hlam hP v₁⟩)⟫_ℂ = _
      dsimp only
      rw [map_smul, inner_smul_right, hF _ (inUJ_mul hg (umat_mem y)), hU.1.2 g hg _ (umat_mem y),
        ContinuousLinearMap.comp_apply]
    · have h0 : (⟨uniformisationL2 ε Ψ T.w v₁, datumEmbedding_mem_Hlam hP v₁⟩ : Hlam ε Ψ T.w) = 0 := by
        rw [← hfix, opConv]
        exact integral_undef hint
      have hz : ∀ x ∈ UJset ε, ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * ⟪v₂, Ψ x v₁⟫_ℂ = 0 := fun x hx => by
        rw [hF x hx, h0, map_zero, inner_zero_right]
      rw [hz g hg]
      symm
      refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [Pi.zero_apply]
      rw [hz _ (inUJ_mul hg (umat_mem y)), mul_zero]
  have e2 : ∫ y : Formalism.REAL.UJ ε, α (Formalism.MainNotions.S.umat y) *
        (((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * ⟪v₂, Ψ (g * Formalism.MainNotions.S.umat y) v₁⟫_ℂ) ∂(Formalism.REAL.muG ε) =
      ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) *
        ∫ y : Formalism.REAL.UJ ε, α (Formalism.MainNotions.S.umat y) * ⟪v₂, Ψ (g * Formalism.MainNotions.S.umat y) v₁⟫_ℂ ∂(Formalism.REAL.muG ε) := by
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  rw [e2] at key
  exact mul_left_cancel₀ hc key

theorem integral_transfer (ε : Fin n → Bool) (ν : Measure (S7.UJ ε)) [ν.IsHaarMeasure] :
    ∃ c : ℝ, ∀ Φ : Matrix (Fin n) (Fin n) ℂ → ℂ,
      ∫ y : Formalism.REAL.UJ ε, Φ (Formalism.MainNotions.S.umat y) ∂(Formalism.REAL.muG ε) = (c : ℂ) * ∫ y, Φ (S7.toM y) ∂ν := by
  suffices H : ∀ (H : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ), H = S7.UJ ε → ∀ (m : MeasurableSpace H),
      @BorelSpace H _ m → ∀ (μH : Measure H), μH.IsHaarMeasure → ∃ c : ℝ, ∀ Φ : Matrix (Fin n) (Fin n) ℂ → ℂ,
        ∫ y, Φ ((y : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∂μH =
          (c : ℂ) * ∫ y, Φ (S7.toM y) ∂ν by
    exact H _ (Subgroup.ext fun _ => Iff.rfl) _ inferInstance (Formalism.REAL.muG ε) (Formalism.REAL.instIsHaarMuG n ε)
  rintro H rfl m hb μH hμH
  obtain rfl : m = borel _ := hb.measurable_eq
  refine ⟨(Measure.haarScalarFactor μH ν : ℝ), fun Φ => ?_⟩
  have e := Measure.isMulLeftInvariant_eq_smul μH ν
  conv_lhs => rw [e]
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem reproducing_smooth_compact_kernel (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (ν : Measure (S7.UJ ε)) [ν.IsHaarMeasure] :
    ∃ β : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧
      ∀ g ∈ UJset ε, ∀ v₁ v₂ : T.V, ⟪v₂, Ψ g v₁⟫_ℂ = ∫ y, β (S7.toM y) * ⟪v₂, Ψ (g * S7.toM y) v₁⟫_ℂ ∂ν := by
  obtain ⟨α, hα1, hα2, hα⟩ := repro_real hgap hP
  obtain ⟨c, hc⟩ := integral_transfer ε ν
  refine ⟨fun x => (c : ℂ) * α x, contDiff_const.mul hα1, hα2.mul_left, fun g hg v₁ v₂ => ?_⟩
  have h1 := hc (fun x => α x * ⟪v₂, Ψ (g * x) v₁⟫_ℂ)
  rw [hα g hg v₁ v₂, h1, ← integral_const_mul]
  congr 1
  funext y
  ring

end Repro

end ReciprocityTheory.ChartRestriction.DS.Lap.S0.DecDerivA
