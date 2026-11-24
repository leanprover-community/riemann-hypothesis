module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Formalism.SharpRestriction.DesignExistsOfChoices
public import Formalism.SharpRestriction.SmoothDesignExistence.DesignExistsDes
public import Formalism.SharpRestriction.MuTuOfTuSize
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PageDutiesOfClassSeven
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk GlobalTheory.EX GlobalTheory.Fc

namespace GlobalTheory.Fc

theorem tameDistinctF_iff {eps : ℝ} (Fm : FamP eps) : DC.TameDistinctF Fm ↔ Formalism.MainNotions.TameDistinctF Fm := by
  unfold DC.TameDistinctF Formalism.MainNotions.TameDistinctF
  simp only [DQ.tameDistinct_iff]

theorem dGamDvdF_iff {eps : ℝ} (Fm : FamP eps) : DC.DGamDvdF Fm ↔ Formalism.MainNotions.DGamDvdF Fm := Iff.rfl

theorem codeUpF_iff {eps : ℝ} (Fm : FamP eps) (C0 CH : ℝ) : DC.CodeUpF Fm C0 CH ↔ Formalism.MainNotions.CodeUpF Fm C0 CH := Iff.rfl

theorem working_classes_frozen : (∀ (𝒜 : FamClass) (eps : ℝ) (Fm : FamP eps), (Formalism.MainNotions.WithTw (Formalism.MainNotions.WithSm (fun Fm => 𝒜 Fm ∧ Formalism.MainNotions.DGamDvdF Fm ∧ Formalism.MainNotions.TameDistinctF Fm ∧ Formalism.MainNotions.BoxesF Fm ∧ Formalism.MainNotions.QDRowsF Fm ∧ Fm.CYL ≤ 9)) Fm ↔ W1 𝒜 Fm) ∧ (Formalism.MainNotions.Des (fun Fm => 𝒜 Fm ∧ Formalism.MainNotions.DGamDvdF Fm ∧ Formalism.MainNotions.TameDistinctF Fm ∧ Formalism.MainNotions.BoxesF Fm ∧ Formalism.MainNotions.QDRowsF Fm ∧ Fm.CYL ≤ 9) 3 Fm ↔ W3 𝒜 Fm)) ∧ (∀ (𝒜 : FamClass) (cT : ℝ → ℝ → ℝ), (DC.MinkDiv → DC.DesignChoices (DC.WithTw 𝒜) 3 cT) → Formalism.MainNotions.MinkDiv → Formalism.MainNotions.DesignChoices (Formalism.MainNotions.WithTw 𝒜) 3 cT) := by
  refine ⟨fun 𝒜 eps Fm => ?_, fun 𝒜 cT h hM => ?_⟩
  · have e1 : Formalism.MainNotions.WithTw (Formalism.MainNotions.WithSm (fun Fm => 𝒜 Fm ∧ Formalism.MainNotions.DGamDvdF Fm ∧ Formalism.MainNotions.TameDistinctF Fm ∧ Formalism.MainNotions.BoxesF Fm ∧
        Formalism.MainNotions.QDRowsF Fm ∧ Fm.CYL ≤ 9)) Fm ↔ W1 𝒜 Fm := by
      simp only [Formalism.MainNotions.WithTw, Formalism.MainNotions.WithSm, W1, tameDistinctF_iff, dGamDvdF_iff]
    refine ⟨e1, ?_⟩
    simp only [Formalism.MainNotions.Des, W3, ← e1]
  · obtain ⟨ε0, h0, h⟩ := h hM
    refine ⟨ε0, h0, fun eps he hle K => ?_⟩
    obtain ⟨Fm, CH, C5, Cb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h eps he hle K
    exact ⟨Fm, CH, C5, Cb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, (tameDistinctF_iff Fm).1 h15, h16,
      (codeUpF_iff Fm 3 CH).1 h17, h18⟩

end GlobalTheory.Fc
