module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHB2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtInt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.EntrywiseClassWordTransfer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem good_of_goodFam {E X S : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup X]
    [NormedSpace ℝ X] {Φ : X → S → V1 E} (h : CutHB.GoodFam Φ) (e : S) : Good (fun v => Φ v e) := by
  refine ⟨h.1 e, fun K hK hK0 => ?_⟩
  obtain ⟨C, hC, hz⟩ := h.2 K hK hK0
  exact ⟨C, hC, fun v hv τ hτ => hz v hv τ hτ e⟩

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.SliceIntegralLemmas

theorem one_variable_letters_under_integral : CutHB.OneBTInt := by
  intro E _ _ _ X _ _ _ _ _ μ _ ℓ hℓ S _ _ κ w Φ hΦ f hf t ht e
  exact (oneBT_int (μ := μ) hℓ κ w Φ f (good_of_goodFam hΦ) (fun b τ hτ => hf b τ hτ) e).2 t ht

end Formalism.FourierDecayAlt.P
