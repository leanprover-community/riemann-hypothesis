module

public import Formalism.HermitianCurvature.StatementJF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothnessOnGoodSet
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxDs1

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jConv_of_jDom : Formalism.FourierDecayAlt.JF.JDom → Formalism.FourierDecayAlt.JF.JConv := by
  intro hD k r Wp Wq _ _ _ _ _ _ D A F hT hC
  obtain ⟨hmeas, hbd⟩ := hD k r Wp Wq D A 0 F hT hC
  have hx : Continuous (fun p : SS k r => xiP D p) := by
    clear hmeas hbd hD hT hC
    unfold xiP psi ell
    refine Continuous.mul ?_ (Continuous.star ?_)
    · refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        (Complex.continuous_re.comp (continuous_const.mul (continuous_finsetSum _ fun a _ => ?_)))))
      split_ifs
      · simp only [Matrix.of_apply]; fun_prop
      · simp only [Matrix.of_apply, Matrix.mulVec, dotProduct]; fun_prop
    · refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        (Complex.continuous_re.comp (continuous_const.mul (continuous_finsetSum _ fun a _ => ?_)))))
      split_ifs
      · simp only [Matrix.of_apply]; fun_prop
      · simp only [Matrix.of_apply, Matrix.mulVec, dotProduct]; fun_prop
  have h0 : (0 : ℕ) + 0 ≤ 0 := le_rfl
  refine ⟨?_, ?_⟩
  · intro g hg
    obtain ⟨b, hb, hbb⟩ := hbd {g} isCompact_singleton (Set.singleton_subset_iff.mpr hg)
    have hbg := hbb [] [] (by simp) (by simp) h0 g (Set.mem_singleton g)
    have hm := hmeas [] [] (by simp) (by simp) h0 g hg
    refine Integrable.mono' hb (hx.aestronglyMeasurable.smul hm) ?_
    filter_upwards [hbg] with p hp
    calc ‖xiP D p • rho D p F g‖ = ‖xiP D p‖ * ‖rho D p F g‖ := norm_smul _ _
      _ ≤ 1 * ‖rho D p F g‖ := by gcongr; exact SmoothnessOnGoodSet.norm_xiP D p
      _ = ‖rho D p (dLR (List.map (AdL p) []) (List.map (AdR p) []) F) g‖ := by rw [one_mul]; rfl
      _ ≤ b p := hp
  · intro K hK hKO
    obtain ⟨b, hb, hbb⟩ := hbd K hK hKO
    exact ⟨b, hb, fun g hg => hbb [] [] (by simp) (by simp) h0 g hg⟩

end Formalism.FourierDecayAlt.P.JFxDs1
