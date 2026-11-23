module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDom
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFpmDecay
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopFormDone
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LimitOfModuleForms
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

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def flCutS (k r : ℕ) (n : ℕ) (g : B.Mat k r) : ℂ :=
  ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)

theorem domination_measurability_holds : NFDomMeas := by
  intro Cb
  obtain ⟨Cc, hFL⟩ := Formalism.FourierDecayAlt.P.limit_of_module_forms Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN ε hε
  obtain ⟨hχ, hInD, hfck, hfcc, hA, -⟩ := hH
  have hck : B.CkOn ⊤ (B.GV P.k P.r) (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) := by
    rw [fpm_id]; exact ckOn_Gpow_smul _ _ p₀ hfck
  obtain ⟨hcpt, hlim⟩ := hFL Wp Wq P p (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) χ ε
    (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ)) N (flCutS P.k P.r) hInD hχ hε hck (inCC_fpm_id p p₀ hfcc) hA
    (fun n g => rfl)
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n => topD p (fun g => flCutS P.k P.r n g •
      D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε g) w)
    (fun n => top_domination_measurable_compact Wp Wq P p _ w Cb hInD (hcpt n) hw.1) (ae_of_all _ fun c => ?_)
  have h := hlim (P.r + 1) w hw.1 hN (TBB.bigPt P.r c) (TBB.bigPt P.r c)
  unfold topD TBB.Ew TBB.NP
  exact (Complex.continuous_re.tendsto _).comp (h.const_mul _)


end

end Formalism.FourierDecayAlt.P.CutBP
