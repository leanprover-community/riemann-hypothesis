module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BasicOperatorsPolynomialLiftNoInversePowerStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopDensityDominated
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF

theorem topDensity_cut_dominated_all :
    GlobalTheory.HCXi.BesselXiIntegrable → Formalism.FourierDecayAlt.P.CutBP.NFTopDomAll := by
  intro hΞ Cb
  obtain ⟨Cc, H⟩ := GlobalTheory.HatNF.top_density_dominated hΞ (fun _ => 0) GlobalTheory.T.basicOperators_polynomialLift_no_inversePower Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hH
  obtain ⟨hm, h, hi, hb⟩ := H Wp Wq P p f A₀ p₀ χ N w a1 a2 a3 a4 a5 (by simpa using a6) hw.1 hN
  have e : ∀ ε : ℝ,
      D.cutF p.T.base χ (Formalism.FourierDecayAlt.P.TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε =
      mulG p.T.base (fun y => χ (y / ε) * y ^ p₀) f := by
    intro ε
    funext g
    simp only [D.cutF, Formalism.FourierDecayAlt.P.TBBx4.fpm, mulG, ContinuousLinearMap.comp_id, smul_smul]
    try push_cast
    try rfl
  refine ⟨eventually_nhdsWithin_of_forall fun ε hε => ?_, h, hi,
    eventually_nhdsWithin_of_forall fun ε hε => ae_of_all _ fun c => ?_⟩
  · rw [e]; exact hm ε hε
  · rw [e]; exact hb ε hε c
end GlobalTheory.HatNF
