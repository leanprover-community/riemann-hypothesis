module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocMaxCentreCut
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpValuationCentre
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem BlowUpOverLocCentreDom.proof : BlowUpOverLocCentreDom.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have := hP.multiProj.isPrime
  intro 𝔫 h𝔫
  have hW : W.IsPrime := hWmin.1.1
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  obtain ⟨V, hBV, hnV⟩ := Ideal.image_subset_nonunits_valuationSubring 𝔫 h𝔫.ne_top
  obtain ⟨W', hp, hh, hr, hb, hc, hloc⟩ := exists_blowUp_centre (J := J) P W hP.multiProj.multiHomog hW hPW
    hWrel N u hu hu' V ((homLocRing_le_blowUpOverLoc P W u).trans hBV)
  have h : blowUpOverLoc P W u ≤ blowUpLocRing P u W' := iInf₂_le W' ⟨hp, hh, hr, hb, hc⟩
  refine ⟨W', hp, hh, hr, hb, hc, h, fun y hy hunit => ?_⟩
  obtain ⟨w, hw⟩ := hunit
  obtain ⟨hyV, hymax⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal (A := V)).1
    (hnV ⟨y, hy, rfl⟩)
  have hinv : ((w⁻¹ : (blowUpLocRing P u W')ˣ) : FractionRing (MRing ι O ⧸ P)) ∈ V := hloc ((w⁻¹ : (blowUpLocRing P u W')ˣ) : blowUpLocRing P u W').2
  have hmul : (y : FractionRing (MRing ι O ⧸ P)) * ((w⁻¹ : (blowUpLocRing P u W')ˣ) : _) = 1 := by
    have h1 := congrArg Subtype.val w.mul_inv
    rw [hw] at h1
    exact h1
  exact (IsLocalRing.mem_maximalIdeal _).1 hymax (IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext hmul))

end

end GroundTheory.Heights₂.Heights.NumbersDVR
