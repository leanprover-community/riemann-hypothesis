module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsIntValuationLtOne
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreExtra
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerLast
public import GroundTheory.HeightsAndTheta.Heights.Intersections.FunFieldLeLocRing
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

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RegularityIntegral.proof (hC : RegularityValuationCentre.Statement) (hB : RegularityRelativeClosedPoint.Statement) :
    RegularityIntegral.Statement := by
  intro K _ ι _ P hP x
  obtain ⟨hF, hNF⟩ := RegularityFunctionFieldNumber.proof K ι P hP
  let _ := hF.toField
  have hv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers (funField P)),
      v.valuation (funField P) (x : funField P) ≤ 1 := by
    intro v
    obtain ⟨n, hn0, hn⟩ := RegularityValuationCentre.exists_int_valuation_lt_one v
    obtain ⟨W, hW, hPW, hnW, hsub⟩ := hC K ι P hP.2.1 _ (v.valuation (funField P)) n hn
    have hWP : W ≠ P := by
      rintro rfl
      have h0 : n ∈ W.comap (C : ℤ →+* MRing ι) := hnW
      rw [show W.comap (C : ℤ →+* MRing ι) = ⊥ from hP.2.2.1, Ideal.mem_bot] at h0
      exact hn0 h0
    exact hsub x (x.2 W (hB K ι P W hP hW hPW hWP) hPW)
  obtain ⟨y, hy⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (funField P)
    (x : funField P) hv
  have hint : IsIntegral ℤ (x : funField P) := hy ▸ (Algebra.IsIntegral.isIntegral y).algebraMap
  let f : funField P →ₐ[ℤ] FractionRing (MRing ι ⧸ P) :=
    { (funField P).subtype with commutes' := fun n => by simp }
  exact hint.map f

end

end GroundTheory.Heights₂.Heights.Inter
