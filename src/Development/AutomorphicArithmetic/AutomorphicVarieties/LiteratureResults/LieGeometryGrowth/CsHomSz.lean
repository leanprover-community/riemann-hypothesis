module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsHkSz
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsIntSz
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullHkSmooth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.homSz :
    HomSz := by
  intro V F _ _ _ _ _ _ q k c
  obtain ⟨C, hC, h⟩ := hkSz V F q k c
  refine ⟨C, hC, fun Y W w b hY hW hw p hp hc hb => ?_⟩
  obtain ⟨ho, hs, -, -⟩ := UpperTheory.V.Lit.Geo.hkSmooth V F Y hY W hW q w hw
  haveI : CompleteSpace F := FiniteDimensional.complete ℝ F
  refine intSz V (V [⋀^Fin q]→L[ℝ] F) k p _ (fun z : V × ℝ => UpperTheory.V.Lit.Geo.hk W z.2 w z.1) (C * b) ho
    (fun t ht => ⟨hp, hW.2 p hp t ht⟩) hs fun t ht => ?_
  exact h W t w p b (abs_le.2 ⟨by linarith [ht.1], ht.2⟩) (hW.1.contDiffAt (hY.mem_nhds hp)) hc
    (hw.contDiffAt (hY.mem_nhds (hW.2 p hp t ht))) (hb t ht)
