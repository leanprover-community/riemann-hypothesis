module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.DegreeHermitianFormula
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfChiOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfLevInv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfPtInv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullRetrFacts
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairDefs

@[expose] public section

open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.ptRetr :
    PtRetr := by
  intro E _ _ _ a ha U hU Ξ r χ G n e hD q α β hα hβ g
  have hv := Pf.levInv E a ha U hU Ξ r χ hD.one hD.tw
  obtain ⟨t, ht⟩ := (retrFacts E a).1 g
  obtain ⟨s, hs⟩ := hD.tw.1
  have h1 := Pf.chiOne E a χ s hs (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g)
  rw [Pf.ptIp_eq]
  refine Finset.sum_congr rfl fun I _ => ?_
  have hc := ((Pf.ptInv E a χ _ G _ _).2.1 (hv q α hα fun i => e (I i)) (hv q β hβ fun i => e (I i))).centre t g
  rw [← hc, ← ht, Pf.pt, h1]
  simp
