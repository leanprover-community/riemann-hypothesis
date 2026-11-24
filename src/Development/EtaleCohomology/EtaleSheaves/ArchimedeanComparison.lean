module

public import Development.EtaleCohomology.EtaleSheaves.SHExistsPf
public import Development.EtaleCohomology.EtaleSheaves.EtStagePf
public import Development.EtaleCohomology.EtaleSheaves.EtaleSpreading.FPProof
public import Development.EtaleCohomology.EtaleSheaves.FPColimPf
public import Development.EtaleCohomology.EtaleSheaves.UnderFAOf
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
public import Development.EtaleCohomology.EtaleSheaves.IECompPf

@[expose] public section

theorem LateralTheory.E.TruncationIsoComparison.IEComp_of : LateralTheory.E.t_E3Cut.IEComp :=
  LateralTheory.E.IECompPf.IEComp_of (LateralTheory.E.UnderFAPf.UnderFA_of LateralTheory.E.FPColimPf.FPColim_of)
    (LateralTheory.E.SpreadPf.Cut.EtSpreads_of LateralTheory.E.SpreadPf.FPProof.finite_presentation_ring_maps_pre_ind_spread LateralTheory.E.EtStagePf.EtStage_of)
theorem LateralTheory.E.TruncationIsoComparison.Comp_of : LateralTheory.E.SHExistsPf.Comp := @LateralTheory.E.TruncationIsoComparison.IEComp_of
