module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.ContinuousTo
public import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.HasFDerivAtOfCurves
public import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.HasFDerivAtOrb
public import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.MapOfRealMul
public import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.MetaplecticGroupT2Space
public import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.MetaplecticUnipotentBlockSecondDiag
import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.MpFOne
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.ContinuousOm

@[expose] public section

open CompanionTheory.ThKR.Mp in
theorem CompanionTheory.ThKR.realMetaplecticRepresentation_holds : GlobalTheory.Published.RealMetaplecticRepresentation :=
  realMetaplectic_of_forall fun l _ _ _ =>
    have hS : SecEx l := secEx_of mkElt nrmUp
    have hO : Surj l := surj_of ddNe hS
    have hN : NearOne l := nearOne_of hS ker secDer
    have hC : Cover l := cover_of topG hO ker hS secDer
    ⟨topG, hC, hO, ker, smooth_of topG hN secDer, onePar_of topG hC hN secDer⟩
