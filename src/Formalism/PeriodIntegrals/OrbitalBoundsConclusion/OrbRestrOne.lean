module

public import Formalism.PeriodIntegrals.OrbRestrOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitRestrictionDegreeOne.RestrictedSingleJetEquation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitRestrictionDegreeOne.Lemmas

@[expose] public section

theorem PI.OrbRestrOne : ∀ (D : Formalism.BasicNotions.D7) (E : PI.OrbJet.Ent D), PI.OrbJet.OrbitRestrictionAtConjugate E := by
  intro D E p _ h5 hn u i Th hTh z
  obtain ⟨ep0, hep0, be, hbe, ep, hep, sg, hsg, U, hU, hEq⟩ := hTh
  have hc : ∀ w, MvPowerSeries.constantCoeff (be w) = 0 := fun w =>
    PI.OrbJet.constantCoeff_zero_of_jet_bound p 2 (be w) (hbe w).2.2.1
  have key := PI.OrbJet.restricted_single_jet_equation (D := D) p hn z Th U ep0 be hc ep sg hEq
  dsimp only [PI.OrbJet.oneLoc, PI.OrbJet.OJ.Loc1.AdmB, PI.OrbJet.OJ.Loc1.B0, PI.OrbJet.OJ.Loc1.Tht]
  refine ⟨ep0, hep0, be z, ⟨ep z, hep z, sg z, hsg z, _, ?_, key⟩,
    (hbe z).1, (hbe z).2.1, (hbe z).2.2.1, (hbe z).2.2.2⟩
  intro m
  rw [MvPowerSeries.coeff_killCompl]
  exact hU _
