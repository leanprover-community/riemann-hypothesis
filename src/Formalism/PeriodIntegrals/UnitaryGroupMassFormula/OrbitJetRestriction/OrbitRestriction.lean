module

public import Formalism.PeriodIntegrals.OrbRestr
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetRestriction.ConstantCoeffZeroOfVanishing
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetRestriction.RestrictedJetEquation
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Classical

namespace PI.OrbJet.OrbW

open Formalism.BasicNotions Formalism.MainNotions.G MvPowerSeries Finsupp PI.OrbJet PI.OrbShared

theorem orbitRestriction : ∀ (D : Formalism.BasicNotions.D7) (E : PI.OrbJet.Ent D), PI.OrbJet.OrbitRestriction E := by
  intro D E
  unfold PI.OrbJet.OrbitRestriction
  intro p _ h u i R hR ep sg be hbe Th hB r hr
  obtain ⟨U, hU, hEq⟩ := hB
  obtain ⟨-, -, hb⟩ := hbe
  haveI : NeZero (nP D p) := ⟨omega⟩

  have hcc : ∀ r ∈ R, MvPowerSeries.constantCoeff (be r) = 0 := fun r hr =>
    constant_coeff_zero_of_vanishing_alt p (nP D p) (be r) (hb r hr).2.2.1
  have key := restricted_jet_equation D p R hR ep sg be hcc Th U hEq hr
  unfold PI.OrbJet.OrbitThetaExpansion
  refine ⟨_, ?_, key⟩
  intro m
  change (ZMod (nP D p) × Fin (D.R.N i) × Fin (D.R.N (i + 1)) →₀ ℕ) at m
  change ‖MvPowerSeries.coeff m (killCompl (orbEmb D p r (Fin (D.R.N i) × Fin (D.R.N (i + 1)))) U)‖ ≤ 1
  rw [MvPowerSeries.coeff_killCompl]
  exact hU _

end PI.OrbJet.OrbW
