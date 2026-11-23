module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RepresentationBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPowKillsLatticeCokernelStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KillsCokerAllOfKillsCokerPhiModuleLatticeStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

open PowerSeries GlobalTheory.BK

namespace GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow

theorem main : GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Stmt := by
  intro O K _ _ _ _ _ l e a _ _ _ _ hT ι κ _ _ _ _ Sig U N η H hB D₁ D₂ hD₁ hD₂ F hF
  haveI : FiniteDimensional ℚ_[l] K := hT.finite
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
  exact GlobalTheory.T.killsCoker_all_of_killsCoker_phiModuleLattice O K l e a ι κ η H D₁ D₂ F _
    (GlobalTheory.T.breuilKisin_pow_kills_lattice_cokernel O K l e a ι κ η H D₁ D₂ F Sig U N hB hD₁.chars_subset hD₂ hF)

end GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow
