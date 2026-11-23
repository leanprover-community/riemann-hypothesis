module

public import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KummerNotFrac
public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.ExistsBeta
public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.ExistsCoeEqUntiltPFlat
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.TieQB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.LocalComparison.LocTied6
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT

@[expose] public section

noncomputable section

namespace period_ring_base

open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst Matrix

theorem base_κ_cont (l : ℕ) [Fact l.Prime] : Continuous (κ : GQ l → ℚ_[l]) := continuous_κ l

theorem base_no_kummer (l : ℕ) [Fact l.Prime] : ∀ L : Fld l, FiniteDimensional ℚ_[l] L → ∀ x : B l,
    ¬ ∀ σ ∈ L.fixingSubgroup, σB σ x - x = qB l (κ σ) * t l := by
  intro L hL x h
  obtain ⟨P, AI, ⟨T0⟩⟩ := GlobalTheory.MemLoc.exists_locPrime_tied l
  obtain ⟨T⟩ := UpperTheory.Lit.Cmp.locTied6 l P AI ⟨T0⟩
  obtain ⟨β, hβ⟩ := UpperTheory.Lit.Drps.exists_beta T
  have := GlobalTheory.Pst.nontrivial_B P
  apply GlobalTheory.Pst.StLat.kummer_not_frac l P AI T0 ⟨L, hL⟩ 1 (T.eB.symm (x + qB l β * t l)) one_ne_zero
  intro g hg
  apply T.eB.injective
  rw [map_one, one_mul, one_mul, one_mul, one_mul, map_sub, DualB.tie_σB T, RingEquiv.apply_symm_apply, hβ, map_add (f := _),
    ← h g hg]
  ring

end period_ring_base
