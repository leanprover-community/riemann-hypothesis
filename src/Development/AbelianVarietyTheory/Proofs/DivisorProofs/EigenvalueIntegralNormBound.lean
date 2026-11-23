module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorMapEigenvalueNormBound
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMemConj

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.eigenvalue_integral_norm_bound : ∀ (p : ℕ) [Fact p.Prime] (Kw : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ) (N : Matrix (Fin n) (Fin n) Kw) (H k : GL (Fin n) (KQ p Kw r)), k ∈ Kres p Kw n r → N.map (inclK p Kw r) = ((H * k * H⁻¹ : GL (Fin n) (KQ p Kw r)) : Matrix (Fin n) (Fin n) (KQ p Kw r)) → ∀ (v : Fin n → PadicAlgCl p) (c : PadicAlgCl p), v ≠ 0 → N.map (fun x => (x : PadicAlgCl p)) *ᵥ v = c • v → ‖c‖ ≤ 1 := by
  first | (exact @GlobalTheory.StabFin.norm_eigen_le_one_of_conj_Kres) | (exact GlobalTheory.StabFin.norm_eigen_le_one_of_conj_Kres) | (intros; apply GlobalTheory.StabFin.norm_eigen_le_one_of_conj_Kres  <;> assumption)
