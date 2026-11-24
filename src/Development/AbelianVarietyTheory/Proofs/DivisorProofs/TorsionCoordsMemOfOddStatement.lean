module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCoordsMemOfOdd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.torsion_weierstrass_coords_mem_of_intV : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → Odd N → ∀ (hu : u ≠ 0) (r s t : ℂ), IntV V ((⟨Units.mk0 u hu, r, s, t⟩ : VariableChange ℂ) • latticeCurve L) → ∀ z, z ∉ L.lattice → (N : ℂ) * z ∈ L.lattice → (L.weierstrassP z - r) / u ^ 2 ∈ V ∧ (L.derivWeierstrassP z / 2 - t - s * (L.weierstrassP z - r)) / u ^ 3 ∈ V := by
  first | exact @GlobalTheory.CMModel.torsion_coords_mem_of_odd | exact GlobalTheory.CMModel.torsion_coords_mem_of_odd | (intros; apply GlobalTheory.CMModel.torsion_coords_mem_of_odd <;> assumption)
