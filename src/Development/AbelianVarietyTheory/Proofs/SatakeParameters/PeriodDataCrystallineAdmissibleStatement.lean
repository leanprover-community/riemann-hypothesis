module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.RepresentationTheory.Invariants
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDataCrystallineAdmissible
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Module

theorem _root_.GlobalTheory.T.period_data_crystalline_admissible : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [IsFractionRing O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V} [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] (L : Lattice (O := O) ρ), Module.Finite LL (FiniteCohomology PD ρ) → ∀ n : ℕ, Module.length O (↥(latticeFiniteCocycles PD L) ⧸ ((latticeFiniteCocycles PD L).map ((((PD.p : ℕ) : O) ^ n) • (LinearMap.id : (G → V) →ₗ[O] (G → V))) ⊔ latticeCoboundaries L).comap (latticeFiniteCocycles PD L).subtype) ≤ (n : ℕ∞) * (finrank LL (FiniteCohomology PD ρ) : ℕ∞) * lenOl PD (O := O) + Module.length O ↥(Representation.invariants (repD L)) := by
  first | exact @GlobalTheory.length_H1fT_modPow_le | exact GlobalTheory.length_H1fT_modPow_le | (intros; apply GlobalTheory.length_H1fT_modPow_le <;> assumption)
