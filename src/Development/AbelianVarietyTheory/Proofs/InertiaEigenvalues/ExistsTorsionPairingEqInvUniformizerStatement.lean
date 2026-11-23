module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTorsionPairingEqInvUniformizer
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

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

theorem _root_.GlobalTheory.T.exists_torsion_pairing_eq_inv_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT'), ∀ ϖ : O, Irreducible ϖ → ∀ (n : ℕ) (f : ↥D.T'), f ∉ powSub (M := ↥D.T') ϖ n → ∃ x : VT ⧸ D.T, ϖ ^ n • x = 0 ∧ pairKO D.bT D.T x f = toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) := by
  first | exact @GlobalTheory.LocDualInt.exists_pairKO_eq_inv_unif | exact GlobalTheory.LocDualInt.exists_pairKO_eq_inv_unif | (intros; apply GlobalTheory.LocDualInt.exists_pairKO_eq_inv_unif <;> assumption)
