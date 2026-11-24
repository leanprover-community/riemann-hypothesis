module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousCocycleLiftOfCompatible
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

theorem _root_.GlobalTheory.T.exists_continuous_cocycle_lift_of_compatible' : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [T2Space M] [CompactSpace M] (ρ : Representation O G M) (a : O) (r : ℕ), (∀ n : ℕ, IsOpen ((powSub (M := M) a n : Submodule O M) : Set M)) → (∀ U ∈ nhds (0 : M), ∃ n : ℕ, ((powSub (M := M) a n : Submodule O M) : Set M) ⊆ U) → ∀ w : ℕ → G → M, (∀ k, (fun g => (Submodule.Quotient.mk (w k g) : M ⧸ powSub (M := M) a (r + k))) ∈ Z1 (quotRep ρ a (r + k))) → (∀ k g, w (k + 1) g - w k g ∈ powSub (M := M) a (r + k)) → ∃ e ∈ Z1 ρ, ∀ k g, e g - w k g ∈ powSub (M := M) a (r + k) := by
  first | exact @GlobalTheory.CocycleLimit.exists_continuous_cocycle_lift_of_compatible | exact GlobalTheory.CocycleLimit.exists_continuous_cocycle_lift_of_compatible | (intros; apply GlobalTheory.CocycleLimit.exists_continuous_cocycle_lift_of_compatible <;> assumption)
