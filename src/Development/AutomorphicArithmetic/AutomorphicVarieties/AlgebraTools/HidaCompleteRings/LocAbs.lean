module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PrecompleteOfFinite
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

open IsLocalRing

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locAbs :
    ∀ (Λ T : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [CommRing T] [Algebra Λ T] [Module.Finite Λ T] (ι : Type) (t : ι → T) (a : ι → Λ), Algebra.adjoin Λ (Set.range t) = ⊤ → ∃ e : T, IsIdempotentElem e ∧ (∀ i, ∃ n : ℕ, (t i - algebraMap Λ T (a i)) ^ n * e ∈ (maximalIdeal Λ).map (algebraMap Λ T)) ∧ 1 - e ∈ (maximalIdeal Λ).map (algebraMap Λ T) ⊔ Ideal.span (Set.range fun i => t i - algebraMap Λ T (a i)) ∧ (∀ s : T, ∃ c : Λ, s - algebraMap Λ T c ∈ (maximalIdeal Λ).map (algebraMap Λ T) ⊔ Ideal.span (Set.range fun i => t i - algebraMap Λ T (a i))) ∧ (e ≠ 0 → ((maximalIdeal Λ).map (algebraMap Λ T) ⊔ Ideal.span (Set.range fun i => t i - algebraMap Λ T (a i))).IsMaximal) :=
  _root_.UpperTheory.Reformulated.B.Qe2.locAbs
