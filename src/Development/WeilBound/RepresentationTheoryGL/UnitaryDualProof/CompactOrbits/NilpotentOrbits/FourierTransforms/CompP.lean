module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseP
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

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Four

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def PhiP : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z →
    ∃ Φ Φ' : (Sp k n → ℂ) →ₗ[ℂ] (Sp k n → ℂ),
      (∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), Φ f ∈ supportedIn (Set.univ : Set (Sp k n))) ∧
      (∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), Φ' f ∈ supportedIn (Set.univ : Set (Sp k n))) ∧
      (∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), ∀ y, (∀ p ∈ Fib Z y, f p = 0) → ∀ p ∈ Fib Z y, Φ f p = 0) ∧
      (∀ g ∈ Gz Z, ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), ∀ p ∈ Bz Z ×ˢ Set.univ,
        Φ (fun q => f (act g q)) p = Φ f (act g p)) ∧
      (∀ f ∈ supportedIn (UU : Set (Sp k n)), Φ f ∈ supportedIn (UU : Set (Sp k n))) ∧
      (∀ f ∈ supportedIn (UU : Set (Sp k n)), Φ' f ∈ supportedIn (UU : Set (Sp k n))) ∧
      (∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), ∀ p ∈ Bz Z ×ˢ Set.univ, Φ (Φ' f) p = f p) ∧
      (∀ (t : kˣ), ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), ∀ p ∈ Bz Z ×ˢ Set.univ,
        Φ f (sig Z t p) = ((((nabs k t)⁻¹ ^ dB0 Z : ℝ)) : ℂ) * Φ (fun q => f (sig Z t⁻¹ q)) p)

def CompP : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z →
    (∀ (t : kˣ), ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), (fun q => f (sig Z t q)) ∈ supportedIn (Set.univ : Set (Sp k n))) ∧
    (∀ (g : GL (Fin n) k), ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), (fun q => f (act g q)) ∈ supportedIn (Set.univ : Set (Sp k n))) ∧
    (∀ (t : kˣ) p, p ∈ Bz Z ×ˢ Set.univ → sig Z t p ∈ Bz Z ×ˢ Set.univ) ∧
    (∀ g ∈ Gz Z, ∀ p, p ∈ Bz Z ×ˢ Set.univ → act g p ∈ Bz Z ×ˢ Set.univ)

end PositivityTheory.RgUd.T.Nil.Four
