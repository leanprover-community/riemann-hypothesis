module

public import Formalism.ConjugateSelfDual.Statement
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
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

@[expose] public section

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory

theorem image_finite_mem_subring (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (iq : FractionRing O →+* Qbar l)
    (hiq : ∀ z : ℤ_[l], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) :
    ∃ T : Finset (Qbar l), ∀ R : Subring (Qbar l), (∀ z : ℤ_[l], algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) ∈ R) → (↑T ⊆ (R : Set (Qbar l))) → ∀ x : O, iq (algebraMap O (FractionRing O) x) ∈ R := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[l]) (M := O)
  refine ⟨s.image (fun x => iq (algebraMap O (FractionRing O) x)), ?_⟩
  intro R hR hT x
  have hx : x ∈ Submodule.span ℤ_[l] (s : Set O) := by rw [hs]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    exact hT (by simpa using Finset.mem_image_of_mem (fun x => iq (algebraMap O (FractionRing O) x)) hy)
  | zero => simpa using R.zero_mem
  | add a b _ _ ha hb => simpa using R.add_mem ha hb
  | smul c a _ ha =>
    rw [Algebra.smul_def, map_mul, map_mul, hiq]
    exact R.mul_mem (hR c) ha

end GlobalTheory
