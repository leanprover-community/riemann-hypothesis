module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.Finiteness.Defs
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def relChartLat {K : Type*} [Fintype K] {ι : K → Type*} {Ω : Type*} [Field Ω] (R : Subalgebra ℤ Ω)
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) : Submodule R Ω where
  carrier := {s | ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
    s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k)) ∈
      Algebra.adjoin R (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)}
  add_mem' := fun {s t} hs ht c hc => by rw [add_mul]; exact add_mem (hs c hc) (ht c hc)
  zero_mem' := fun c _ => by simp
  smul_mem' := fun r s hs c hc => by rw [smul_mul_assoc]; exact Subalgebra.smul_mem _ (hs c hc) r

def RelLatticeFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n m : ℕ) (g : Fin m → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (relChartLat (Algebra.adjoin ℤ (Set.range g)) y a n).FG

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
