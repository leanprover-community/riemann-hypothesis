module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial TensorProduct


variable {Ω : Type*} [Field Ω]


section Join

variable {Ω Ω' : Type*} [Field Ω] [Field Ω'] [Algebra Ω Ω'] {ι κ : Type*}
  {E : Type*} [AddCommGroup E] [Module Ω E] {r : ℕ}

def joinPt (x : ι → Ω) (z : κ → Ω') : ι × κ → Ω' :=
  segreJoin (fun i => algebraMap Ω Ω' (x i)) z

end Join

section AddBlock

universe u

def addBlockIdx {K : Type*} (ι : K → Type u) (κ : Type u) : Option K → Type u
  | none => κ
  | some k => ι k

def addBlockPt {K : Type*} {ι : K → Type u} {κ : Type u} {Ω Ω' : Type*} [Field Ω] [Field Ω']
    [Algebra Ω Ω'] (y : (Σ k, ι k) → Ω) (z : κ → Ω') : (Σ o, addBlockIdx ι κ o) → Ω'
  | ⟨none, i⟩ => z i
  | ⟨some k, i⟩ => algebraMap Ω Ω' (y ⟨k, i⟩)

end AddBlock

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights
