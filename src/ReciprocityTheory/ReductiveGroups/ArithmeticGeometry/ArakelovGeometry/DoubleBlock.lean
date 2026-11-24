module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsSmoothPts
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def mHom (ι : K → Type) [∀ k, Fintype (ι k)] (a : K → ℕ) : Submodule ℤ (MRing ι) :=
  Submodule.span ℤ {s | IsMultiHomog s a}

def mPiece (W : Ideal (MRing ι)) (a : K → ℕ) : Submodule ℤ (MRing ι ⧸ W) :=
  (mHom ι a).map (Ideal.Quotient.mkₐ ℤ W).toLinearMap

end

abbrev FinTwoTypeFamily (κ : Type) : Fin 2 → Type := fun _ => κ

variable {Ω : Type} [Field Ω] {κ : Type}

def pair (x x' : Ix κ → Ω) : (Σ k, FinTwoTypeFamily κ k) → Ω :=
  fun p => if p.1 = 0 then x ⟨(), p.2⟩ else x' ⟨(), p.2⟩

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
