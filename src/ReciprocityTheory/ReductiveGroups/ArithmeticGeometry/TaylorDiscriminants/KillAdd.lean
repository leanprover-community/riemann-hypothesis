module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB

variable {k : Type} [CommRing k] {d n : ℕ}

def dAdd (u : Fin d → k) (b : Fin n) (G : PS k n d) : PS k n d :=
  ∑ j : Fin d, C (u j) * MvPowerSeries.pderiv (b, j) G

def polyAdd {ι : Type} [Fintype ι] (u : ι → Fin d → k) (P : MvPolynomial (ι × Fin n) k) (G : PS k n d) :
    PS k n d :=
  ∑ m ∈ P.support, C (P.coeff m) *
    (Finset.univ : Finset (ι × Fin n)).toList.foldr (fun p g => (dAdd (u p.1) p.2)^[m p] g) G

def quadCol (β : Matrix (Fin d) (Fin d) k) : PS k n d :=
  ∑ b : Fin n, ∑ i : Fin d, ∑ j : Fin d, C (β i j) * X (b, i) * X (b, j)

def KillAddSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d n : ℕ) (ι : Type) [Fintype ι] (u : ι → Fin d → k)
    (β : Matrix (Fin d) (Fin d) k) (P : MvPolynomial (ι × Fin n) k),
    secondOrder k (fun p p' : ι × Fin n => if p.2 = p'.2 then
      dotProduct (u p.1) (β.mulVec (u p'.1)) + dotProduct (u p'.1) (β.mulVec (u p.1)) else 0) P = 0 →
    ∀ (m : k) (g : PS k n d),
      constantCoeff (polyAdd u P (FB.expS k (m • quadCol (n := n) β) * g)) = constantCoeff (polyAdd u P g)

end ReciprocityTheory.ChartRestriction.G.TB
