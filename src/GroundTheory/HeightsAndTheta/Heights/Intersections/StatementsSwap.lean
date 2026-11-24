module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SwapCycles.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ)
    (a a' : K → ℕ) (s s' : MRing ι),
    IsArithVar P d → IsMultiHomog s a → IsMultiHomog s' a' → s ∉ P → s' ∉ P →
    (∀ W, W ∈ divSupp P s → W ∉ divSupp P s') →
    ((divCycle P s).sum fun W m => m • divCycle W s') =
      (divCycle P s').sum fun W m => m • divCycle W s

def GeoNumCut.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (V : Ideal (MRing ι)) (n : ℕ)
    (a : Fin n → K → ℤ) (b : K → ℕ) (t : MRing ι),
    IsMultiProjPrime V → (charOf V).Prime →
    ringKrullDim (MRing ι ⧸ V) = ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    IsMultiHomog t b → t ∉ V →
    geoNum (n + 1) V (Fin.snoc a fun k => (b k : ℤ)) =
      ∑ᶠ U ∈ divSupp V t, (multAt (V ⊔ Ideal.span {t}) U : ℤ) * geoNum n U a

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Inter
