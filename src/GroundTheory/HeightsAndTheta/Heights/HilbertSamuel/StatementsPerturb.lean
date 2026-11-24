module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
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
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SemiposTwist.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P0 P : Ideal (MRing ι)) (L : HermLine ι)
    (p q : ℕ), IsSemipositiveRel P0 P L → IsSemipositiveRel P0 P (HermLine.zcomb L (fsH ι) q p)

def GenOnFibres.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) (w : Fin n → Ω),
    (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w →
    KH.GeneratedV ℚ (KH.genIdeal y) a ∧ ∀ ℓ : ℕ, ℓ.Prime → KH.GeneratedV (ZMod ℓ) (fibreIdeal ℓ y) a

def AmpleOfGenTwist.Statement : Prop :=
  ∀ (S : Type) [Field S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (α : K → ℤ) (p q : ℕ),
    IsMultiHomogIdeal V → KH.GeneratedV S V α → 1 ≤ p →
    KH.AmpleV S V ((q : ℤ) • α + fun _ => (p : ℤ))

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
