module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenOnFibres
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def FibreRelLift.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (ℓ : ℕ) (a : K → ℤ) (r : ℕ) (s : Fin r → Ω)
    (J : KH.Cell K ι 0)
    (u : Fin r → LocalizedModule (KH.cellMon (ZMod ℓ) J.1) (MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ))),
    (∀ j, s j ∈ chartLat y a 1) → (∀ k, y ⟨k, GenOnFibres.cellChart J k⟩ ≠ 0) →
    (∀ j, u j ∈ KH.locPart ι (KH.quotPart (ZMod ℓ) (GenOnFibres.idealOver y (ZMod ℓ))) (KH.cellMon (ZMod ℓ) J.1) (-a)) →
    ∑ j, u j * GenOnFibres.secCoch (y := y) (S := ZMod ℓ) (s j) a J = 1 →
    ∃ (u' : Fin r → Ω) (v : Ω), (∀ j, u' j ∈ chartRingZ y (GenOnFibres.cellChart J)) ∧
      v ∈ chartRingZ y (GenOnFibres.cellChart J) ∧
      ∑ j, u' j * (s j * ∏ k, y ⟨k, GenOnFibres.cellChart J k⟩ ^ (-a k)) + ℓ * v = 1

end GroundTheory.Heights₂.Heights.HilbertSamuel
