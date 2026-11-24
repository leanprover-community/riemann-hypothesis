module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHFreeObj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AmpleSt
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

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

def KHFreeEmbed.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (a : (Σ k, ι k) → ℤ),
    (∀ (n : ℕ) (f : CombC S (negSet a) n),
      KH.cechD S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n (embed S a n f) =
        embed S a (n + 1) (combD S (negSet a) n f)) ∧
    (∀ (c d : K → ℤ), blockSum a = c + d → ∀ (n : ℕ) (f : CombC S (negSet a) n),
      embed S a n f ∈ KH.cechCc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n) ∧
    ((∀ p, 0 ≤ a p) → ∃ m ∈ KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (blockSum a),
      ∀ I : ∀ k, Finset (ι k), monoFrac S I a = LocalizedModule.mk m 1)

end

end GroundTheory.Heights₂.Heights.Kleiman
