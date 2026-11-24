module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleCechObj
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

noncomputable section

universe u v w

def CechDouble.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] (N r : ℕ) (x : Fin (N + 1) → Ω) (h : Fin (r + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module S E]
    (A : Chart x → Submodule S E) (B : Chart h → Submodule S E) (M : Chart x → Chart h → Submodule S E),
    (∀ (I I' : Chart x) (J : Chart h), I.1 ⊆ I'.1 → M I J ≤ M I' J) →
    (∀ (I : Chart x) (J J' : Chart h), J.1 ⊆ J'.1 → M I J ≤ M I J') →
    (∀ I, Cech.AugExact S (M I) (A I)) → (∀ J, Cech.AugExact S (fun I => M I J) (B J)) →
    ∀ n : ℕ, Nonempty (Cech.Hdeg (fun _ : Chart x => E) A (Cech.idRes S E (support x)) n ≃ₗ[S]
      Cech.Hdeg (fun _ : Chart h => E) B (Cech.idRes S E (support h)) n)

end

end GroundTheory.Heights₂.Heights.Kleiman
