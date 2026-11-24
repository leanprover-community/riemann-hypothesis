module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
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

open Filter

noncomputable section

universe u w


open Classical in
def SectionCount.Drop.Filt.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (d : ℕ)
    (Nb : LineBundle k x) (b : ℕ), IsSubvar x (primeOf (S := k) x) (d + 1) → 1 ≤ b →
    ∃ β ∈ (twistSys k x (b : ℤ)).secs,
      (∃ I, β ∉ ((twistSys k x (b : ℤ)).twist (idealSys x (primeOf (S := k) x))).sub I) ∧
      ∃ (m : ℕ) (pp : Fin m → Ideal (Poly k N)) (e : Fin m → ℕ) (c : Fin m → ℤ),
        (∀ j, IsSubvar x (pp j) (e j) ∧ e j ≤ d ∧
          primeOf (S := k) x ⊔ zeroIdeal (twistSys k x (b : ℤ)) β ≤ pp j) ∧
        (∀ qq : Ideal (Poly k N),
          ((Finset.univ.filter fun j => e j = d ∧ pp j = qq).card : ℤ) =
            if h : qq ∈ (primeOf (S := k) x ⊔ zeroIdeal (twistSys k x (b : ℤ)) β).minimalPrimes ∧
                IsSubvar x qq d then
              haveI : qq.IsPrime := h.1.1.1
              ((cutMult (primeOf (S := k) x ⊔ zeroIdeal (twistSys k x (b : ℤ)) β) qq).toNat : ℤ)
            else 0) ∧
        ∀ n i : ℕ,
          (Module.finrank k (twistMul Nb.toSubSystem n (-((i : ℤ) * b))).secs : ℤ) -
              (Module.finrank k (twistMul Nb.toSubSystem n (-(((i + 1 : ℕ) : ℤ) * b))).secs : ℤ) ≤
            ∑ j, (Module.finrank k (SubSystem.quotH
              ((twistMul Nb.toSubSystem n (-((i : ℤ) * b))).twist (twistSys k x (c j)))
              (((twistMul Nb.toSubSystem n (-((i : ℤ) * b))).twist (twistSys k x (c j))).twist
                (idealSys x (pp j))) 0) : ℤ)

end

end GroundTheory.Heights₂.Heights.Kleiman
