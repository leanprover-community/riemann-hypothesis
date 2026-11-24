module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperQuotIsoSt
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

open MvPolynomial

noncomputable section

universe u v w

def SnapperQuotFilt.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F₁ F₂ : SubFamily k x E), (∀ I, (F₁.sub I).FG) → (∀ I, F₂.sub I ≤ F₁.sub I) →
    ∀ J : Ideal (Poly k N), (∀ f ∈ J, ∀ d : ℕ, homogeneousComponent d f ∈ J) → primeOf (S := k) x ≤ J →
    (∀ I, (F₁.toSubSystem.twist (idealSys x J)).sub I ≤ F₂.sub I) →
    ∃ (r : ℕ) (G : ℕ → SubFamily k x E) (pp : Fin r → Ideal (Poly k N)) (a : Fin r → ℤ),
      (∀ m I, ((G m).sub I).FG) ∧ (G 0).toSubSystem = F₂.toSubSystem ∧
      (G r).toSubSystem = F₁.toSubSystem ∧ (∀ m < r, ∀ I, (G m).sub I ≤ (G (m + 1)).sub I) ∧
      (∀ m, (pp m).IsPrime ∧ (∀ f ∈ pp m, ∀ d : ℕ, homogeneousComponent d f ∈ pp m) ∧ J ≤ pp m) ∧
      ∀ (m : Fin r) (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ),
        Nonempty (QuotIso
          (((G (m + 1)).toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
          (((G m).toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
          (((twistSys k x (a m)).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
          ((((twistSys k x (a m)).twist (idealSys x (pp m))).twistPows t (fun j => (L j).toSubSystem) n).twist
            (twistSys k x c)))

end

end GroundTheory.Heights₂.Heights.Kleiman
