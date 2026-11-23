module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

def OrthChange : Prop :=
  ∀ (D : D7) (p : ℕ), p.Prime → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (r r' : ℕ)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (b' : Fin r' → Matrix (Fin N') (Fin N) D.host.E),
    LocBasis D p (YYl D L L') b → Orthonormal D b → LocBasis D p (YYl D L L') b' → Orthonormal D b' →
    r' = r ∧ ∃ A : Fin r → Fin r' → D.host.E,
      (∀ i j, A i j ∈ D.host.K) ∧
      (∀ i j, ∃ s : ℕ, Nat.Coprime s p ∧ ∃ c : 𝓞 D.host.K, (s : D.host.E) * A i j = ((c : D.host.K) : D.host.E)) ∧
      (∀ j j', ∑ i, A i j * D.host.conj (A i j') = if j = j' then 1 else 0) ∧
      ∀ j, b' j = ∑ i, A i j • b i

def UnitSubst : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (lam : Qbar →+* ℂ_[p]) (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]),
      IsModel lam (lamOf D cc δ) C → IsWq (C • wModel lam (lamOf D cc δ)) wq →
    ∀ (r : ℕ) (A : Fin r → Fin r → D.host.E), (∀ i j, A i j ∈ D.host.K) →
      (∀ i j, ∃ s : ℕ, Nat.Coprime s p ∧ ∃ c : 𝓞 D.host.K, (s : D.host.E) * A i j = ((c : D.host.K) : D.host.E)) →
      (∀ j j', ∑ i, A i j * D.host.conj (A i j') = if j = j' then 1 else 0) →
      ∃ S : Fin r → MvPowerSeries (Fin r) ℂ_[p],
        (∀ i, MvPowerSeries.constantCoeff (S i) = 0) ∧ (∀ i, IntegralMv (S i)) ∧
        (∀ i, PowerSeries.subst (S i) (flog (C • wModel lam (lamOf D cc δ)) wq) =
          ∑ j, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) (lamC lam (D.host.φ₀ (A i j))) *
            PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin r) ℂ_[p])
              (flog (C • wModel lam (lamOf D cc δ)) wq)) ∧
        ∃ V : MvPowerSeries (Fin r) ℂ_[p], IntegralMv V ∧
          ePh lam (lamOf D cc δ) C wq r = MvPowerSeries.subst S (ePh lam (lamOf D cc δ) C wq r) * V

end Formalism.L2.KerInert
