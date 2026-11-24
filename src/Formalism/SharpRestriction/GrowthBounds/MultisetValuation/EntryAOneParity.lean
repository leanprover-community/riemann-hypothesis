module

public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

theorem ea_applyD_map {σ τ K K' : Type} [Field K] [Field K'] (φ : K →+* K')
    (P : MvPolynomial σ (MvPolynomial τ ℤ)) (f : MvPowerSeries σ K) :
    applyD P (MvPowerSeries.map φ f) = MvPolynomial.map φ (applyD P f) := by
  unfold applyD

  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have e : φ.comp (Int.castRingHom K) = Int.castRingHom K' := RingHom.ext_int _ _
  have e2 : φ (∏ x ∈ n.support, ((n x).factorial : K)) = ∏ x ∈ n.support, ((n x).factorial : K') := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun x _ => map_natCast φ _
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul (MvPolynomial.map φ), MvPolynomial.map_C,
    MvPolynomial.map_map, e, MvPowerSeries.coeff_map, map_mul φ, e2]

def ea_InClassA (X : Sys p) {K' : Type} [Field K'] (R' : Subring K') (j : ℕ) (h F : MvPowerSeries (X.ZA j) K') : Prop :=
  ∃ g : ℕ → MvPowerSeries (X.ZA j) K', (∀ i, IntR R' (g i)) ∧ ∀ α : X.ZA j →₀ ℕ,
    MvPowerSeries.coeff α F = ∑ i ∈ range (α.degree + 1),
      (((p : K') ^ i)⁻¹ * MvPowerSeries.coeff α (h ^ i * g i))

def ea_RestSU (X : Sys p) (Y : Pend X) : Prop :=
  DworkLemma p → BeProp p Y.be → ∀ (v : X.Pl) (j : ℕ) (U : MvPowerSeries (X.EA j ⊕ X.EA j) Y.Kc),
    IntR Y.Oc (inParamK p Y.Kc U) →
    ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] [Algebra Y.Kc K'] [IsScalarTower (K0 p) Y.Kc K'] (R' : Subring K')
      (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') → Rp p K' vp ≤ R' → (∀ x ∈ Y.Oc, algebraMap Y.Kc K' x ∈ R') →
      ∃ u : Fin (X.G.P.n' v) → K', (∀ s, u s ∈ R') ∧
        ea_InClassA X R' j (X.hhA K' j v u) (atPi vp (MvPowerSeries.map (algebraMap Y.Kc K')
          (X.ThZA Y.Kc j (MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-Y.PhAt j v)) * U))))

end Formalism.MainNotions.FormalGroupSystem.Pf
