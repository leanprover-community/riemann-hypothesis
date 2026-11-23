module

public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.ManyEdges
public import Formalism.SharpRestriction.GrowthBounds.ProjectionOfIsotypicDecomposition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.MainNotions.Pf14 Formalism.MainNotions.G.Joints

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem valLe_of_vK {p : ℕ} (S : UniformizedDVR p O) (D : ℕ) (a : O)
    (h : Formalism.MainNotions.PlaneGramData.leQ (vK p (algebraMap O (KK O) a)) (D : ℝ)) :
    ValLe (Kf := KK O) (p : O) D (algebraMap O (KK O) a) := by
  obtain ⟨q, hq, hqD⟩ := h
  have ha : a ≠ 0 := by
    rintro rfl
    have h0 : vK p (algebraMap O (KK O) 0) = ⊤ := by simp [vK, ordW]
    rw [h0] at hq
    exact WithTop.top_ne_coe hq
  rw [vK_alg p a ha] at hq
  have hq' : (nv a : ℚ) / (ramE p O : ℚ) = q := WithTop.coe_injective hq
  have hr : (0 : ℝ) < (ramE p O : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (ramE_ne_zero S)
  have hle : nv a ≤ D * ramE p O := by
    rw [← hq'] at hqD
    push_cast at hqD
    rw [div_le_iff₀ hr] at hqD
    exact_mod_cast hqD
  have hne : IsDiscreteValuationRing.addVal O a ≠ ⊤ := fun h0 =>
    ha (IsDiscreteValuationRing.addVal_eq_top_iff.mp h0)
  have hne' : IsDiscreteValuationRing.addVal O (p : O) ≠ ⊤ := fun h0 =>
    S.p_ne (IsDiscreteValuationRing.addVal_eq_top_iff.mp h0)
  have e1 : IsDiscreteValuationRing.addVal O a = (nv a : ℕ∞) := (ENat.coe_toNat hne).symm
  have e2 : IsDiscreteValuationRing.addVal O (p : O) = (ramE p O : ℕ∞) := (ENat.coe_toNat hne').symm
  have hdvd : a ∣ (p : O) ^ D := by
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow, e1, e2,
      nsmul_eq_mul]
    exact_mod_cast hle
  obtain ⟨b, hb⟩ := hdvd
  exact ⟨a, b, rfl, hb.symm⟩

end Formalism.MainNotions.TestSideCounting
