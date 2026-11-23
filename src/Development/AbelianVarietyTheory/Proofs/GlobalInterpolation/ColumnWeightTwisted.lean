module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelChainSharpColumnValuationOwnChainIff
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions GlobalTheory.LvT

namespace GlobalTheory.Proof.ColumnWeightTwisted

theorem exists_int_m_mul_EatT (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) :
    ∃ k : ℤ, (D.R.m : ℝ) * EatT D u w = (k : ℝ) := by
  unfold EatT
  split_ifs
  · obtain ⟨a, ha⟩ := D.R.m_even
    obtain ⟨b, hb⟩ := D.R.t_odd
    refine ⟨(D.R.m : ℤ) * (2 * (∑ τ : D.what₂.Tau, (Wtau D u τ : ℤ)) + (D.R.f : ℤ) * (D.R.N D.R.m : ℤ)) +
      ((topsOf D.host D.eTau).card : ℤ) * ((b : ℤ) + 1) * ((D.R.m : ℤ) + 1) * a, ?_⟩
    have ha' : (D.R.m : ℝ) = a + a := by exact_mod_cast ha
    have hb' : (D.R.t : ℝ) = 2 * b + 1 := by exact_mod_cast hb
    unfold Formalism.MainNotions.G.Nm
    push_cast
    rw [hb', ha']
    ring
  · exact ⟨0, by simp⟩

theorem colGeTw_of_tupleChainSharpColumnValuation : ∀ (D : D7) (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup), TupleChainSharpColumnValuation T u μ → ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T → ∀ x ∈ LT.Nlam D u w, Formalism.MainNotions.WeilJacquetShalikaLaw.ColGeTw T u μ w x (-((D.R.m : ℝ) * EatT D u w)) := by
  intro D T u μ h w hw x hx
  obtain ⟨k, hk⟩ := exists_int_m_mul_EatT D u w
  obtain ⟨c, hc⟩ := D.what₂.places.val_surj w ((D.what₂.places.ramIdx w : ℤ) * k)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [AddValuation.map_zero] at hc
    exact WithTop.top_ne_coe hc
  obtain ⟨y, hy, e⟩ := h w hw c _ hc (by rw [hk]; push_cast; exact le_rfl) x hx
  have hv : vAdd (D.plEq w) c = (D.what₂.places.ramIdx w : ℤ) * k := by
    rw [D.val_eq w _ hc0] at hc
    exact_mod_cast hc
  have hvi : vAdd (D.plEq w) c⁻¹ = - vAdd (D.plEq w) c := by
    unfold vAdd
    rw [map_inv₀, WithZero.log_inv]
  refine ⟨c⁻¹ • y, ?_, c⁻¹, y, hy, rfl, Or.inr ?_⟩
  · rw [LinearMap.map_smulₛₗ, e, smul_smul, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_smul]
  · rw [hvi, hv, hk]
    unfold DV.ur
    push_cast
    exact le_of_eq (by ring)

end GlobalTheory.Proof.ColumnWeightTwisted
