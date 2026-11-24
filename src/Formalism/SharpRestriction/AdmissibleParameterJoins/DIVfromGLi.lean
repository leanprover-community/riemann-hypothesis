module

public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.WeilJacquetShalikaLaw

theorem mEatT_nat (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) : ∃ n : ℕ, (D.R.m : ℝ) * EatT D u w = n := by
  classical
  obtain ⟨a, ha⟩ := D.R.m_even
  obtain ⟨b, hb⟩ := D.R.t_odd
  have hm : (D.R.m : ℝ) = 2 * (a : ℝ) := by rw [ha]; push_cast; ring
  have ht : (D.R.t : ℝ) = 2 * (b : ℝ) + 1 := by rw [hb]; push_cast; ring
  unfold EatT
  split_ifs with hs
  · first
    | simp only [Formalism.MainNotions.G.Nm]
    | simp only [Formalism.Nm]
    | skip
    refine ⟨D.R.m * (2 * ∑ τ : D.what₂.Tau, Wtau D u τ) + D.R.m * D.R.f * D.R.N D.R.m +
      (topsOf D.host D.eTau).card * (b + 1) * a * (2 * a + 1), ?_⟩
    push_cast
    rw [hm, ht]
    ring
  · exact ⟨0, by simp⟩

theorem vAdd_Tpow (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hw : D.what₂.places.resChar w = (D.mem u).A.T) (n : ℕ) :
    D.what₂.places.val w ((((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n) = (((n * D.what₂.places.ramIdx w : ℕ) : ℤ) : WithTop ℤ) := by
  rw [AddValuation.map_pow, ← hw, D.what₂.places.val_resChar w, ← WithTop.coe_nsmul]
  congr 1

theorem ColGe0_atT (D : D7) (u : D.what₂.Word) (h5 : Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp D u) (w : D.what₂.places.Pl)
    (hw : D.what₂.places.resChar w = (D.mem u).A.T) (x : ((D.fm u).lat 0).V) (hx : x ∈ LT.Nlam D u w) :
    ColGe0 D u w x (-((D.R.m : ℝ) * EatT D u w)) := by
  obtain ⟨n0, hn0⟩ := mEatT_nat D u w
  have hT0 : (((D.mem u).A.T : ℕ) : D.what₂.LL) ≠ 0 := by
    have hp := D.what₂.places.resChar_prime w
    rw [hw] at hp
    exact_mod_cast hp.ne_zero
  have hc0 : (((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n0 ≠ 0 := pow_ne_zero _ hT0
  have hval := vAdd_Tpow D u w hw n0
  have hle : (D.what₂.places.ramIdx w : ℝ) * ((D.R.m : ℝ) * Formalism.MainNotions.product_first_zeroth_parts.ET D u w) ≤
      (((n0 * D.what₂.places.ramIdx w : ℕ) : ℤ) : ℝ) := by
    show (D.what₂.places.ramIdx w : ℝ) * ((D.R.m : ℝ) * EatT D u w) ≤ _
    rw [hn0]
    push_cast
    rw [mul_comm]
  obtain ⟨y', hy'S, hy'⟩ := h5 w hw _ _ hval hle x hx
  refine ⟨((((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n0)⁻¹ • y', ?_,
    ((((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n0)⁻¹, y', hy'S, rfl, Or.inr ?_⟩
  · rw [map_smulₛₗ, hy', smul_smul, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_smul]
    rfl
  · have hinv : D.what₂.places.val w ((((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n0)⁻¹ =
        ((-((n0 * D.what₂.places.ramIdx w : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
      rw [AddValuation.map_inv, hval]
      rfl
    have hv := D.val_eq w _ (inv_ne_zero hc0)
    rw [hinv] at hv
    have hvz : vAdd (D.plEq w) ((((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n0)⁻¹ =
        -((n0 * D.what₂.places.ramIdx w : ℕ) : ℤ) := (WithTop.coe_injective hv).symm
    rw [hvz]
    show (D.what₂.places.ramIdx w : ℝ) * (-((D.R.m : ℝ) * EatT D u w)) ≤ _
    rw [hn0]
    push_cast
    nlinarith

end Formalism.MainNotions.J

end
