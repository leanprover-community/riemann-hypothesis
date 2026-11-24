module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpOrbOfAmpDD
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothAdd
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

open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.QuantumDeterminants

theorem nonzero_K_finite : Formalism.MainNotions.S.Pv.AmpDD.NzKF := by
  intro hKD hKS k r ε lam H _ _ _ σ w0 Wp _ _ z c π hlam hσ hw0 l hl hnz
  obtain ⟨x, hxDD, hlx⟩ := hnz
  have hxs : x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ :=
    Formalism.FourierDecayAlt.P.DDSmoothness.DD_smooth hKS hlam hσ hw0 x hxDD
  obtain ⟨hadd, hsmul, -, C, Ws, hWs, hbd⟩ := hl
  have hpos : 0 < ‖l x‖ := norm_pos_iff.mpr hlx
  set e : ℝ := ‖l x‖ / (|C| + 1) with he
  have he0 : 0 < e := div_pos hpos (by positivity)
  obtain ⟨v, hvK, hv⟩ := hKD k r ε lam H σ hlam hσ x hxs Ws hWs e he0
  refine ⟨v, hvK, fun hlv => ?_⟩
  have hvs : v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := hKS k r ε lam H σ hlam hσ v hvK
  have hdiff_s : x - v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ v]
    exact Formalism.FourierDecayAlt.P.DDSmoothness.smooth_add hxs (Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul (-1) hvs)
  have hsplit : l x = l (x - v) + l v := by
    have := hadd (x - v) hdiff_s v hvs
    rw [sub_add_cancel] at this
    exact this
  rw [hlv, add_zero] at hsplit
  have hb := hbd (x - v) hdiff_s
  set S := (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w (x - v)‖).sum with hS
  have hS0 : 0 ≤ S := by
    rw [hS]; apply List.sum_nonneg; intro y hy
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hy; exact norm_nonneg _
  have h1 : ‖l x‖ ≤ |C| * S := by
    rw [hsplit]; exact hb.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hS0)
  have h2 : |C| * S ≤ |C| * e := mul_le_mul_of_nonneg_left hv.le (abs_nonneg C)
  have h3 : |C| * e < ‖l x‖ := by
    rw [he, mul_div_assoc']
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg C]
  linarith

end Formalism.MainNotions.S.Pv.AmpDDPf
