module

public import Formalism.HermitianCurvature.TopDensNonnegOfKappa
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

open MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

theorem signed_coordinate_eq_sign_smul (P : M.Par) (l : ℕ) (Y : ℂ) :
    (fun ρ => M.x0 P l ρ Y) = M.sgn P l • fun ρ => M.xC P ρ Y := by
  funext ρ
  simp only [Pi.smul_apply, smul_eq_mul, M.x0, M.sgn, M.xC]

theorem xKappaOfNF : XKappaOfNF := by
  intro hNF hPos Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hD
  obtain ⟨hPl, -, hL, hQQ, -, hinv, -, hLS⟩ := hD
  obtain ⟨d, hdL, hdS, hdR, hdQ⟩ := hNF Wp Wq P z z' π π' hPl X
  have hfn : ∀ i j : Fin 6,
      (∀ x ∈ DomR P.k P.r z z', fnVal P.k P.r z z' i x.2 * fnVal P.k P.r z z' j x.2 = 1) →
      X.fn i * X.fn j = 1 := by
    intro i j hij
    refine LinearMap.ext fun Φ => Subtype.ext (funext fun c => funext fun g => ?_)
    rw [Module.End.mul_apply, Module.End.one_apply]
    by_cases hx : (c, g) ∈ DomR P.k P.r z z'
    · have e1 := X.fn_apply i (X.fn j Φ) (c, g) hx
      have e2 := X.fn_apply j Φ (c, g) hx
      dsimp only at e1 e2
      rw [e1, e2, smul_smul, hij (c, g) hx, one_smul]
    · have e1 := (X.fn i (X.fn j Φ)).2.1 (c, g) hx
      have e2 := Φ.2.1 (c, g) hx
      dsimp only at e1 e2
      rw [e1, e2]
  have hG : ∀ x ∈ DomR P.k P.r z z', fnVal P.k P.r z z' 5 x.2 * fnVal P.k P.r z z' 4 x.2 = 1 := by
    intro x hx
    simp only [fnVal]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hx.2.2.ne')
  have hG' : ∀ x ∈ DomR P.k P.r z z', fnVal P.k P.r z z' 4 x.2 * fnVal P.k P.r z z' 5 x.2 = 1 := by
    intro x hx
    simp only [fnVal]
    exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hx.2.2.ne')
  have hGinv : L.GGi * L.GG = 1 := by
    rw [hL.2.2.2.2.2.2.2.2.2.2.1, hL.2.2.2.2.2.2.2.2.2.2.2.1]
    refine Prod.ext ?_ ?_
    · show X.fn 5 * X.fn 4 = 1
      exact hfn 5 4 hG
    · show MulOpposite.op (X.fn 5) * MulOpposite.op (X.fn 4) = MulOpposite.op 1
      rw [← MulOpposite.op_mul, hfn 4 5 hG']
  have hGG : L.GG = d.L.GG := hL.2.2.2.2.2.2.2.2.2.2.1.trans hdL.2.2.2.2.2.2.2.2.2.2.1.symm
  have hx : ∀ Y, st.x Y = d.κ fun ρ => M.x0 P l0 ρ Y := by
    intro Y
    have h1 := hLS.tau Y
    have h2 : d.QQ Y 1 1 = d.L.GG * d.x Y := by simp [NFData.QQ]
    rw [hQQ Y, hdQ Y, Matrix.smul_apply, h2, ← hGG, ← mul_smul_comm] at h1
    have h3 : st.x Y = M.sgn P l0 • d.x Y := by
      calc st.x Y = L.GGi * (L.GG * st.x Y) := by rw [← mul_assoc, hGinv, one_mul]
        _ = L.GGi * (L.GG * (M.sgn P l0 • d.x Y)) := by rw [← h1]
        _ = _ := by rw [← mul_assoc, hGinv, one_mul]
    rw [h3, NFData.x, signed_coordinate_eq_sign_smul, map_smul]
  have hxi : ∀ Y ∈ st.inv, st.xi Y = d.κ fun ρ => (M.x0 P l0 ρ Y)⁻¹ := by
    intro Y hY
    have hne : ∀ ρ, M.x0 P l0 ρ Y ≠ 0 := by
      intro ρ
      have hY' := hY
      rw [hinv] at hY'
      have e := congrFun (signed_coordinate_eq_sign_smul P l0 Y) ρ
      simp only [Pi.smul_apply, smul_eq_mul] at e
      rw [e]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (hY' ρ)
    have hprod : (d.κ fun ρ => M.x0 P l0 ρ Y) * (d.κ fun ρ => (M.x0 P l0 ρ Y)⁻¹) = 1 := by
      rw [← map_mul, ← map_one d.κ]
      congr 1
      funext ρ
      simp [hne ρ]
    calc st.xi Y
        = st.xi Y * ((d.κ fun ρ => M.x0 P l0 ρ Y) * (d.κ fun ρ => (M.x0 P l0 ρ Y)⁻¹)) := by
          rw [hprod, mul_one]
      _ = (st.xi Y * st.x Y) * (d.κ fun ρ => (M.x0 P l0 ρ Y)⁻¹) := by rw [hx Y, mul_assoc]
      _ = _ := by rw [(hLS.x_xi Y hY).2, one_mul]
  exact ⟨d.κ, hx, hxi, hPos Wp Wq P z z' π π' hPl X d hdL hdS hdR hdQ⟩

end Formalism.FourierDecayAlt.P5
