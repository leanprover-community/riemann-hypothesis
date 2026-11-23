module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import GroundTheory.HeightsAndTheta.Heights.LocalDensities.PHermitianDetMono
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne

@[expose] public section

open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace PositivityTheory.Xgp.gram_size

theorem one {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℂ) (m : ℝ) (hm : 1 ≤ m) (hA : A.PosDef) (hB : B.PosDef)
    (h : ((m : ℂ) • B - A).PosSemidef) : Real.log A.det.re - Real.log B.det.re ≤ k * Real.log m := by
  have h1 : A.det.re ≤ ((m : ℂ) • B).det.re :=
    GroundTheory.Heights₂.Heights.FourB.HermitianDetMono.proof k ((m : ℂ) • B) A hA.posSemidef h
  have e : ((m : ℂ) • B).det.re = m ^ k * B.det.re := by
    rw [det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  have hA' : 0 < A.det.re := by simpa using (Complex.lt_def.mp hA.det_pos).1
  have hB' : 0 < B.det.re := by simpa using (Complex.lt_def.mp hB.det_pos).1
  have hm' : 0 < m := by linarith
  rw [e] at h1
  have h2 := Real.log_le_log hA' h1
  rw [Real.log_mul (by positivity) hB'.ne', Real.log_pow] at h2
  linarith

end PositivityTheory.Xgp.gram_size

theorem PositivityTheory.Xgp.t_gram_size : ∀ (n k : ℕ) (G G₀ : Matrix (Fin n) (Fin n) ℂ) (V : Matrix (Fin n) (Fin k) ℂ) (m : ℝ), 1 ≤ m → G₀.PosDef → G.PosDef → ((m : ℂ) • G₀ - G).PosSemidef → ((m : ℂ) • G - G₀).PosSemidef → LinearIndependent ℂ Vᵀ → |Real.log (Vᴴ * G * V).det.re - Real.log (Vᴴ * G₀ * V).det.re| ≤ k * Real.log m := by
  intro n k G G₀ V m hm hG₀ hG h1 h2 hV
  have hinj : Function.Injective V.mulVec := Matrix.mulVec_injective_iff.mpr hV
  have hA : (Vᴴ * G * V).PosDef := hG.conjTranspose_mul_mul_same hinj
  have hB : (Vᴴ * G₀ * V).PosDef := hG₀.conjTranspose_mul_mul_same hinj
  have e1 : Vᴴ * ((m : ℂ) • G₀ - G) * V = (m : ℂ) • (Vᴴ * G₀ * V) - Vᴴ * G * V := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  have e2 : Vᴴ * ((m : ℂ) • G - G₀) * V = (m : ℂ) • (Vᴴ * G * V) - Vᴴ * G₀ * V := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  have p1 := h1.conjTranspose_mul_mul_same V
  have p2 := h2.conjTranspose_mul_mul_same V
  rw [e1] at p1
  rw [e2] at p2
  have a1 := PositivityTheory.Xgp.gram_size.one _ _ m hm hA hB p1
  have a2 := PositivityTheory.Xgp.gram_size.one _ _ m hm hB hA p2
  rw [abs_sub_le_iff]
  constructor <;> linarith
