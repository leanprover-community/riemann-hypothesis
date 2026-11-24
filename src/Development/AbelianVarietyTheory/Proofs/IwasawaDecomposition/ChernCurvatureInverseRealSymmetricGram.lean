module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.RealGram

open GlobalTheory.HermFrame Filter

theorem curv_inv_of_real : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {g : ℕ} (H : E → Matrix (Fin g) (Fin g) ℂ) (z : E), GlobalTheory.HermFrame.MContDiffAt 2 H z → IsUnit (H z).det → (∀ᶠ x in 𝓝 z, (H x).IsSymm) → (∀ᶠ x in 𝓝 z, (H x).IsHermitian) → (∀ ξ η, GlobalTheory.HermFrame.mddbar H z ξ η = 0) → ∀ ξ η, GlobalTheory.HermFrame.curv (fun x => (H x)⁻¹) z ξ η = -((GlobalTheory.HermFrame.conn H z η)ᵀᴴ * GlobalTheory.HermFrame.conn H z ξ)ᵀ := by
  intro E _ _ _ _ g H z h2 hu hs hh hdd ξ η
  have hsz : (H z)ᵀ = H z := hs.self_of_nhds.eq
  have hhz : (H z)ᴴ = H z := hh.self_of_nhds.eq
  have he : (fun x => (H x)⁻¹) =ᶠ[𝓝 z] fun x => dualGram (H x) :=
    hs.mono fun x hx => by
      show (H x)⁻¹ = (H x)⁻¹ᵀ
      rw [transpose_nonsing_inv, hx.eq]
  have hbar : (mdbar H z η)ᵀ = mdbar H z η := by
    rw [← mdbar_transpose]; exact mdbar_congr (hs.mono fun x hx => hx.eq) η
  have hdel : (mdel H z η)ᴴ = mdbar H z η := conjTranspose_mdel hh η
  have key : (conn H z η)ᵀᴴ = (H z)ᵀ⁻¹ * (mdbar H z η)ᵀ := by
    rw [conn, transpose_mul, transpose_transpose, conjTranspose_mul, hdel, transpose_nonsing_inv,
      transpose_transpose, hsz, hbar, conjTranspose_nonsing_inv, hhz]
  rw [curv_congr he, curv_dual h2 hu, curv_eq h2 hu, hdd, transpose_zero, Matrix.mul_zero,
    sub_zero, key, conn, Matrix.mul_assoc, Matrix.mul_assoc]

end GlobalTheory.RealGram
