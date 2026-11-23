module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSimultaneousDiagonalisationPosDefHermitianStatement
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight

@[expose] public section

open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix
namespace GlobalTheory.HSAmp

theorem star_mulVec_single_dot (ι : Type) [Fintype ι] [DecidableEq ι]
    (T M : Matrix ι ι ℂ) (i : ι) :
    star (T *ᵥ Pi.single i 1) ⬝ᵥ M *ᵥ (T *ᵥ Pi.single i 1) = (Tᴴ * M * T) i i := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  simp [Matrix.mulVec_single, dotProduct_single]

theorem det_re_le_pow_mul_det_re (ι : Type) [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ)
    (κ : ℝ) (hA : A.PosDef) (hB : B.PosDef)
    (hle : ∀ c : ι → ℂ, (star c ⬝ᵥ A *ᵥ c).re ≤ κ * (star c ⬝ᵥ B *ᵥ c).re) :
    A.det.re ≤ κ ^ Fintype.card ι * B.det.re := by
  obtain ⟨T, d, hT, hTB, hTA⟩ := GlobalTheory.T.exists_simultaneous_diagonalisation_posDef_hermitian ι B A hB hA.isHermitian
  have hTu : IsUnit T := (Matrix.isUnit_iff_isUnit_det T).2 hT
  have hinj : Function.Injective T.mulVec := Matrix.mulVec_injective_iff_isUnit.2 hTu

  have hcol : ∀ i, T *ᵥ Pi.single i 1 ≠ 0 := by
    intro i h
    have : Pi.single i (1 : ℂ) = 0 := hinj (by rw [h, Matrix.mulVec_zero])
    simpa using congrFun this i
  have hBi : ∀ i, star (T *ᵥ Pi.single i 1) ⬝ᵥ B *ᵥ (T *ᵥ Pi.single i 1) = 1 := by
    intro i; rw [star_mulVec_single_dot, hTB]; simp
  have hAi : ∀ i, star (T *ᵥ Pi.single i 1) ⬝ᵥ A *ᵥ (T *ᵥ Pi.single i 1) = (d i : ℂ) := by
    intro i; rw [star_mulVec_single_dot, hTA]; simp
  have hdpos : ∀ i, 0 < d i := by
    intro i
    have h := hA.dotProduct_mulVec_pos (hcol i)
    rw [hAi] at h
    exact_mod_cast h
  have hdle : ∀ i, d i ≤ κ := by
    intro i
    have h := hle (T *ᵥ Pi.single i 1)
    rw [hAi, hBi] at h
    simpa using h

  set t := T.det
  have hn : (Complex.normSq t : ℂ) = star t * t := Complex.normSq_eq_conj_mul_self
  have hdetB : (Complex.normSq t : ℂ) * B.det = 1 := by
    have := congrArg Matrix.det hTB
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at this
    rw [hn, ← this]; ring
  have hdetA : (Complex.normSq t : ℂ) * A.det = ((∏ i, d i : ℝ) : ℂ) := by
    have := congrArg Matrix.det hTA
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_diagonal] at this
    rw [hn, Complex.ofReal_prod, ← this]; ring
  have hpos : 0 < Complex.normSq t := Complex.normSq_pos.2 hT.ne_zero
  have hBre : Complex.normSq t * B.det.re = 1 := by
    have := congrArg Complex.re hdetB
    simpa [Complex.re_ofReal_mul] using this
  have hAre : Complex.normSq t * A.det.re = ∏ i, d i := by
    have := congrArg Complex.re hdetA
    rwa [Complex.re_ofReal_mul, Complex.ofReal_re] at this
  have hprod : ∏ i, d i ≤ κ ^ Fintype.card ι := by
    calc ∏ i, d i ≤ ∏ _i : ι, κ :=
          Finset.prod_le_prod₀ (fun i _ => (hdpos i).le) (fun i _ => hdle i)
      _ = κ ^ Fintype.card ι := by simp
  refine le_of_mul_le_mul_left ?_ hpos
  calc Complex.normSq t * A.det.re = ∏ i, d i := hAre
    _ ≤ κ ^ Fintype.card ι := hprod
    _ = Complex.normSq t * (κ ^ Fintype.card ι * B.det.re) := by
        rw [mul_left_comm, hBre, mul_one]

end GlobalTheory.HSAmp
