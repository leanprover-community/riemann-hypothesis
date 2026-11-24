module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InstBorelUK
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

open Matrix
open scoped Kronecker ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)

variable {n : ℕ} {lam : Fin n → ℤ}

theorem cjL_apply (A : Matrix (Ix n lam) (Ix n lam) ℂ) : cjL lam A = sqQ lam * clm lam A * Ring.inverse (sqQ lam) := by
  simp [cjL, mul_assoc]
  rfl

theorem clm_mul' (A B : Matrix (Ix n lam) (Ix n lam) ℂ) : clm lam (A * B) = clm lam A * clm lam B := map_mul _ A B

theorem clm_one' : clm lam (1 : Matrix (Ix n lam) (Ix n lam) ℂ) = 1 := map_one _

theorem cj_mul (hu : IsUnit (sqQ lam)) (A B : Matrix (Ix n lam) (Ix n lam) ℂ) :
    cjL lam A * cjL lam B = cjL lam (A * B) := by
  rw [cjL_apply, cjL_apply, cjL_apply, clm_mul']
  have h : Ring.inverse (sqQ lam) * sqQ lam = 1 := Ring.inverse_mul_cancel _ hu
  calc sqQ lam * clm lam A * Ring.inverse (sqQ lam) * (sqQ lam * clm lam B * Ring.inverse (sqQ lam))
      = sqQ lam * clm lam A * (Ring.inverse (sqQ lam) * sqQ lam) * clm lam B * Ring.inverse (sqQ lam) := by
        simp only [mul_assoc]
    _ = sqQ lam * (clm lam A * clm lam B) * Ring.inverse (sqQ lam) := by rw [h, mul_one]; simp only [mul_assoc]

theorem cj_one (hu : IsUnit (sqQ lam)) : cjL lam 1 = 1 := by
  rw [cjL_apply, clm_one', mul_one]
  exact Ring.mul_inverse_cancel _ hu

theorem lefε_apply (H : Mat n) : lefε n lam H = cjL lam (creL n (cf n H) ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ)) := rfl

theorem lefι_apply (H : Mat n) : lefι n lam H = cjL lam (annL n (cf n H) ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ)) := rfl

theorem lefFr_apply (x : Mat n) : lefFr n lam x = cjL lam (fr0 lam x) := rfl

theorem frame_zero_apply (x : Mat n) : fr0 lam x = gamM (Mt x⁻¹)ᵀ ⊗ₖ rhoW lam x := rfl

end PositivityTheory.RgBcC
