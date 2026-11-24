module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
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
public import Mathlib.LinearAlgebra.Matrix.Rank
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GaussS

@[expose] public section

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR.G

variable {m n : ℕ}

theorem det_gram_eq_zero (hmn : m < n) (x : Fin m → Fin n → ℂ) : (gramX (fun _ : Fin m => true) x).det = 0 := by
  have hg : gramX (fun _ : Fin m => true) x = (Matrix.of x)ᴴ * Matrix.of x := by
    ext i j
    simp [gramX, evX, Qp, Qb, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hg]
  by_contra hne
  have hu : IsUnit ((Matrix.of x)ᴴ * Matrix.of x) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hne)
  have h1 := Matrix.rank_of_isUnit _ hu
  have h2 := Matrix.rank_mul_le_right (Matrix.of x)ᴴ (Matrix.of x)
  have h3 := Matrix.rank_le_height (Matrix.of x)
  simp only [Fintype.card_fin] at h1 h3
  omega

theorem trace_transpose_mul' (X Y : Matrix (Fin n) (Fin n) ℂ) : (Xᵀ * Y).trace = (Yᵀ * X).trace := by
  rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]

end PositivityTheory.Rg.Sw.HSt.L3
