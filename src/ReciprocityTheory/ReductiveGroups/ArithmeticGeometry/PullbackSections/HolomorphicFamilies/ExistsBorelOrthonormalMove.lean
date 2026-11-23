module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ProdCastLESucc
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PerpSurj

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Frames

variable {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r)

theorem diagonal_minor_orthonormal {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
  unfold dmin
  rw [hx τ, ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.lminor_diagonal]
  simp [psgn, Finset.prod_range]

theorem norm_diagonal_minor_one {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm x τ i‖ = 1 := by
  rw [diagonal_minor_orthonormal X hx, Complex.norm_real, Real.norm_eq_abs]
  unfold psgn
  rw [Finset.abs_prod]
  apply Finset.prod_eq_one
  intro a _
  unfold sgn
  split_ifs <;> simp

theorem exists_borel_orthonormal_move {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ b ∈ Bor X.Ψ r, rmul x b ∈ X.dom ∧ X.IsOrtho (rmul x b) := by
  refine ⟨ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x, ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem X hx, fun τ => ⟨?_, fun i => ?_⟩,
    ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf X hx⟩
  · show (mat x τ * mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hx τ).1 ((ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem X hx) τ).1
  · rw [diagonal_minor_orthonormal X (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf X hx) τ i, Complex.ofReal_re]
    have h : psgn X.p0 i ≠ 0 := by
      unfold psgn
      rw [Finset.prod_ne_zero_iff]
      intro a _
      unfold sgn
      split_ifs <;> norm_num
    exact mul_self_pos.2 h

end Frames

section Act

variable {dim : (E →+* ℂ) → ℕ}

end Act

end ReciprocityTheory.ChartRestriction.G.PullbackSections
