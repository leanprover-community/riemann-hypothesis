module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitFrameEqOrthonormalMulTriangular
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt
import Formalism.LocalToGlobal.ProjectiveLattices.JFDFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.unitFrame_eq_orthonormal_mul_triangular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 : ℕ) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E), (∀ a b, cc (Gm a b) = Gm b a) → (∀ x ∈ GG Ψ Gm p0, (∀ τ i, ‖dmin Gm x τ i‖ = 1) → ∃ x₀ : Frame Ψ r, ∃ b ∈ Bor Ψ r, (∀ τ : Ψ, gram τ.1 Gm (mat x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ (∀ τ i, ‖b τ i i‖ = 1) ∧ x = rmul x₀ b) ∧ (∀ x₀ : Frame Ψ r, (∀ τ : Ψ, gram τ.1 Gm (mat x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) → x₀ ∈ GG Ψ Gm p0 ∧ ∀ τ i, ‖dmin Gm x₀ τ i‖ = 1) ∧ ∀ (τ : E →+* ℂ) (u x₀ : Matrix (Fin r) (Fin r) ℂ), uᵀ * Gm.map τ * u.map (starRingEnd ℂ) = Gm.map τ → gram τ Gm (u * x₀) = gram τ Gm x₀ := by
  first | exact @GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular | exact GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular | (intros; apply GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular <;> assumption)
