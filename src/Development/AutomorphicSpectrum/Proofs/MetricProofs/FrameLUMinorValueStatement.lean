module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameLUMinorValue
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

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan


theorem _root_.GlobalTheory.T.frame_LU_minor_value : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (hh : Ψ → Matrix (Fin N) (Fin N) ℂ) (τ' : Ψ) (a' b' : Fin N) (z : (Σ k, ι k) → ℂ) (A L U : Matrix (Fin N) (Fin N) ℂ), M.IsFrame F → zb ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal zb) → IsBlockDiag j A → (hh τ')⁻¹ * A = L * U → IsBlockDiag j L → IsLowerUni L → IsBlockDiag j U → U.BlockTriangular id → (∀ c ∈ stepCols N j (stepOf N j b'), U c c ≠ 0) → b' < a' → ((a' : ℕ) < N - j ↔ (b' : ℕ) < N - j) → (∀ k, M.blk (τ', stepOf N j b') = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k, z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ A I (stepCols N j (stepOf N j b'))) → lowRead M F zb hh z τ' a' b' = L a' b' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.LowRead.main | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.LowRead.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.LowRead.main <;> assumption)
