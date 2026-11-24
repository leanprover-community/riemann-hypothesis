module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.CentreFin

variable {n r : ℕ}

variable {J : Matrix (Fin n) (Fin n) ℂ} {X Y : Matrix (Fin n) (Fin r) ℂ}

theorem dual_swap (hJ : Jᴴ = J) (hxy : Xᴴ * J * Y = 1) : Yᴴ * J * X = 1 := by
  have := congrArg conjTranspose hxy
  rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ, conjTranspose_one, ← Matrix.mul_assoc] at this

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem map_cT_emb (h : IsCMExt F E σ) (τ : E →+* ℂ) {a b : ℕ} (C : Matrix (Fin a) (Fin b) E) :
    (Formalism.UG.cT (σ : E →+* E) C).map τ = (C.map τ)ᴴ :=
  Matrix.ext fun i j => h.2.2.2 τ (C j i)

theorem frame_emb (h : IsCMExt F E σ) {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}
    (hW : IsWittFrame σ J X Y) (τ : E →+* ℂ) :
    (X.map τ)ᴴ * J.map τ * X.map τ = 0 ∧ (Y.map τ)ᴴ * J.map τ * Y.map τ = 0 ∧ (X.map τ)ᴴ * J.map τ * Y.map τ = 1 := by
  simp only [← map_cT_emb h, ← Matrix.map_mul]
  rw [hW.xx, hW.yy, hW.xy]
  exact ⟨Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)⟩

end Global

end GlobalTheory.CentreFin

end
