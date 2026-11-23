module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isFrac_transition : ∀ (A A' : Type) [CommRing A] [CommRing A'] (k : A →+* A') (N : Type) [AddCommGroup N] [Module A N] (N' : Type) [AddCommGroup N'] [Module A' N'] (τ : N →ₛₗ[k] N') (t : A) (t' : A') (a : ℕ) (y : LocalizedModule (Submonoid.powers t) N) (y' : LocalizedModule (Submonoid.powers t') N') (z m : N) (z' n : N') (i j : ℕ), IsFrac t y z a → IsFrac t y m i → IsFrac t' y' z' a → IsFrac t' y' n j → t' ^ a • τ z = k t ^ a • z' → ∃ r : ℕ, (k t * t') ^ r • (t' ^ j • τ m - k t ^ i • n) = 0 := by
  intro A A' _ _ k N _ _ N' _ _ τ t t' a y y' z m z' n i j h1 h2 h3 h4 h5
  unfold IsFrac at h1 h2 h3 h4
  obtain ⟨⟨_, r₁, rfl⟩, e1⟩ := LocalizedModule.mk_eq.1 (h1.symm.trans h2)
  obtain ⟨⟨_, r₂, rfl⟩, e2⟩ := LocalizedModule.mk_eq.1 (h3.symm.trans h4)
  simp only [Submonoid.smul_def] at e1 e2
  have e3 := congrArg τ e1
  simp only [map_smulₛₗ, map_pow] at e3
  refine ⟨r₁ + r₂ + a, ?_⟩
  linear_combination (norm := skip) (-(k t ^ r₂ * t' ^ (r₁ + r₂ + a) * t' ^ j)) • e3
    + (k t ^ (r₂ + r₁ + i) * t' ^ (r₁ + r₂ + j)) • h5
    + (k t ^ (r₁ + r₂ + a + i) * t' ^ r₁) • e2
  match_scalars <;> ring

end GlobalTheory.BSP
