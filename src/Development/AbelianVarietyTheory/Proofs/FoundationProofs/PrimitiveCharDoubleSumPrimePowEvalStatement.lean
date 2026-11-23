module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Integral
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveCharDoubleSumPrimePowEval
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

@[expose] public section

open GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.primitiveChar_doubleSum_primePow_eval : ∀ (p m : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharZero K] (ψ : DirichletCharacter K (p ^ m)) (ζm : K), 1 ≤ m → ψ.IsPrimitive → IsPrimitiveRoot ζm (p ^ m) → ∀ n₁ n₂ d d' : ℤ, ¬ ((p : ℤ) ∣ n₁ ∧ (p : ℤ) ∣ n₂) → (∀ u : (ZMod (p ^ m))ˣ, (d : ZMod (p ^ m)) = u * (-(n₂ : ZMod (p ^ m))) → (d' : ZMod (p ^ m)) = u * (n₁ : ZMod (p ^ m)) → ∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - (n₂ : ZMod (p ^ m)) * a) * ζm ^ ((a.val : ℤ) * d + (b.val : ℤ) * d') = (p : K) ^ m * ψ⁻¹ (u : ZMod (p ^ m)) * gaussS p m ψ ζm) ∧ ((¬ ∃ u : (ZMod (p ^ m))ˣ, (d : ZMod (p ^ m)) = u * (-(n₂ : ZMod (p ^ m))) ∧ (d' : ZMod (p ^ m)) = u * (n₁ : ZMod (p ^ m))) → ∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - (n₂ : ZMod (p ^ m)) * a) * ζm ^ ((a.val : ℤ) * d + (b.val : ℤ) * d') = 0) := by
  first | exact @GlobalTheory.KummerEisensteinGalois.ChSum.charSum | exact GlobalTheory.KummerEisensteinGalois.ChSum.charSum | (intros; apply GlobalTheory.KummerEisensteinGalois.ChSum.charSum <;> assumption)
