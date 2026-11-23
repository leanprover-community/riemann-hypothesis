module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.GalBasic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.kolEx :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M F n a : ℕ) [NeZero M], F * n ≠ 0 → ∀ (ζ : Ω), IsPrimitiveRoot ζ M → ∀ δ : G ℚ Ω, Pows M a δ → ∀ y : Ω, y ≠ 0 → (∀ h ∈ fixMu ℚ Ω (F * n), h y = y) →
    (∀ g ∈ fixMu ℚ Ω F, ∃ z : Ω, (∀ h ∈ fixMu ℚ Ω (F * n), h z = z) ∧ z ^ M = g y / y) → ∃ κ : G ℚ Ω → ZMod M, IsKol M F n ζ δ a y κ := by
  intro Ω _ _ _ M F n a _ hFn ζ hζ δ hδ y hy hfix hz
  have hM : M ≠ 0 := NeZero.ne M
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨Y, hY⟩ := IsAlgClosed.exists_pow_nat_eq y (Nat.pos_of_ne_zero hM)
  have hcomm := (galBasic Ω (F * n) hFn).2.2.2.2.2.1 y hfix
  have hroot : ∀ g ∈ fixMu ℚ Ω F, ∀ z : Ω, z ^ M = g y / y →
      ∃ k : ℕ, k < M ∧ ζ ^ k = g (opP δ a Y) / opP δ a Y / opP δ a z := by
    intro g _ z hz'
    apply hζ.eq_pow_of_pow_eq_one
    have hgy : g y ≠ 0 := by simpa using hy
    have hdy : δ y ≠ 0 := by simpa using hy
    have hdgy : δ (g y) ≠ 0 := by simpa using hgy
    unfold opP
    calc (g (δ Y / Y ^ a) / (δ Y / Y ^ a) / (δ z / z ^ a)) ^ M
        = g (δ (Y ^ M)) / (g (Y ^ M)) ^ a / (δ (Y ^ M) / (Y ^ M) ^ a) / (δ (z ^ M) / (z ^ M) ^ a) := by
          simp only [map_div₀, map_pow, div_pow]
          ring
      _ = 1 := by
          rw [hY, hz', map_div₀ δ, hcomm g δ]
          field_simp
          rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero a hy)]
  classical
  choose! zf hzf using hz
  have hk := fun g hg => hroot g hg (zf g) (hzf g hg).2
  choose! kf hkf using hk
  refine ⟨fun g => (kf g : ZMod M), Y, hY, fun g hg => ⟨zf g, (hzf g hg).1, (hzf g hg).2, ?_⟩⟩
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hkf g hg).1]
  exact (hkf g hg).2
