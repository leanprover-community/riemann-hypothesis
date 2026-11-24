module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.RedRoot
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

theorem UpperTheory.V.Stick.splitInj :
    ∀ (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (p : ℕ) [Fact p.Prime] (π : 𝓞 K →+* ZMod p), p.Coprime M →
    Function.Injective (conjI M K (RingHom.ker π)) := by
  intro M _ K _ _ _ p _ π hp a b hab
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hz := (IsCyclotomicExtension.zeta_spec M ℚ K).toInteger_isPrimitiveRoot
  obtain ⟨hπz, -⟩ := redRoot (𝓞 K) p π M _ hp hz
  have key : ∀ x : 𝓞 K, π (sgO M K a x) = π (sgO M K b x) := by
    intro x
    have h1 : x - ((π (sgO M K a x)).val : 𝓞 K) ∈ conjI M K (RingHom.ker π) a := by
      simp only [conjI, Ideal.mem_comap, RingHom.mem_ker, map_sub, map_natCast,
        ZMod.natCast_zmod_val, sub_self]
    rw [hab] at h1
    simp only [conjI, Ideal.mem_comap, RingHom.mem_ker, map_sub, map_natCast,
      ZMod.natCast_zmod_val, sub_eq_zero] at h1
    exact h1.symm
  have h2 := key (IsCyclotomicExtension.zeta_spec M ℚ K).toInteger
  rw [sgO_apply _ _ _ hz.pow_eq_one, sgO_apply _ _ _ hz.pow_eq_one, map_pow, map_pow] at h2
  exact Units.ext (ZMod.val_injective _ (hπz.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h2))
