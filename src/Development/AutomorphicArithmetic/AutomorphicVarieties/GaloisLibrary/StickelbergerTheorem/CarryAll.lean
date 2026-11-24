module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.CarryPrime
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.DegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.ImportsBis
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

theorem UpperTheory.V.Stick.carryAll :
    ∀ (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (c : ClassGroup (𝓞 K)) (a b : ZMod M),
    ∏ t : (ZMod M)ˣ, clMap (sg M K t)⁻¹.toRingEquiv c ^ carry M (a * t) (b * t) = 1 := by
  intro M _ K _ _ _ c a b
  set S : Set (HeightOneSpectrum (𝓞 K)) := {v | v.asIdeal ∣ Ideal.span {((M : ℕ) : 𝓞 K)}}
  have hM0 : Ideal.span {((M : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast NeZero.ne M
  have hS : S.Finite := Ideal.finite_factors hM0
  obtain ⟨v, hvS, hprime, hvc⟩ := degOne K S hS c
  haveI : Fact (Ideal.absNorm v.asIdeal).Prime := ⟨hprime⟩
  obtain ⟨π, hπ⟩ := (red K (Ideal.absNorm v.asIdeal) v.asIdeal).1 rfl
  have hpv := ((red K (Ideal.absNorm v.asIdeal) v.asIdeal).2 π hπ).2.2.2
  have hcop : (Ideal.absNorm v.asIdeal).Coprime M := by
    rw [Nat.Prime.coprime_iff_not_dvd hprime]
    rintro ⟨k, hk⟩
    apply hvS
    show v.asIdeal ∣ _
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hpv
  rw [← hvc]
  exact carryPrime M K _ π hcop v hπ a b
