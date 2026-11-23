module

public import Formalism.CyclotomicNorms.StatementT
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.RingTheory.Ideal.GoingUp

@[expose] public section

namespace GlobalTheory.RingHomOfIsIntegral

theorem exists_ringHom_of_isIntegral (R : Type) [CommRing R] [CharZero R] [Algebra.IsIntegral ℤ R]
    (l : ℕ) [hl : Fact (Nat.Prime l)] : Nonempty (R →+* AlgebraicClosure (ZMod l)) := by
  have hinj : Function.Injective (algebraMap ℤ R) := (algebraMap ℤ R).injective_int
  have hlp : (Ideal.span {(l : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hl.out.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hl.out)
  obtain ⟨P, -, hP, hPc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := R)
    (Ideal.span {(l : ℤ)}) ⊥ (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      rw [hinj (hx.trans (map_zero _).symm)]
      exact Ideal.zero_mem _)
  have := hP
  have hl0 : ((l : ℕ) : R ⧸ P) = 0 := by
    have h1 : (l : ℤ) ∈ P.comap (algebraMap ℤ R) := by
      change (l : ℤ) ∈ Ideal.under ℤ P
      rw [hPc]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap] at h1
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
    simpa using h1
  have hchar : CharP (R ⧸ P) l := (CharP.charP_iff_prime_eq_zero hl.out).mpr hl0
  let : Algebra (ZMod l) (R ⧸ P) := ZMod.algebra _ l
  have : Algebra.IsIntegral (ZMod l) (R ⧸ P) := ⟨fun x => by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ((Algebra.IsIntegral.isIntegral (R := ℤ) r).map (Ideal.Quotient.mkₐ ℤ P)).tower_top⟩
  exact ⟨(IsAlgClosed.lift (R := ZMod l) (S := R ⧸ P)
    (M := AlgebraicClosure (ZMod l))).toRingHom.comp (Ideal.Quotient.mk P)⟩

theorem nonempty_ringHom : ∀ (l : ℕ) [Fact (Nat.Prime l)],
    Nonempty (↥(integralClosure ℤ ℂ) →+* Formalism.CyclotomicNorms.Fbar l) := by
  intro l _
  exact exists_ringHom_of_isIntegral (integralClosure ℤ ℂ) l

end GlobalTheory.RingHomOfIsIntegral
