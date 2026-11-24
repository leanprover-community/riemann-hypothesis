module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CyclotomicInertiaSpan.CycIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.IneFixRoots
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.PlacesQ
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

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.ineTau :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (q : ℕ), q.Prime → (∀ A : ValuationSubring Ω, Over A q → ∀ b : (ZMod q)ˣ, ∃ t ∈ Ine (F := ℚ) A, Lifts q b t) ∧ ∃ τ : G ℚ Ω, IsTau q τ := by
  intro Ω _ _ _ q hq
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hall : ∀ x : (ZMod q)ˣ, x ∈ B3.pPart q q := by
    intro x
    unfold B3.pPart
    rw [MonoidHom.mem_ker]
    have h : q / q ^ q.factorization q = 1 := by
      rw [hq.factorization_self, pow_one, Nat.div_self hq.pos]
    have hs : Subsingleton (ZMod (q / q ^ q.factorization q))ˣ := by
      rw [h]
      infer_instance
    exact Subsingleton.elim _ _
  have part1 : ∀ A : ValuationSubring Ω, Over A q → ∀ b : (ZMod q)ˣ,
      ∃ t ∈ Ine (F := ℚ) A, Lifts q b t := by
    intro A hA b
    have hA' : A.valuation (q : Ω) < 1 := by
      unfold Over at hA
      exact hA
    have hmap := B1.cycIne Ω q q A hA'
    have hb : b ∈ Subgroup.map (B1.cycN ℚ Ω q) (Ine A) := by
      rw [hmap]
      exact hall b
    obtain ⟨t, ht, htb⟩ := hb
    refine ⟨t, ht, ?_⟩
    unfold Lifts Pows
    exact (B1.cycN_eq_iff ℚ Ω q t b).1 htb
  refine ⟨part1, ?_⟩
  obtain ⟨A, hA⟩ := (B3.placesQ Ω).1 q hq
  obtain ⟨b, hgen⟩ := IsCyclic.exists_generator (α := (ZMod q)ˣ)
  have hA2 : Over A q := by
    unfold Over
    exact hA
  obtain ⟨t, ht, hl⟩ := part1 A hA2 b
  refine ⟨t, ?_⟩
  unfold IsTau
  refine ⟨?_, ?_⟩
  · intro k hk
    unfold fixMu
    intro ζ hζ
    exact ((LDataCardLeFinrank.ineFixRoots ℚ Ω q A hA k hk ζ hζ).2 t ht)
  · unfold GenAt
    exact ⟨b, hgen, hl⟩
