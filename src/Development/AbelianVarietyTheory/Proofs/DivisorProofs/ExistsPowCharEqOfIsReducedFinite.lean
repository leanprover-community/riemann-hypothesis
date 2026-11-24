module

public import Mathlib.FieldTheory.Perfect
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsCounitDerivationCounitComp
public import Mathlib.Algebra.CharP.Algebra

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem GlobalTheory.exists_pow_char_eq_of_isReduced_finite : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] [IsReduced A], ∀ a : A, ∃ b : A, a = b ^ p := by
  intro p _ k _ _ _ A _ _ _ _ a
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  haveI : PerfectField k := PerfectRing.toPerfectField k p
  let e := IsArtinianRing.equivPi A
  have key : ∀ I : MaximalSpectrum A, ∃ c : A ⧸ I.asIdeal, e a I = c ^ p := by
    intro I
    haveI : I.asIdeal.IsMaximal := I.isMaximal
    letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : Module.Finite k (A ⧸ I.asIdeal) := Module.Finite.trans A (A ⧸ I.asIdeal)
    haveI : Algebra.IsAlgebraic k (A ⧸ I.asIdeal) := Algebra.IsAlgebraic.of_finite k _
    haveI : PerfectField (A ⧸ I.asIdeal) := Algebra.IsAlgebraic.perfectField k
    haveI : CharP (A ⧸ I.asIdeal) p :=
      charP_of_injective_algebraMap (algebraMap k (A ⧸ I.asIdeal)).injective p
    haveI : PerfectRing (A ⧸ I.asIdeal) p := PerfectField.toPerfectRing p
    obtain ⟨c, hc⟩ := surjective_frobenius (A ⧸ I.asIdeal) p (e a I)
    exact ⟨c, by rw [← hc, frobenius_def]⟩
  choose c hc using key
  refine ⟨e.symm c, e.injective ?_⟩
  rw [map_pow, AlgEquiv.apply_symm_apply]
  funext I
  rw [hc I, Pi.pow_apply]
