module

public import Mathlib.Order.CompletePartialOrder
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.Minkowski
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.PlacesQ
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CyclotomicInertiaSpan.OnePrimeOfTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.B1

theorem UpperTheory.V.B1.ineSpan :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N : Subgroup (G ℚ Ω)) (S : Finset ℕ) (B : ℕ → ValuationSubring Ω), IsOpen (N : Set (G ℚ Ω)) → commutator (G ℚ Ω) ≤ N →
    (∀ p ∈ S, p.Prime ∧ (B p).valuation (p : Ω) < 1) →
    (∀ B' : ValuationSubring Ω, (∀ p ∈ S, ¬ B'.valuation (p : Ω) < 1) → Ine (F := ℚ) B' ≤ N) → N ⊔ (⨆ p ∈ S, Ine (F := ℚ) (B p)) = ⊤ := by
  intro Ω _ _ _ N S B ho hc hB hI
  have hle : ∀ p ∈ S, Ine (F := ℚ) (B p) ≤ N ⊔ (⨆ p ∈ S, Ine (F := ℚ) (B p)) := fun p hp =>
    (le_iSup₂ (f := fun p (_ : p ∈ S) => Ine (F := ℚ) (B p)) p hp).trans le_sup_right
  have hN : N ≤ N ⊔ (⨆ p ∈ S, Ine (F := ℚ) (B p)) := le_sup_left
  generalize N ⊔ (⨆ p ∈ S, Ine (F := ℚ) (B p)) = M at hle hN
  have hn : M.Normal := Subgroup.Normal.of_commutator_le _ (hc.trans hN)
  refine B3.minkowski Ω M hn (Subgroup.isOpen_mono hN ho) fun B' => ?_
  by_cases h : ∀ p ∈ S, ¬ B'.valuation (p : Ω) < 1
  · exact (hI B' h).trans hN
  · push Not at h
    obtain ⟨p, hp, hv⟩ := h
    obtain ⟨g, hg⟩ := (B3.placesQ Ω).2.2 p (B p) B' (hB p hp).1 (hB p hp).2 hv
    intro x hx
    have := hn.conj_mem _ (hle p hp (hg x hx)) g
    simpa [mul_assoc] using this
