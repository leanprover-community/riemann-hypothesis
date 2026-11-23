module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneAbs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.UnramIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContinuousCoboundaries2

@[expose] public section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.sc_disc :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [NumberField K] [Algebra K Ω], Module.finrank ℚ K = 2 → (∀ B : ValuationSubring Ω, B.valuation (l : Ω) < 1 → Ine (F := ℚ) B ≤ galOf ℚ K Ω) → ¬ (l : ℤ) ∣ discr K := by
  intro Ω _ _ _ l _ K _ _ _ h2 hB
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h2⟩
  haveI : IsGalois ℚ K := {}
  have hl : l.Prime := Fact.out
  rw [← (UpperTheory.V.CF.unramIff).2.1 K l hl, (UpperTheory.V.CF.unramIff).1 K l hl]
  intro w hw
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver (F := K) Ω w
  have hv : A.valuation (l : Ω) < 1 := by
    have h := (hA (l : 𝓞 K)).2 hw
    simpa only [map_natCast] using h
  have hI := hB A hv
  rw [← UpperTheory.V.CF.ineAbs ℚ K Ω A w hA, Subgroup.eq_bot_iff_forall]
  rintro _ ⟨σ, hσ, rfl⟩
  have hσ' : ∀ x : K, σ (algebraMap K Ω x) = algebraMap K Ω x := hI hσ
  ext x
  apply (algebraMap K Ω).injective
  show algebraMap K Ω (σ.restrictNormal K x) = algebraMap K Ω x
  rw [AlgEquiv.restrictNormal_commutes]
  exact hσ' x
