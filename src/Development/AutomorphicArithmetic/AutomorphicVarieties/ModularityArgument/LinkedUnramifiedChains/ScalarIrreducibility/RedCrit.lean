module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
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
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FlipTwoThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

theorem UpperTheory.V.J.redCrit :
    ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (q : Ideal A), q.IsPrime → (∀ P ∈ associatedPrimes A A, P ≤ q → P ∈ minimalPrimes A) →
        (∀ P ∈ minimalPrimes A, P ≤ q → ∀ a ∈ P, ∃ s ∉ P, s * a = 0) → ∀ a : A, (∀ P : Ideal A, P.IsPrime → P ≤ q → a ∈ P) → ∃ s ∉ q, s * a = 0 := by
  intro A _ _ q hq h1 h2 a ha
  by_contra hcon
  push_neg at hcon
  let N : Submodule A A := Submodule.span A {a}
  have hann : ∀ x, x ∈ Module.annihilator A N ↔ x * a = 0 := by
    intro x
    rw [Module.mem_annihilator]
    constructor
    · intro h
      exact congrArg Subtype.val (h ⟨a, Submodule.mem_span_singleton_self a⟩)
    · intro h m
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp m.2
      apply Subtype.ext
      change x * (m : A) = 0
      rw [← hc, smul_eq_mul, mul_left_comm, h, mul_zero]
  have hle : Module.annihilator A N ≤ q := by
    intro x hx
    by_contra hxq
    exact hcon x hxq ((hann x).mp hx)
  obtain ⟨P, hP, hPq⟩ := Ideal.exists_minimalPrimes_le hle
  have hPass : P ∈ associatedPrimes A N :=
    Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes A N hP
  have hPA : P ∈ associatedPrimes A A :=
    associatedPrimes.subset_of_injective N.injective_subtype hPass
  have hPmin := h1 P hPA hPq
  obtain ⟨s, hsP, hs⟩ := h2 P hPmin hPq a (ha P hPmin.1.1 hPq)
  exact hsP (hP.1.2 ((hann s).mpr hs))
