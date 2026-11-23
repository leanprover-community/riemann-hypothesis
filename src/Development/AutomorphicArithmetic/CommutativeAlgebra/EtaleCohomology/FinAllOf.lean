module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.LocFacts
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Final
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.QuasiCompactOfProj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ResidueExistence.ResEx
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.NormLtOneOfIrreducible
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

@[expose] public section



set_option backward.isDefEq.respectTransparency false

open CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison

theorem UpperTheory.Ru.crystallineComparison.finAll_of :
    (∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] (r : Res l K) (f : ℕ), 0 < f → CIn l K r f) → UpperTheory.Gal.crystallineComparison.Br.FinAll := by
  intro h l _ K _ _ _ f hf hc ϖ hϖ M hM n j T hr hPt A hA B₀
  obtain ⟨r⟩ := UpperTheory.Gal.CD.resEx l K
  have hx : ∀ x : r.k, x ^ l ^ f = x := by
    have hker : RingHom.ker r.ρ = IsLocalRing.maximalIdeal (OK l K) := by
      have hm : (RingHom.ker r.ρ).IsMaximal := RingHom.ker_isMaximal_of_surjective r.ρ r.surj
      exact IsLocalRing.eq_maximalIdeal hm
    have e : IsLocalRing.ResidueField (OK l K) ≃+* r.k :=
      (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective r.surj)
    have hcard : Nat.card r.k = l ^ f := by
      rw [← Nat.card_congr e.toEquiv]
      exact hc
    have hfin : Finite r.k :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
    have := Fintype.ofFinite r.k
    intro x
    rw [← hcard, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  exact UpperTheory.Ru.crystallineComparison.final l K r f hf hx (h l K r f hf) ϖ hϖ M hM n j T hr hPt A hA B₀
