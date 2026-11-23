module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyComplexOfSheafCocycleClassProperties
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.HCEqv

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R) (E E' : Spc) (f : E ⟶ E'),
    Eqv R f F ↔ SurjH ((HC R F).map f.op) ∧ InjH ((HC R F).map f.op) := by
  intro R _ F E E' f
  obtain ⟨-, cl, hsurj, heq, hzero, hpull⟩ := GlobalTheory.EtC.HCElements.main R F
  constructor
  · intro hf
    refine ⟨fun n z hz => ?_, fun n c hc ⟨y, hy⟩ => ?_⟩
    · obtain ⟨x, hx⟩ := (hf n).2 (cl E n z hz)
      obtain ⟨c, hc, rfl⟩ := hsurj E' n x
      obtain ⟨h, hp⟩ := hpull E E' f n c hc
      rw [hp, heq] at hx
      obtain ⟨y, hy⟩ := hx
      exact ⟨c, y, hc, hy⟩
    · obtain ⟨h, hp⟩ := hpull E E' f n c hc
      have h0 : cl E n (((HC R F).map f.op).f n c) h = 0 := (hzero E n _ h).2 ⟨y, hy⟩
      rw [← hp] at h0
      have : cl E' n c hc = 0 := (hf n).1 (h0.trans (map_zero _).symm)
      obtain ⟨b, hb⟩ := (hzero E' n c hc).1 this
      exact ⟨b, hb.symm⟩
  · rintro ⟨hS, hI⟩ n
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨c, hc, rfl⟩ := hsurj E' n x
      obtain ⟨h, hp⟩ := hpull E E' f n c hc
      rw [hp, hzero] at hx
      obtain ⟨b, hb⟩ := hI n c hc hx
      exact (hzero E' n c hc).2 ⟨b, hb.symm⟩
    · intro x
      obtain ⟨z, hz, rfl⟩ := hsurj E n x
      obtain ⟨c, y, hc, hcy⟩ := hS n z hz
      obtain ⟨h, hp⟩ := hpull E E' f n c hc
      refine ⟨cl E' n c hc, ?_⟩
      rw [hp, heq]
      exact ⟨y, hcy⟩

end GlobalTheory.EtC.HCEqv
