module

public import Mathlib.Basic.NNReal.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorsionLift
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
public import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.XiMulNu

@[expose] public section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.ResiduePointLift

theorem exists_algHom_lift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O →
    ∀ (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Flat O A]
    (c : A →ₐ[O] IsLocalRing.ResidueField O), ∃ x : A →ₐ[O] O, ∀ a, IsLocalRing.residue O (x a) = c a := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ hv A _ _ _ _ c
  haveI : IsFractionRing O C := hv.isFractionRing
  haveI : IsIntegrallyClosed O := hv.isIntegrallyClosed
  obtain ⟨ψ, h1, h2⟩ := GlobalTheory.UT.ExactTerm.exists_ringHom_lift C (c : A →+* IsLocalRing.ResidueField O)
    (RingHom.ext fun o => by simp [IsLocalRing.ResidueField.algebraMap_eq])
  refine ⟨{ ψ with commutes' := fun o => RingHom.congr_fun h1 o }, fun a => RingHom.congr_fun h2 a⟩

end GlobalTheory.ResiduePointLift
