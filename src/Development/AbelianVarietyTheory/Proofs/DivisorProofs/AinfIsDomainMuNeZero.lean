module

public import Development.AbelianVarietyTheory.Definitions.Divisors.XiMulNu
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps

@[expose] public section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem _root_.GlobalTheory.ainf_isDomain_and_mu_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (_root_.GlobalTheory.Sandwich.root ε).untilt p → IsDomain (_root_.GlobalTheory.Sandwich.Ainf p O) ∧ _root_.GlobalTheory.Sandwich.mu ε ≠ 0 := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hprim
  haveI : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  refine ⟨by unfold _root_.GlobalTheory.Sandwich.Ainf; infer_instance, ?_⟩
  intro h
  unfold _root_.GlobalTheory.Sandwich.mu at h
  have h1 : WittVector.teichmuller p ε = 1 := sub_eq_zero.mp h
  have hε : ε = 1 := by
    have := congrArg (fun x => WittVector.coeff x 0) h1
    simpa [WittVector.teichmuller_coeff_zero] using this
  have hroot : _root_.GlobalTheory.Sandwich.root ε = 1 := by
    unfold _root_.GlobalTheory.Sandwich.root
    rw [hε, map_one]
  rw [hroot, map_one] at hprim
  exact (Fact.out : p.Prime).one_lt.ne' (IsPrimitiveRoot.one_left_iff.mp hprim)

end GlobalTheory
