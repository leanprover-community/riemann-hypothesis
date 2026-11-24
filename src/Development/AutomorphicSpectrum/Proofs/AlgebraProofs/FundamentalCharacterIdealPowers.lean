module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterOrderGenerates
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RiRank
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

import Development.WeilBound.CoreStatements.HodgeTatePoints.RiRank

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open PositivityTheory.HtPt.Ri (wsum wsum_eq mem_xIdeal v_card_sub_one)
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem r_decomp_relay : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable (F := F) AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ m, xIdeal AA.carrier (σ ^ m) = Ideal.span {c m}) → augIdeal AA.carrier = Submodule.span R ((fun m (a : F) => algebraMap R C (c m * (σ ^ m) a)) '' (Finset.Icc 1 (p ^ f - 1) : Set ℕ)) ∧ AA.carrier = Submodule.span R {(1 : F → C)} ⊔ augIdeal AA.carrier ∧ HasColen R v AA.carrier (∏ m ∈ Finset.Icc 1 (p ^ f - 1), v (algebraMap R C (c m))) :=
  @_root_.PositivityTheory.HtPt.Ri.r_decomp

end GlobalTheory.CompanionTheory.Ar.GR
