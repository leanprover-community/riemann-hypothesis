module

public import Development.AbelianVarietyTheory.Definitions.Divisors.XiMulNu
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.DualLattices.CotangentSurjective

@[expose] public section

open ReciprocityTheory.PGsh.Up GlobalTheory.Sandwich Matrix

theorem _root_.GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ ε : PreTilt O p, IsPrimitiveRoot (root ε).untilt p → IsDomain (Ainf p O) ∧ IsLocalRing (Ainf p O) ∧ RingHom.ker (WittVector.fontaineTheta O p) = Ideal.span {xi ε} ∧ Function.Surjective (WittVector.fontaineTheta O p) ∧ WittVector.fontaineTheta O p (nu ε) ≠ 0 ∧ xi ε ≠ 0 ∧ (∀ x : Ainf p O, x ≠ 0 → ∃ (N : ℕ) (y : Ainf p O), x = xi ε ^ N * y ∧ WittVector.fontaineTheta O p y ≠ 0) := by
  first | exact @GlobalTheory.AinfXi.ainf_local_xi_order | exact GlobalTheory.AinfXi.ainf_local_xi_order | (intros; apply GlobalTheory.AinfXi.ainf_local_xi_order <;> assumption)
