module

public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDualBasisOfUnimodularLatticeAtPrime
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
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero

@[expose] public section

open GlobalTheory.MomN Formalism.L2.Ker.JMB
open scoped ComplexConjugate

theorem _root_.GlobalTheory.T.exists_dualBasis_of_unimodular_lattice_at_prime : ∀ (q : ℕ) [Fact q.Prime] (g : ℕ) (S : Setup g) (r : ℕ) (b : Fin r → Fin g → ℂ), S.Ok → S.NNBasis q b → ∃ (s : ℕ) (c : Fin r → Fin g → ℂ), Nat.Coprime s q ∧ (∀ j, c j ∈ S.La) ∧ (∀ i j, beta S.d S.Hm (c j) (b i) = if i = j then (s : ℂ) else 0) ∧ ∀ x ∈ S.La, (s : ℂ) • x = ∑ j, beta S.d S.Hm x (b j) • c j := by
  first | exact @GlobalTheory.MomDual.dual_basis | exact GlobalTheory.MomDual.dual_basis | (intros; apply GlobalTheory.MomDual.dual_basis <;> assumption)
