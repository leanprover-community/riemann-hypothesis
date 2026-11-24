module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.EvaluationAtUnitaryOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfRunTh
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.LevShrink
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

private theorem satEig_rev_of_stable {q n : ℕ} {B : Multiset ℂˣ} (hB : B.card = n) (hs : inv B = B)
    (i : Fin (n + 1)) : satEig q n B (i.rev : ℕ) = satEig q n B n * satEig q n B (i : ℕ) := by
  have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
  have h := GlobalTheory.LFun.ConjPlace.satEig_inv_mul (q := q) hB hi
  have hs' : B.map (·⁻¹) = B := hs
  rw [hs'] at h
  have hr : (i.rev : ℕ) = n - (i : ℕ) := by
    rw [Fin.val_rev]; omega
  rw [hr, ← h, mul_comm]

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.hecke_eigenvalues_unitary_one_factor :
    EvaluationAtUnitaryOne := by
  intro E _ _ _ w a b e he B₁ B₂ h₁ h₂ s₁ s₂
  induction he with
  | one => simp [ev2, Ex.ev]
  | step c p =>
    have r₁ := satEig_rev_of_stable (q := qV E w) h₁ s₁ p.1
    have r₂ := satEig_rev_of_stable (q := qV E w) h₂ s₂ p.2
    simp only [ev2, Ex.ev, dEx, Fin.val_last, r₁, r₂]
    ring
  | mul _ _ ih₁ ih₂ =>
    simp only [ev2, Ex.ev] at ih₁ ih₂ ⊢
    rw [ih₁, ih₂, one_mul]
