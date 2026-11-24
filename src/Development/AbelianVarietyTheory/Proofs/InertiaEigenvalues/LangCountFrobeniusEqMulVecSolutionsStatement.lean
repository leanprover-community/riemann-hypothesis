module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LangCountFrobeniusEqMulVecSolutions
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

@[expose] public section

open GlobalTheory.PMonE

theorem _root_.GlobalTheory.T.lang_count_frobenius_eq_mulVec_solutions : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e : ℕ), 0 < e → ∀ A : Matrix m m F, (∀ i j, ‖A i j‖ ≤ 1) → A.det ≠ 0 → (∀ x : m → F, (∀ i, x i ^ p ^ e = A.mulVec x i) → Integral x) ∧ Nat.card {x : m → F // ∀ i, x i ^ p ^ e = A.mulVec x i} = (p ^ e) ^ Fintype.card m := by
  first | exact @GlobalTheory.PMonE.langCount | exact GlobalTheory.PMonE.langCount | (intros; apply GlobalTheory.PMonE.langCount <;> assumption)
