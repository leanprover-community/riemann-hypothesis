module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOperatorHeckeTQEqUAddVTwist
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.thetaOperator_heckeT_q_eq_U_add_V_twist : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], Algebra.IsAlgebraic ℚ Ω → (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → 1 ≤ N → ∀ (n w d q : ℕ), Odd w → q.Prime → ¬ q ∣ N * l → ((q : Ω))⁻¹ ∈ A → (l : Ω) ∈ A.nonunits → l ≠ 2 → ¬ l ∣ N → d.Coprime N → ∀ b : X.Fn l, b ∈ X.B N l w → ∀ φ φ' : HahnSeries ℚ Ω, IsLat 1 φ → IsLat 1 φ' →
  IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ →
  IsThB X A N l n (X.act l (sgD N l (d * q) : Matrix (Fin 2) (Fin 2) ℤ) b) φ' →
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeT N l q b)) (hq ε q φ + ((q : Ω) ^ (w + 1)) • vq q φ') := by
  first | exact @GlobalTheory.HeckeTh.isThB_heckeT | exact GlobalTheory.HeckeTh.isThB_heckeT | (intros; apply GlobalTheory.HeckeTh.isThB_heckeT <;> assumption)
