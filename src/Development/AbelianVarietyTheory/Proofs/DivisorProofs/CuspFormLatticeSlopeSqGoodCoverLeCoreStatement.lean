module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormLatticeSlopeSqGoodCoverLeCore
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.cuspFormLattice_slope_sq_goodCover_le_core : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (S : Set (T.R j)), LawsJ T → InR D j → Y.Good e o → Dom a n → S ⊆ (T.cuspA j a n : Set (T.R j)) → GoodW (T.U j) (xiR D) (T.V j) (T.dict j) (wtZ a n) → GoodW Y.U (xiR D) (fun _ => D.sp.W j) Y.dict (wtZ a n) → slope_sq (Y.nrm (wtZ a n)) (Y.latOver (wtZ a n) S) - 2 * (Real.log |(discr Y.d.c₂.F : ℝ)| / Module.finrank ℚ Y.d.c₂.F) ≤ slope_sq (normW (T.U j) (xiR D) (T.V j) (T.dict j) (wtZ a n)) (latW (T.U j) (wtZ a n) ⊓ ((Submodule.span T.Q.c.F S).comap (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)).subtype).restrictScalars (𝓞 T.Q.c.F)) := by
  exact @GlobalTheory.CoreRing.slope_sq_latOver_sub_le
