module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopFormNegativePartEqZeroOfNonnegOnOpen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial MeasureTheory
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric


theorem _root_.GlobalTheory.T.chernTopForm_negativePart_eq_zero_of_nonneg_on_open : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ} (E : Fr (ratOf X) m 0) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) (R : MvPolynomial (ι × ℕ) ℝ), (∀ y ∈ ptsIn X.str σ O, ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∀ A ∈ E.S (under y), 0 ≤ chernTop R (fun w => H A (c.e.symm w)) (c.e y)) → chernTopPart E H R (-1) (ptsIn X.str σ O) = 0 := by
  first | exact @GlobalTheory.chernTopPart_neg_eq_zero_of_nonneg | exact GlobalTheory.chernTopPart_neg_eq_zero_of_nonneg | (intros; apply GlobalTheory.chernTopPart_neg_eq_zero_of_nonneg <;> assumption)
