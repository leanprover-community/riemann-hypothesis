module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapLine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotSquareLinearFactorOfPencilLineDiscriminantNeZ
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc

theorem _root_.GlobalTheory.T.not_square_linear_factor_of_pencilLineDiscriminant_ne_zero : ∀ (F K : Type) [Field F] [Field K] [Algebra F K] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F) (s : Fin D → Fin N → K) (a b : Fin N → K), 1 ≤ δ → (GlobalTheory.PencilDisc.line s a b f).natDegree ≤ δ → (GlobalTheory.PencilDisc.line s a b f).coeff δ = MvPolynomial.aeval (GlobalTheory.HSChoice.join s b) f → GlobalTheory.PencilDisc.disc δ s a b f ≠ 0 → GlobalTheory.HSChoice.NoSquare (GlobalTheory.HSChoice.spec s f) := by
  first | exact @GlobalTheory.PencilDisc.noSquare_spec_of_disc_ne_zero | exact GlobalTheory.PencilDisc.noSquare_spec_of_disc_ne_zero | (intros; apply GlobalTheory.PencilDisc.noSquare_spec_of_disc_ne_zero <;> assumption)
