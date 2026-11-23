module

public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.GramMat
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.GramMatrixPosDefConjugate
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open NumberField TensorProduct GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.Lines Matrix
open scoped ComplexOrder nonZeroDivisors

theorem _root_.GlobalTheory.T.gram_matrix_pos_def_conjugate : ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L) (i : ℕ) (f : Fin i → B.carrier), LinearIndependent (𝓞 L) f → (∀ σ, (gramMat B σ f).PosDef) ∧ ∀ σ, gramMat B (ComplexEmbedding.conjugate σ) f = (gramMat B σ f).map (starRingEnd ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lines.gramMat_posDef_and_conj | exact GlobalTheory.CompanionTheory.Ar.Lines.gramMat_posDef_and_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Lines.gramMat_posDef_and_conj <;> assumption)
