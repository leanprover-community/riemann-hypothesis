module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateUnitaryKTypeSameWeight
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe

@[expose] public section

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_conjugate_unitaryKType_sameWeight : ∀ (k : ℕ) (Λ : Fin k → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), IsURepOn (UJset (allPos k)) σ → IsKTypeOf (allPos k) σ Λ ⊤ → ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℂ E) (_ : FiniteDimensional ℂ E) (π : Matrix (Fin k) (Fin k) ℂ → (E →L[ℂ] E)) (J : H →ₛₗ[starRingEnd ℂ] E), Function.Bijective J ∧ IsURepOn (UJset (allPos k)) π ∧ IsKTypeOf (allPos k) π Λ ⊤ ∧ ∀ g u, π g (J u) = J (σ (g.map star) u) := by
  first | exact @GlobalTheory.ConjugateType.exists_conjugate_type | exact GlobalTheory.ConjugateType.exists_conjugate_type | (intros; apply GlobalTheory.ConjugateType.exists_conjugate_type <;> assumption)
