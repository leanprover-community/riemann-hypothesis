module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntertwinerOfSameHarishChandraParamUnitary
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section


theorem _root_.GlobalTheory.T.exists_intertwiner_of_same_harishChandraParam_unitary : ∀ (k : ℕ) (u : Fin k → ℝ) (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (π₁ : Matrix (Fin k) (Fin k) ℂ → (H₁ →L[ℂ] H₁)) (π₂ : Matrix (Fin k) (Fin k) ℂ → (H₂ →L[ℂ] H₂)), Formalism.MainNotions.S.IsHCTypeU k u π₁ → Formalism.MainNotions.S.IsHCTypeU k u π₂ → ∃ A : H₁ ≃ₗ[ℂ] H₂, ∀ g ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ x, A (π₁ g x) = π₂ g (A x) := by
  first | exact @GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU | exact GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU | (intros; apply GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU <;> assumption)
