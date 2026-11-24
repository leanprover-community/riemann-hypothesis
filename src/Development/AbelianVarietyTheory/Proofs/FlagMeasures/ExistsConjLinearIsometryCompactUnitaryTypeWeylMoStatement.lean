module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConjLinearIsometryCompactUnitaryTypeWeylMo
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

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

theorem _root_.GlobalTheory.T.exists_conjLinear_isometry_compact_unitary_type_weyl_module : ∀ (k n : ℕ) (h : k = n) (lam : DomWeight n) (u : Fin k → ℝ), (∀ i : Fin k, u i = (lam.w (Fin.cast h i) : ℝ) + ((rhoVec k i : ℚ) : ℝ)) → ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)), IsHCTypeU k u π → ∃ j : W →ₗ⋆[ℂ] MvPolynomial (Fin n × Fin n) ℂ, (∀ ξ, j ξ ∈ delSq ℂ n lam) ∧ (∀ p ∈ delSq ℂ n lam, ∃ ξ, j ξ = p) ∧ (∀ ξ η, normFock lam (j η) (j ξ) = ⟪η, ξ⟫_ℂ) ∧ ∀ g ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ ξ, j (π (g.submatrix (Fin.cast h) (Fin.cast h)) ξ) = (g.det ^ (-lam.detShift)) • Formalism.GradedWeylDivisibility.rowAct ℂ gᴴ (j ξ) := by
  first | exact @GlobalTheory.WeylConjType.exists_conj_weyl | exact GlobalTheory.WeylConjType.exists_conj_weyl | (intros; apply GlobalTheory.WeylConjType.exists_conj_weyl <;> assumption)
