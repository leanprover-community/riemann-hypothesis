module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarishChandraTypeDualWeylModuleFockNorm
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

@[expose] public section


theorem _root_.GlobalTheory.T.exists_harishChandraType_dualWeylModuleFockNorm : ∀ (n : ℕ) (lam : Formalism.BasicNotions.DomWeight n), ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (e : H →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ), Formalism.MainNotions.S.IsHCTypeU n (fun i => (lam.w i : ℝ) + ((Formalism.BasicNotions.rhoVec n i : ℚ) : ℝ)) π ∧ Function.Injective e ∧ (∀ x, e x ∈ Formalism.BasicNotions.nablaSq ℂ n lam) ∧ ∀ g : GL (Fin n) ℂ, (g : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ → ∀ x, e (π (g : Matrix (Fin n) (Fin n) ℂ) x) = Formalism.BasicNotions.sqAct ℂ n lam g (e x) := by
  first | exact @GlobalTheory.NablaType.exists_isHCTypeU_nablaSq | exact GlobalTheory.NablaType.exists_isHCTypeU_nablaSq | (intros; apply GlobalTheory.NablaType.exists_isHCTypeU_nablaSq <;> assumption)
