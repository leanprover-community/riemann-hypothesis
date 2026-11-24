module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHoweDualityIntertwinerUnitaryPairLocal
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

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct InnerProductSpace

theorem _root_.GlobalTheory.T.exists_howeDuality_intertwiner_unitaryPair_local : ∀ (N n : ℕ) (hn : n ≤ N) (ν : Fin N → ℕ) (x₁ x₃ : ℤ) (Λ : Fin n → ℝ) (Λ' : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H'] (σ' : Matrix (Fin N) (Fin N) ℂ → (H' →L[ℂ] H')), Antitone ν → (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) → (∀ a, Λ a = -(x₃ : ℝ) + ν (Fin.castLE hn a)) → (∀ b, Λ' b = (x₁ : ℝ) + ν b) → Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos n)) σ → Formalism.MainNotions.S.IsKTypeOf (Formalism.MainNotions.S.allPos n) σ Λ ⊤ → Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos N)) σ' → Formalism.MainNotions.S.IsKTypeOf (Formalism.MainNotions.S.allPos N) σ' Λ' ⊤ → ∃ I : MvPolynomial (Fin N × Fin n) ℂ →ₗ[ℂ] H →ₗ[ℂ] H', I ≠ 0 ∧ ∀ h ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos N), ∀ g ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos n), ∀ P v, I ((h.det ^ x₁ * g.det ^ x₃) • GlobalTheory.CompactHowe.subst2 h (g⁻¹)ᵀ P) (σ g v) = σ' h (I P v) := by
  first | exact @GlobalTheory.CompactHowe.exists_local_lift | exact GlobalTheory.CompactHowe.exists_local_lift | (intros; apply GlobalTheory.CompactHowe.exists_local_lift <;> assumption)
