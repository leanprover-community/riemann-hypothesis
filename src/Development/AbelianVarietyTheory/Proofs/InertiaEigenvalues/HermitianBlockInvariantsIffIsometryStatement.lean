module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianBlockInvariantsIffIsometry
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.hermitianBlock_invariants_iff_isometry : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (lam : F), A.IsGen τ p → (∀ (a : A.K) (X : Hn r F E), IsUnit a → HasInv X (A.invK τ p lam a) → ∀ (x : A.K) (y : A.L), IsUnit y → a = x * A.NL y → ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom x j ∧ (∀ z, j (algebraMap A.K A.L τ * z) = X.1.1 *ᵥ j z) ∧ j y = X.2.1) ∧ ∀ (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∃ Ax : selfAdjoint (Matrix (Fin r) (Fin r) E), (∀ z, j (algebraMap A.K A.L τ * z) = Ax.1 *ᵥ j z) ∧ ∀ y, HasInv ((Ax, j y, lam) : Hn r F E) (A.invK τ p lam (x * A.NL y)) := by
  first | exact @GlobalTheory.EtIsom.herm_iff_isom | exact GlobalTheory.EtIsom.herm_iff_isom | (intros; apply GlobalTheory.EtIsom.herm_iff_isom <;> assumption)
