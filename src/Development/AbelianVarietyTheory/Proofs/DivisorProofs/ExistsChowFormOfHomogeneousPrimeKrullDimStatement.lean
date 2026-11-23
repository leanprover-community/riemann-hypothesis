module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChowFormOfHomogeneousPrimeKrullDim
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal

@[expose] public section

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

theorem _root_.GlobalTheory.T.exists_chowForm_of_homogeneous_prime_krullDim : ∀ (K : Type) [Field K] (N D : ℕ) (P : Ideal (MvPolynomial (Fin N) K)), P.IsPrime → (∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) → ringKrullDim (MvPolynomial (Fin N) K ⧸ P) = (D + 1 : ℕ) → ∃ (δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) K), IsChowFormInt P D δ f := by
  first | exact @GlobalTheory.ChowHt.exists_isChowFormInt_of_ringKrullDim_eq | exact GlobalTheory.ChowHt.exists_isChowFormInt_of_ringKrullDim_eq | (intros; apply GlobalTheory.ChowHt.exists_isChowFormInt_of_ringKrullDim_eq <;> assumption)
