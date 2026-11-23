module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffMatrixFamilyBilateralSubstitutionMonomialCo
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


theorem _root_.GlobalTheory.T.coeff_matrixFamilyBilateralSubstitution_monomial_continuous_algebraic : ∀ {ι : Type} {N n : ℕ} (k k' : ι × Fin N × Fin n →₀ ℕ), Continuous (fun p : (ι → Matrix (Fin N) (Fin N) ℂ) × (ι → Matrix (Fin n) (Fin n) ℂ) => AddMonoidAlgebra.coeff (GlobalTheory.CompactHowe.substF p.1 p.2 (MvPolynomial.monomial k 1)) k') ∧ ∀ (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ), (∀ i a b, IsAlgebraic ℚ (h i a b)) → (∀ i a b, IsAlgebraic ℚ (g i a b)) → IsAlgebraic ℚ (AddMonoidAlgebra.coeff (GlobalTheory.CompactHowe.substF h g (MvPolynomial.monomial k 1)) k') := by
  first | exact @GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic | exact GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic | (intros; apply GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic <;> assumption)
