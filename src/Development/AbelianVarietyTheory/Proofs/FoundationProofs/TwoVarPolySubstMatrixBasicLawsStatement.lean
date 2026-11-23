module

public import Development.AbelianVarietyTheory.Definitions.Foundations.OpLDOneSubMemTriv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoVarPolySubstMatrixBasicLaws
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
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.twoVarPolySubstMatrix_basic_laws : ∀ (R : Type) [CommRing R], (∀ (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R), slP (m * m') p = slP m' (slP m p)) ∧ (∀ p : MvPolynomial (Fin 2) R, slP 1 p = p) ∧ (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (w : ℕ) (p : MvPolynomial (Fin 2) R), p.IsHomogeneous w → (slP m p).IsHomogeneous w) ∧ (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (u : Fin 2 → R) (p : MvPolynomial (Fin 2) R), MvPolynomial.eval u (slP m p) = MvPolynomial.eval (m.map (Int.castRingHom R) *ᵥ u) p) ∧ (∀ (S : Type) [CommRing S] (f : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R), MvPolynomial.map f (slP m p) = slP m (MvPolynomial.map f p)) ∧ (∀ (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R), (∀ i j, (m i j : R) = (m' i j : R)) → slP m p = slP m' p) ∧ (∀ (w : ℕ) (p : MvPolynomial (Fin 2) R), p.IsHomogeneous w → slP (-1) p = (-1 : R) ^ w • p) := by
  first | exact @GlobalTheory.KZ.polySlash_laws | exact GlobalTheory.KZ.polySlash_laws | (intros; apply GlobalTheory.KZ.polySlash_laws <;> assumption)
