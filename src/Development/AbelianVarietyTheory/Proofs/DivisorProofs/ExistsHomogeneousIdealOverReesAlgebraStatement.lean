module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.ReesAlgebra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousIdealOverReesAlgebra
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

open MvPolynomial

theorem _root_.GlobalTheory.T.exists_homogeneous_ideal_over_reesAlgebra : ∀ (R : Type) [CommRing R] (I : Ideal R) (n : ℕ) (J : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ (e t : ℕ) (a : R) (F : MvPolynomial (Fin (n + 1)) R), a ∈ I → F.IsHomogeneous t → (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) → ∃ 𝔞 : Ideal (MvPolynomial (Fin (n + 1)) (reesAlgebra I)), (∀ F ∈ 𝔞, ∀ d, homogeneousComponent d F ∈ 𝔞) ∧ ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) (reesAlgebra I)), F.IsHomogeneous t → (F ∈ 𝔞 ↔ ∀ (e : ℕ) (G : MvPolynomial (Fin (n + 1)) R), (∀ m, AddMonoidAlgebra.coeff G m = (AddMonoidAlgebra.coeff F m).1.coeff e) → G ∈ J e) := by
  first | exact @GlobalTheory.ReesHomogeneous.exists_homogeneous_ideal | exact GlobalTheory.ReesHomogeneous.exists_homogeneous_ideal | (intros; apply GlobalTheory.ReesHomogeneous.exists_homogeneous_ideal <;> assumption)
