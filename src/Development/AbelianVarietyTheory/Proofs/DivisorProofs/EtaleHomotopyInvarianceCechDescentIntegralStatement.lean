module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
public import Mathlib.RingTheory.PiTensorProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceCechDescentIntegral
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.etaleHomotopyInvariance_cechDescent_integral : ∀ (q : ℕ) [NeZero q] (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Algebra.IsIntegral A B → RingHom.ker (algebraMap A B) ≤ nilradical A → IsUnit (q : A) → (∀ k : ℕ, HInv q (PiTensorProduct A (fun _ : Fin (k + 1) => B))) → HInv q A := by
  first | (exact @GlobalTheory.EtC.CechDescHInv.hInv_of_integral) | (exact GlobalTheory.EtC.CechDescHInv.hInv_of_integral) | (intros; apply GlobalTheory.EtC.CechDescHInv.hInv_of_integral  <;> assumption)
