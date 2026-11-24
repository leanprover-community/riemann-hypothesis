module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweFiniteLengthTensorProductFactorsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweQuotientFiniteLengthFockPolynomialsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory
theorem howeAlg_fock_tensor : ∀ (T : Type) [Fintype T] [DecidableEq T] (P Q R S : T → ℕ) (x : T → ℂ), HoweAlg (fun w => actAt (V := fun w => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) w (fockAct2 (P w) (Q w) (R w) (S w))) (tensAny fun w => coinv (P w) (Q w) (R w) (S w) (x w)) := by
  intro T _ _ P Q R S x
  exact GlobalTheory.T.howe_finite_length_tensor_product_factors T (fun w => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) _ _ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) (fun w => coinv (P w) (Q w) (R w) (S w) (x w)) (fun w => GlobalTheory.T.howeQuotientFiniteLength_fockPolynomials (P w) (Q w) (R w) (S w) (x w))
end GlobalTheory
