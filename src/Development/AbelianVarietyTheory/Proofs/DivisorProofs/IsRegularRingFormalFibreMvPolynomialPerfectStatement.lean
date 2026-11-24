module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularRingFormalFibreMvPolynomialPerfect
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

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.isRegularRing_formal_fibre_mvPolynomial_perfect : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (n : ℕ) (P : Ideal (MvPolynomial (Fin n) Λ)) [P.IsPrime] (K : Type) [Field K] [Algebra (Localization.AtPrime P) K] [Algebra.EssFiniteType (Localization.AtPrime P) K], (∀ a : Λ, algebraMap (Localization.AtPrime P) K (algebraMap Λ (Localization.AtPrime P) a) = 0 → a = 0) → IsRegularRing (AdicCompletion (maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P) ⊗[Localization.AtPrime P] K) := by
  first | exact @GlobalTheory.isRegularRing_adicCompletion_tensor_of_mvPolynomial | exact GlobalTheory.isRegularRing_adicCompletion_tensor_of_mvPolynomial | (intros; apply GlobalTheory.isRegularRing_adicCompletion_tensor_of_mvPolynomial <;> assumption)
