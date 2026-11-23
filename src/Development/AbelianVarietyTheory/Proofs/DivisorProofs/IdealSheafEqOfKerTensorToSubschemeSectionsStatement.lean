module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSecAlgTop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqOfKerTensorToSubschemeSections
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

theorem _root_.GlobalTheory.T.idealSheaf_eq_of_ker_tensorToSubschemeSections : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (I₁ I₂ : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData), (∀ U : T.affineOpens, RingHom.ker (GlobalTheory.HilbAff.kappa A B g I₁ U) = RingHom.ker (GlobalTheory.HilbAff.kappa A B g I₂ U)) → I₁ = I₂ := by
  first | (exact @GlobalTheory.HilbAff.IdealDet.eq_of_ker_kappa_eq) | (exact GlobalTheory.HilbAff.IdealDet.eq_of_ker_kappa_eq) | (intros; apply GlobalTheory.HilbAff.IdealDet.eq_of_ker_kappa_eq <;> assumption)
