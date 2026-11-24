module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeOfEtalePunctured
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

open IsLocalRing

theorem _root_.GlobalTheory.T.free_of_etale_on_punctured_spectrum : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A], (((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) → 3 ≤ ringKrullDim R → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → Module.Free R A := by
  first | exact @GlobalTheory.PurityStep.free_of_etale_punctured | exact GlobalTheory.PurityStep.free_of_etale_punctured | (intros; apply GlobalTheory.PurityStep.free_of_etale_punctured <;> assumption)
