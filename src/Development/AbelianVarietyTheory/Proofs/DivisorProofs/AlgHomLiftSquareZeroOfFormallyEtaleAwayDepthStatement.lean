module

public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
public import Mathlib.RingTheory.Etale.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftSquareZeroOfFormallyEtaleAwayDepth
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

theorem _root_.GlobalTheory.T.algHom_lift_squareZero_of_formallyEtale_away_depth : ∀ (R : Type) [CommRing R] [IsLocalRing R] (A : Type) [CommRing A] [Algebra R A], (∀ g ∈ maximalIdeal R, Algebra.FormallyEtale (Localization.Away g) (TensorProduct R (Localization.Away g) A)) → ∀ (S T : Type) [CommRing S] [Algebra R S] [CommRing T] [Algebra R T], ReciprocityTheory.CA.ModDepthGE R S 2 → ReciprocityTheory.CA.ModDepthGE R T 1 → ∀ (π : S →ₐ[R] T), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (φ : A →ₐ[R] T), ∃ ψ : A →ₐ[R] S, π.comp ψ = φ := by
  first | exact @GlobalTheory.SquareZeroLift.squareZeroLift | exact GlobalTheory.SquareZeroLift.squareZeroLift | (intros; apply GlobalTheory.SquareZeroLift.squareZeroLift <;> assumption)
