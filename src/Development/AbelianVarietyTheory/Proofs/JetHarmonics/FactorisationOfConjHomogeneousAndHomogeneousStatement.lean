module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FactorisationOfConjHomogeneousAndHomogeneous
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.StatementI

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.factorisation_of_conjHomogeneous_and_homogeneous : ∀ (T Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] (l : T → Wp) (l' : T → Wq) (J : T → T → (Wq →L[ℂ] Wp) → (Wq →L[ℂ] Wp)) (A : T → Wq → Wq → Wp) (Bb : T → Wp → Wq → Wp), (∀ y a c (t : ℂ), A y (t • a) c = star t • A y a c) → (∀ x b c (t : ℂ), Bb x (t • b) c = t • Bb x b c) → (∀ x y X c, J x y X c = A y (ContinuousLinearMap.adjoint X (l x)) c) → (∀ x y X c, J x y X c = Bb x (X (l' y)) c) → ∃ OO : Wq →L[ℂ] Wp, ∀ x y X, J x y X = ⟪l x, X (l' y)⟫_ℂ • OO := by
  first | exact @GlobalTheory.factorisation_of_two_partial_integrations | exact GlobalTheory.factorisation_of_two_partial_integrations | (intros; apply GlobalTheory.factorisation_of_two_partial_integrations <;> assumption)
