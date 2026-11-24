module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareLemmaTruncatedDivPowerPolyOneVariable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.poincareLemma_truncated_divPowerPoly_oneVariable : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) (G : Type) [CommRing G] [Algebra R G] (J' : Ideal G) (δ' : DividedPowers J') (q : Q.P →+* G) (n : ℕ), Q.IsStd δ η → IsLev δ (n + 1) → SemiHom (RingHom.id R) q → IsDPMorphism η δ' q → Function.Surjective q → J' = (Q.ext J).map q → (∀ b, q b = 0 ↔ b ∈ fil η (n + 1)) → ∀ (α : B →+* G) (h : SemiHom (RingHom.id R) α) (hd : IsDPMorphism δ δ' α), (∀ b, α b = q (algebraMap B Q.P b)) → RQ h hd := by
  first | exact @GlobalTheory.PDForm.rq_truncPoly | exact GlobalTheory.PDForm.rq_truncPoly | (intros; apply GlobalTheory.PDForm.rq_truncPoly <;> assumption)
