module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLinearLiftAdditiveHolomorphicAbelian
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
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TopLeWchartNsmul
import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcSPin
import Formalism.LocalToGlobal.ProjectiveLattices.JFDFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.exists_linearLift_additiveHolomorphic_abelian : ∀ (P P' : Out.PolAV (Sp ℂ)) (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A (spMap (RingHom.id ℂ)) φ → ∀ (u : HolUnif P'.A P'.L P'.g) (g : ℕ) (T : Over (Sp ℂ)) (i : Sp ℂ ⟶ T.left), i ≫ T.hom = 𝟙 _ → ∀ G : (Fin g → ℂ) → (T ⟶ P.A), (∀ z z', G (z + z') = G z * G z') → IsHolTo Set.univ (fun z => i ≫ (G z).left) → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ), (∀ z, (u.ex (F z)).left ≫ φ = i ≫ (G z).left) ∧ (∀ z, G z = 1 → F z ∈ u.Λ) ∧ ∀ (z : Fin g → ℂ) (z' : Fin P'.g → ℂ) (η' : epsR ℂ ⟶ P'.A), IsDerivAt0 (fun z => i ≫ (G z).left) z (η'.left ≫ φ) → u.IsDiff z' η' → z' = F z := by
  first | exact @GlobalTheory.AbelianLetters.exists_linear_lift_of_isGrpPullback | exact GlobalTheory.AbelianLetters.exists_linear_lift_of_isGrpPullback | (intros; apply GlobalTheory.AbelianLetters.exists_linear_lift_of_isGrpPullback <;> assumption)
