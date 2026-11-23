module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsNormPull
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreSectionLinearCombExistsUniqueThetaAction
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

theorem _root_.GlobalTheory.T.fibreSection_linearComb_exists_unique_thetaAction : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (J : Type) [Fintype J] (s : J → SecA A F k) (b : J → F), (∃ t, IsComb A s b t) ∧ (∀ t t', IsComb A s b t → IsComb A s b t' → t = t') ∧ (∀ (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) (s' : J → SecA A F k) t t', (∀ i, IsActOf A.A A.L k θ (s i) (s' i)) → IsComb A s b t → (IsActOf A.A A.L k θ t t' ↔ IsComb A s' b t')) ∧ (∀ (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) (t : SecA A F k), ∃! t', IsActOf A.A A.L k θ t t') ∧ ∀ (I : Type) [Fintype I] (M : I → J → F) (r : I → SecA A F k) (a : I → F) (t : SecA A F k), (∀ i, IsComb A s (M i) (r i)) → IsComb A r a t → IsComb A s (fun j => ∑ i, M i j * a i) t := by
  first | exact @GlobalTheory.secComb_thetaAct | exact GlobalTheory.secComb_thetaAct | (intros; apply GlobalTheory.secComb_thetaAct <;> assumption)
