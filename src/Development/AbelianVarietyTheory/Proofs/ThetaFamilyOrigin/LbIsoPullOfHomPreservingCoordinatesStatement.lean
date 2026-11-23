module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.LbIsoPullOfHomPreservingCoordinates
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lbIso_pull_of_hom_preserving_coordinates : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P P' : Out.PolAV (Sp K)) (N m : ℕ) (J : Type) (s : J → (lbPow P.L N).Sec) (s' : J → (lbPow P'.L N).Sec) (a : J) (θ : (lbPow P.L 1).Sec) (θ' : (lbPow P'.L 1).Sec) (φ : P.A ⟶ P'.A), 1 ≤ m → IsMonHom φ → ⨆ j, Out.nonzeroLocus (s j) = ⊤ → (∀ (F : Type) [Field F] (y : Sp F ⟶ P.A.left) (v : J → F), Crd (lbPow P.L N) s y v → Crd (lbPow P'.L N) s' (y ≫ φ.left) v) → (∃ l, θ.f l ≠ 0) → (∀ (y : P.A.left) k l, y ∈ (lbPow P.L N).U k → (Out.mulA P.A m).left y ∈ (lbPow P.L 1).U l → Associated (gs (𝟙 P.A.left) y ((lbPow P.L N).U k) ((s a).f k)) (gs (Out.mulA P.A m).left y ((lbPow P.L 1).U l) ((θ).f l))) → (∀ (y : P'.A.left) k l, y ∈ (lbPow P'.L N).U k → (Out.mulA P'.A m).left y ∈ (lbPow P'.L 1).U l → Associated (gs (𝟙 P'.A.left) y ((lbPow P'.L N).U k) ((s' a).f k)) (gs (Out.mulA P'.A m).left y ((lbPow P'.L 1).U l) ((θ').f l))) → LBIso (P'.L.pull φ.left) P.L := by
  first | exact @GlobalTheory.ZH.PolAgree.lbIso_pull | exact GlobalTheory.ZH.PolAgree.lbIso_pull | (intros; apply GlobalTheory.ZH.PolAgree.lbIso_pull <;> assumption)
