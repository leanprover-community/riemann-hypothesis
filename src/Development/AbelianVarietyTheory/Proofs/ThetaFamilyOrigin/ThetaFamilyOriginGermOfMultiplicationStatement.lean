module

public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIndepSections
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ThetaFamilyOriginGermOfMultiplication
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaFamily_origin_germ_of_multiplication : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N m : ℕ) (J : Type) (x : J → ((Out.baseOver (Sp K)) ⟶ P.A)) (th : LB.Sec (Out.LPow P.A P.L 1 (Out.baseOver (Sp K)))) (t : J → LB.Sec (Out.LPow P.A P.L N (Out.baseOver (Sp K)))) (ρ : P.A.left ⟶ ((Out.baseOver (Sp K)) ⊗ P.A).left) (e : ρ ≫ (snd (Out.baseOver (Sp K)) P.A).left = 𝟙 P.A.left) (a : J), Out.IsGenSec P.A P.L 1 th → IsThetaFamily P N m x th t → x a = 1 → (∃ l, (PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((1 : ℕ) : ℤ) (th)).f l ≠ 0) ∧ (∀ (y : P.A.left) k l, y ∈ (lbPow P.L N).U k → (Out.mulA P.A m).left y ∈ (lbPow P.L 1).U l → Associated (gs (𝟙 P.A.left) y ((lbPow P.L N).U k) ((PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((N : ℕ) : ℤ) (t a)).f k)) (gs (Out.mulA P.A m).left y ((lbPow P.L 1).U l) ((PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((1 : ℕ) : ℤ) (th)).f l))) := by
  first | exact @GlobalTheory.ThetaGerm.germ_origin | exact GlobalTheory.ThetaGerm.germ_origin | (intros; apply GlobalTheory.ThetaGerm.germ_origin <;> assumption)
