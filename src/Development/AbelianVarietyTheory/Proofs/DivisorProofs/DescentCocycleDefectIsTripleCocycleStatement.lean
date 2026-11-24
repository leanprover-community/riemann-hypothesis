module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentCocycleDefectIsTripleCocycle
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
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.LBDescent GlobalTheory.DescNorm

theorem _root_.GlobalTheory.T.descentCocycleDefect_isTripleCocycle : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) (M : LB X), M.IsLB → ∀ (φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ) (D : Γ(Triple f, ⊤)ˣ), Defect f M φ D → TriCocycle f D := by
  first | exact @GlobalTheory.PolRoot.triCocycle_of_defect | exact GlobalTheory.PolRoot.triCocycle_of_defect | (intros; apply GlobalTheory.PolRoot.triCocycle_of_defect <;> assumption)
