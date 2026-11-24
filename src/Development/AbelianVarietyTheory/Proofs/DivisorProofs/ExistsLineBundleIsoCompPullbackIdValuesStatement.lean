module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoCompPullbackIdValues
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveValueOfRingElementPsiRelation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorsionLift

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two


theorem _root_.GlobalTheory.T.exists_lineBundleIso_comp_pullback_id_values : ∀ {Y X₀ X : Scheme.{0}} {A : LB Y} {L₀ : LB X₀} {M : LB X} {K₀ K : Type} [Fintype K₀] [Fintype K] (φ₀ : K₀ → (Y ⟶ X₀)) (ε₀ : K₀ → ℤ) (φ : K → (Y ⟶ X)) (ε : K → ℤ), A.IsLB → L₀.IsLB → M.IsLB → ∀ (u : LB.Iso A (LB.LinComb L₀ φ₀ ε₀)), u.IsGen → ∀ (v : LB.Iso (LB.LinComb L₀ φ₀ ε₀) ((LB.LinComb M φ ε).pull (𝟙 Y))), v.IsGen → ∃ w : LB.Iso A (LB.LinComb M φ ε), w.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι) (J₀ : (Z ⟶ X₀) → L₀.ι) (a : A.ι), q z ∈ A.U a → Good M z J → Good L₀ z J₀ → gm q z _ (w.s (fun k => J (q ≫ φ k), a)) = gm q z _ (u.s (fun k => J₀ (q ≫ φ₀ k), a)) * GlobalTheory.Mum.Two.isoVal v q z J J₀ := by
  exact @GlobalTheory.IsoPullIdComp.exists_comp_val
