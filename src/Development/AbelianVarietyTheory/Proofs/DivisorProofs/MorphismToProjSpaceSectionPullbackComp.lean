module

public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.toProj_secPull_secPull (R : Type) [CommRing R] (N : ℕ) (X Y Z : Scheme.{0}) (L : LB X)
    (s : Fin (N + 1) → L.Sec) (h : Y ⟶ X) (g : Z ⟶ Y) (f : Z ⟶ Sp R)
    (hs₁ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (GlobalTheory.secPull (s i) h) g) = ⊤)
    (hs₂ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) (g ≫ h)) = ⊤) :
    GlobalTheory.ProjSpace.toProj f (fun i => GlobalTheory.secPull (GlobalTheory.secPull (s i) h) g) hs₁ =
      GlobalTheory.ProjSpace.toProj f (fun i => GlobalTheory.secPull (s i) (g ≫ h)) hs₂ := by
  refine GlobalTheory.ProjSpace.toProj_eq_of_locally hs₂ hs₁ fun z => ?_
  obtain ⟨k, hk⟩ : ∃ k : PUnit → L.ι, z ∈ (L.pull (g ≫ h)).U k :=
    GlobalTheory.ProjSpace.exists_chart_of_iSup_nonzeroLocus hs₂ z
  let l : ((L.pull h).pull g).ι := fun _ _ => k PUnit.unit
  have hle : (L.pull (g ≫ h)).U k ≤ ((L.pull h).pull g).U l := by
    rw [GlobalTheory.Cartier.pull_U L (g ≫ h) k, GlobalTheory.Cartier.pull_U (L.pull h) g l,
      GlobalTheory.Cartier.pull_U L h (fun _ => k PUnit.unit)]
    exact fun _ hy => hy
  refine ⟨_, hk, k, le_rfl, l, hle, 1, fun j => ?_⟩
  rw [_root_.one_mul]
  unfold GlobalTheory.secPull
  rw [GlobalTheory.chartSec_f, GlobalTheory.chartSec_f, GlobalTheory.chartSec_f (GlobalTheory.chartPullPull L (g ≫ h)) (s j) k]
  simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE_assoc,
    Scheme.Hom.appLE_map]
  rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_map]
  rfl
