module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DualMapSOfIdToRingHom
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieFrames
import Formalism.DegreeFormula.FlagDegFormula
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

namespace GlobalTheory.ArLieBase


set_option backward.isDefEq.respectTransparency false in
theorem hom_ext_dualNumber_away : ∀ {L : Type} [CommRing L] {s : Set L}, Ideal.span s = ⊤ → ∀ {Y : Scheme.{0}} {w w' : Sp (DualNumber L) ⟶ Y}, (∀ a : s, spMap (Formalism.L2.Pj.dualMap (algebraMap L (Localization.Away (a : L)))) ≫ w = spMap (Formalism.L2.Pj.dualMap (algebraMap L (Localization.Away (a : L)))) ≫ w') → w = w' := by
  intro L _ s hs Y w w' h
  have hs' : Ideal.span (Set.range (fun k : s => (TrivSqZeroExt.inl (k : L) : DualNumber L))) = ⊤ := by
    have := congrArg (Ideal.map (TrivSqZeroExt.inlHom L L)) hs
    rw [Ideal.map_span, Ideal.map_top, Set.image_eq_range] at this
    exact this
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of (DualNumber L)) _ hs').openCover
  refine Scheme.Cover.hom_ext 𝒰 _ _ fun (k : s) => ?_
  have hd : Formalism.L2.Pj.dualMap (algebraMap L (Localization.Away (k : L))) =
      ReciprocityTheory.ChartRestriction.G.Chart.dAway (k : L) := by
    refine RingHom.ext fun x => ?_
    ext <;> simp [Formalism.L2.Pj.dualMap, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]
  have e : 𝒰.f k = Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Chart.toL (k : L))) ≫
      Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Chart.dAway (k : L))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ReciprocityTheory.ChartRestriction.G.Chart.toL_comp]
    rfl
  have hk := h k
  rw [hd] at hk
  rw [e, Category.assoc, Category.assoc]
  exact congrArg (_ ≫ ·) hk

end GlobalTheory.ArLieBase
