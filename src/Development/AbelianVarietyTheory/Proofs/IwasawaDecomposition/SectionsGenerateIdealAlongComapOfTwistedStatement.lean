module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratesAlong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Proportional
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionsGenerateIdealAlongComapOfTwisted
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup

theorem _root_.GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted : ∀ (X W : Scheme.{0}) (J : X.IdealSheafData) (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X), Generates J σ → GeneratesAlong (J.comap g) σ g := by
  first | exact @GlobalTheory.ProjBlowup.generatesAlong_comap_of_generates | exact GlobalTheory.ProjBlowup.generatesAlong_comap_of_generates | (intros; apply GlobalTheory.ProjBlowup.generatesAlong_comap_of_generates <;> assumption)
