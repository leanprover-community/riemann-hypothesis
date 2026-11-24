module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SqMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeneratorRatioUnitExists
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.generator_ratio_unit_exists : ∀ (X Y F : Scheme.{0}) (L : LB X) (M : LB Y) (f : F ⟶ X) (g : F ⟶ Y), L.IsLB → M.IsLB → ∀ (w : LB.Iso (L.pull f) (M.pull g)), w.IsGen → ∀ (Y' : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y' ⟶ F)) (φL : K → (Y' ⟶ X)) (φM : K → (Y' ⟶ Y)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φL ε)) (b : LB.Gen (LB.LinComb M φM ε)), (∀ i, φ i ≫ f = φL i) → (∀ i, φ i ≫ g = φM i) → c.IsGen → b.IsGen → ∃ u : Γ(Y', ⊤)ˣ, Tr w φ φL φM ε c b u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.exists_ratio_iso | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.exists_ratio_iso | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.exists_ratio_iso <;> assumption)
