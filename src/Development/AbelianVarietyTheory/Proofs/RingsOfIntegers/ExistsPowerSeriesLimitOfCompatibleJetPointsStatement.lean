module

public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmallPointsSubstitutionAlgHomSinglePoint
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPowerSeriesLimitOfCompatibleJetPoints
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit

theorem _root_.GlobalTheory.T.exists_powerSeries_limit_of_compatible_jetPoints : ∀ (V : Type) [CommRing V] [IsLocalRing V] (G : Over (Sp V)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G), (∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetTrunc : Jet V (Fin 1 × Fin d) (m + 1) →ₐ[V] Jet V (Fin 1 × Fin d) m) ≫ x (m + 1) = x m) → ∃ X : limO V d 1 ⟶ G, IsLimit x X := by
  first | exact @GlobalTheory.TransUnit.LimEx.exists_isLimit | exact GlobalTheory.TransUnit.LimEx.exists_isLimit | (intros; apply GlobalTheory.TransUnit.LimEx.exists_isLimit <;> assumption)
