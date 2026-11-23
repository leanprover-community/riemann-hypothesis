module

public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetPointsUnitLawActionBaseChange
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
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartFrameTrA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

theorem _root_.GlobalTheory.T.jetPoints_unit_law_action_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X0), x1 = spMap ψ ≫ x0 → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t.G), (∀ m, (x' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (x m).left) → ((∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1) → (∀ m, homAt x1 (jetAug : Jet S' (Fin 1 × Fin d) m →ₐ[S'] S') ≫ x' m = 1)) ∧ (∀ F : Fin d → PS S 2 d, (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ m, homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x m = jptG t x0 d x m (0 : Fin 2) * jptG t x0 d x m (1 : Fin 2)) → (∀ m, homAt x1 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (MvPowerSeries.map ψ (F p.2))) ≫ x' m = jptG t x1 d x' m (0 : Fin 2) * jptG t x1 d x' m (1 : Fin 2))) ∧ ∀ act : 𝓞 E → Fin d → PS S 1 d, (∀ b j, MvPowerSeries.constantCoeff (act b j) = 0) → (∀ m (b : 𝓞 E), x m ≫ t.act.act b = homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x m) → (∀ m (b : 𝓞 E), x' m ≫ t.act.act b = homAt x1 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (MvPowerSeries.map ψ (act b p.2))) ≫ x' m) := by
  first | exact @GlobalTheory.JetPointBC.unit_law_act_baseChange | exact GlobalTheory.JetPointBC.unit_law_act_baseChange | (intros; apply GlobalTheory.JetPointBC.unit_law_act_baseChange <;> assumption)
