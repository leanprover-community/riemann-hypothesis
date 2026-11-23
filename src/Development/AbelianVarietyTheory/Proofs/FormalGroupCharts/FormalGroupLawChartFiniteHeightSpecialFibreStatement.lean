module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalGroupLawChartFiniteHeightSpecialFibre
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.formalGroupLaw_chart_finiteHeight_specialFibre : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G] (D : Out.DegData T (maximalIdeal T)) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing T)))) (_ : Out.UnifPre (maximalIdeal T) D A G) (d : ℕ) (F : FGLaw T d) (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x → ∀ N : ℕ, 1 ≤ N → ∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS (ResidueField T) 1 d)) ^ M ≤ Ideal.span (Set.range fun j => MvPowerSeries.map (residue T) (mulF F.F N j)) := by
  first | exact @GlobalTheory.FiniteHeight.exists_pow_span_X_le_span_map_residue_mulF | exact GlobalTheory.FiniteHeight.exists_pow_span_X_le_span_map_residue_mulF | (intros; apply GlobalTheory.FiniteHeight.exists_pow_span_X_le_span_map_residue_mulF <;> assumption)
