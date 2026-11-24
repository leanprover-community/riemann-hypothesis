module

public import Formalism.LocalToGlobal.CharacterGerms.IntSubst
public import Formalism.LocalToGlobal.CharacterGerms.Interface
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesLthPowerOfPderivVanishModMaximal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Formalism.LocalToGlobal.Divisibility.Numbers
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.mvPowerSeries_lthPower_of_pderiv_vanish_mod_maximal : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (σ : Type) [Fintype σ], (∀ b : MvPowerSeries σ C, IntS V b → (∀ i μ, V.MM (MvPowerSeries.coeff μ (MvPowerSeries.pderiv (R := C) i b))) → ∃ b' : MvPowerSeries σ C, IntS V b' ∧ ∀ μ, V.MM (MvPowerSeries.coeff μ (b - b' ^ V.l))) ∧ (∀ f g : MvPowerSeries σ C, IntS V f → IntS V g → (∀ μ, V.MM (MvPowerSeries.coeff μ (f ^ V.l - g ^ V.l))) → ∀ μ, V.MM (MvPowerSeries.coeff μ (f - g))) ∧ ∀ f g : MvPowerSeries σ C, IntS V f → IntS V g → ∀ μ, V.MM (MvPowerSeries.coeff μ ((f + g) ^ V.l - f ^ V.l - g ^ V.l)) ∧ V.MM (MvPowerSeries.coeff μ ((f - g) ^ V.l - (f ^ V.l - g ^ V.l))) := by
  first | exact @GlobalTheory.SeriesFrobRoot.main | exact GlobalTheory.SeriesFrobRoot.main | (intros; apply GlobalTheory.SeriesFrobRoot.main <;> assumption)
