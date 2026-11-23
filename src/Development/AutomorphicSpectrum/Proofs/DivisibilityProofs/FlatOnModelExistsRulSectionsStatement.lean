module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBareNormDisc
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlatOnModelExistsRulSections
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

theorem _root_.GlobalTheory.T.flat_on_model_exists_rul_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Formalism.L2.Pj.Comp Xo c) (Z' : CptOver Y (Z : Set (Xo.XF c))) (τ : GlobalTheory.AllWt.Psi H) (φ : FrameFn Xo c), FlatOnModel Z' τ.1 φ → ∃ s s' : Formalism.L2.Pj.Rul Xo c, s ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0) ∧ s' ∈ GlobalTheory.AllWt.secZ Xo c (-GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * s' = s' ∧ s * s' = GlobalTheory.FlatLine.idem Z ∧ Reads (Z : Set (Xo.XF c)) τ.1 s φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Br.exists_flat_sec | exact GlobalTheory.CompanionTheory.Ar.Br.exists_flat_sec | (intros; apply GlobalTheory.CompanionTheory.Ar.Br.exists_flat_sec <;> assumption)
