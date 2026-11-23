module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBareNormDisc
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.UnfSectionNormBoundAtHeight
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

theorem _root_.GlobalTheory.T.unf_section_norm_bound_at_height : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (U : Formalism.L2.Pj.Unf Xo c σ r) (x : ℝ) (Z : Formalism.L2.Pj.Comp Xo c) (τ : GlobalTheory.AllWt.Psi H) (s : Formalism.L2.Pj.Rul Xo c) (φ : FrameFn Xo c) (t : ℝ), Formalism.L2.Pj.GoodEmb c σ → Formalism.L2.Pj.IsUnf U → (∀ k (τ' : E →+* ℂ), ‖τ' (U.X k).ξ0‖ = x) → s ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0) → IsLineFn (Z : Set (Xo.XF c)) τ.1 φ → Reads (Z : Set (Xo.XF c)) τ.1 s φ → HasInfNorm (Z : Set (Xo.XF c)) τ.1 φ σ t → ∀ z ∈ GlobalTheory.AllWt.framesOn U Z, (∀ hz : z.2 ∈ (U.X z.1).dom, GlobalTheory.FlatLine.Tested (U.un z.1 ⟨z.2, hz⟩)) → GlobalTheory.AllWt.homN U x (GlobalTheory.AllWt.wtOf D (GlobalTheory.FlatLine.flatWt D τ) 0) s z = Real.exp t := by
  exact @GlobalTheory.CompanionTheory.Ar.Br.homN_eq_exp_hodge
