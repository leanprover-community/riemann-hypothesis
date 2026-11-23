module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginWeightFree
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.DefiniteFormStabilizerFiniteAwayFromP
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem good_origin_root_coefficients : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [DecidableEq (CMType H)] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b₀ : T.Comp) (lam : Top.Wt (CMType H) (Dw.p + Dw.q)) (n' : Option (RootIx Dw) → ℤ), (∀ j, (n' j : ℝ) = (T.M B b₀).coef lam 0 j) → Top.RegDominant lam → ∃ (q₀ : ℕ) (n₀ : Option (RootIx Dw) → ℤ) (ε : (T.M B b₀).Ω) (u : MRing (T.M B b₀).ι) (C s₀ : ℝ), 0 < q₀ ∧ (∀ j, (n₀ j : ℝ) = q₀ * (T.M B b₀).coef T.nu (-1) j) ∧ ε ≠ 0 ∧ ε ∈ chartLatNm (T.M B b₀).y (Top.combLine ((T.M B b₀).line 1) n₀).a 1 ∧ Small.IsFormOff (mCoordIdeal (T.M B b₀).y) u ∧ 0 ≤ C ∧ 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ → ∀ z ∈ mcPts (mCoordIdeal (T.M B b₀).y), MvPolynomial.aeval z u ≠ 0 → ∀ x : ℂ, Small.HasVal (T.M B b₀).y (Top.combLine ((T.M B b₀).line 1) n₀).a ε z x → x ≠ 0 → s / q₀ * Real.log ‖x‖ + (T.M B b₀).weight (Top.scale s) (lam - s • T.nu) s z ≤ C * s + Real.log (∏ r, ((o.toTowerOrigin.Or B b₀).sing r).h z ^ n' (some r)) := by
  intro E _ _ _ H Dw l Xo c _ Y T o B b₀ lam n' hn' _
  exact root_origin_weight_free E H Dw l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y (o.toTowerOrigin.S B) (T.M B b₀)
    (o.toTowerOrigin.Sys b₀) (o.toTowerOrigin.Fx b₀) (o.toTowerOrigin.Or B b₀) lam T.nu n'
    (o.toTowerOrigin.nu_eq b₀) hn'

end GlobalTheory.CompanionTheory.Ar.Small
