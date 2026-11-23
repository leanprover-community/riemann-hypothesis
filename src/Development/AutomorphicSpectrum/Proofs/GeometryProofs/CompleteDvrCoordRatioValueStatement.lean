module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompleteDvrCoordRatioValue
import Formalism.LocalRingCardinality.DataHost
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.complete_dvr_coord_ratio_value : ∀ (X : AlgebraicGeometry.Scheme.{0}) (Ω : Type) [Field Ω] (ξ : AlgebraicGeometry.Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (A : Subring Ω) (T : CDVR) (evT : A →+* T.Fr) (c : (k : K) → J k), (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ (hr : ∀ k i, y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ A), (∀ k i, evT ⟨_, hr k i⟩ ∈ (algebraMap T.V T.Fr).range) → (∀ a : A, ∃ b : A, evT b ≠ 0 ∧ (b : Ω) ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩) ∧ (a : Ω) * b ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩)) → ∃ (zV : AlgebraicGeometry.Spec (CommRingCat.of T.V) ⟶ X) (h : genPt ξ ⤳ centre zV), InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c ⟨centre zV, h⟩ ∧ FinRd.Roots.ReadsPt ξ A T evT zV := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.chart_point | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.chart_point | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.chart_point <;> assumption)
