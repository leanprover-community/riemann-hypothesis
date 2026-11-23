module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LocalComponentsSurjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
public import Development.WeilBound.CoreStatements.HodgeTatePoints.CdAffine
public import Development.WeilBound.CoreStatements.HodgeTatePoints.CocpMain
public import Development.WeilBound.CoreStatements.HodgeTatePoints.IsMapOfCancel
import Development.WeilBound.CoreStatements.HodgeTatePoints.IsPullbackWhisker
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.HtPt.Cf

theorem fib_inj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d), FibPF t (x (IsLocalRing.closedPoint k)) → ConjInj g.B p :=
  fib_inj_of PositivityTheory.HtPt.Ce.geompf_tan PositivityTheory.HtPt.Ce.germ_bc PositivityTheory.HtPt.Cocp.tanpf_inj

theorem family_ex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (C : ACurve K) (z : Sp K ⟶ X0) (Y : CurveIn C z), (∀ i, FibPF t (GlobalTheory.CompanionTheory.Ar.centre (Y.x i))) → ∃ (d : ℕ) (F : Family C p d (𝓞 E)) (g : GermAt t z d), g.B = F.B ∧ ∀ i, ∃ gi : GermAt t (Y.x i) d, ∀ l, IsCombAtG t z g.tg (fun j => lin (F.φ i) 1 j l) (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l) :=
  family_ex_of PositivityTheory.HtPt.Ce.geompf_tan PositivityTheory.HtPt.Ce.germ_bc PositivityTheory.HtPt.Cocp.tanpf_inj PositivityTheory.HtPt.Cd.germ_affine

end PositivityTheory.HtPt.Cf
