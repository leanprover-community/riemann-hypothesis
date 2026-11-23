module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NearRecordOfValue
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.WeilBound.CoreStatements.FlagImmersions.CptEx
public import Development.WeilBound.CoreStatements.FlagImmersions.ExistsIntProj
public import Development.WeilBound.CoreStatements.FlagImmersions.ExistsLiftGenFibre
public import Development.WeilBound.CoreStatements.FlagImmersions.HostRd
public import Development.WeilBound.CoreStatements.FlagImmersions.LocalCmpOf
public import Development.WeilBound.CoreStatements.FlagImmersions.LogIdealNonpos
public import Development.WeilBound.CoreStatements.FlagImmersions.MemGenFibre
public import Development.WeilBound.CoreStatements.FlagImmersions.RangeSubIff
public import Development.WeilBound.CoreStatements.FlagImmersions.RootFlatOnHodgeOf
public import Development.WeilBound.CoreStatements.FlagImmersions.UnitAtOfSpan
public import Development.WeilBound.CoreStatements.FlagImmersions.ValAtOfExtends
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace RootFieldNumerics

theorem rootFlatOnHodge (hFD : Fl.FlatDegree) (hG : Given) : Flat.RootFlatOnHodge :=
  RF.rootFlatOnHodge_of RF.cptEx RF.periodOf RF.smoothLine
    (RF.localCmp_of RF.pointEx RF.valuePhi RF.intFrames RF.fibSandwich) RF.chiEx RF.numerics hFD hG

theorem global_model_tower_final_condition : Fl.FlatDegree → Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ a τ, ∃ R : Flat.RootFlat (T.M 2 a) τ, Flat.NearRecord (D.p + D.q) T.bad (hostRd E) (hostLval H) R.ht := by
  intro hFD hG E _ _ _ _ H D Xo l c Y _ T o II hY _ _ _ _ a τ
  exact Flat.OnHodge.tower (rootFlatOnHodge hFD hG) hY ⟨o.toTowerOrigin, o.omVB⟩ a τ

end RootFieldNumerics
