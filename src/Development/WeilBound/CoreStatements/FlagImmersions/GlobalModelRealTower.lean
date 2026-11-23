module

public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.WeilBound.CoreStatements.FlagImmersions.AnalyticAtAeval
public import Development.WeilBound.CoreStatements.FlagImmersions.ContAtOfHoloOn
public import Development.WeilBound.CoreStatements.FlagImmersions.CoordsOrbit
public import Development.WeilBound.CoreStatements.FlagImmersions.CountableBall
public import Development.WeilBound.CoreStatements.FlagImmersions.EqZeroOfTri
public import Development.WeilBound.CoreStatements.FlagImmersions.ExistsModelOfEq
public import Development.WeilBound.CoreStatements.FlagImmersions.ExistsRightInv
public import Development.WeilBound.CoreStatements.FlagImmersions.FlagImmersion
public import Development.WeilBound.CoreStatements.FlagImmersions.GenRigidOf
public import Development.WeilBound.CoreStatements.FlagImmersions.HasPerConj
public import Development.WeilBound.CoreStatements.FlagImmersions.Imports
public import Development.WeilBound.CoreStatements.FlagImmersions.IsHolToOfLocal
public import Development.WeilBound.CoreStatements.FlagImmersions.NormDetEq
public import Development.WeilBound.CoreStatements.FlagImmersions.PerCoord
public import Development.WeilBound.CoreStatements.FlagImmersions.RankLem
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

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

theorem RootFieldNumerics.global_model_real_tower : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → (realOf o.toTowerOrigin).Unif := by
  intro hG E _ _ _ _ H D Xo l c Y _ T o II _ _ _ hp _ a
  rw [o.j_eq]
  exact RootFieldNumerics.Un.unif_of (RootFieldNumerics.biholo_of RootFieldNumerics.descend) RootFieldNumerics.locPer RootFieldNumerics.transport RootFieldNumerics.frameVals
    (RootFieldNumerics.perMat_of RootFieldNumerics.perCoord RootFieldNumerics.matStep) (RootFieldNumerics.flagImm_of RootFieldNumerics.rankLem)
    (RootFieldNumerics.countGen_of (RootFieldNumerics.genRigid_of RootFieldNumerics.frameVals)) RootFieldNumerics.potLoc RootFieldNumerics.ptsFam hG (le_add_right hp) (o.refOr a)
    (o.ref_top a) (o.ref_deg a) (o.ample a)
