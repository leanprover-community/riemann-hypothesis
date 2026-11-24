module

public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSandwichOfHodgeTateFreeStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatZeroFromResolutionAndGagaStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerIntersectionOfSandwichSplitStatement
public import Development.WeilBound.CoreStatements.FlagImmersions.EqOfSpecializesGenPt
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace RootFieldNumerics

theorem global_model_tower_fifth_condition : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.I5 II ∧ T.I6 II := by
  intro hG E _ _ _ _ H D Xo l c Y _ T o II _ _ hII hp _
  have hG' := hG
  obtain ⟨-, -, -, -, hRes, -, hF, hGaga, -⟩ := hG'
  refine GlobalTheory.T.tower_intersection_of_sandwich_split hG (GlobalTheory.T.flat_zero_from_resolution_and_gaga hRes hGaga) E H D l (Xo l) c Y T o II hII.1
    (splitComps_of_origin o.toTowerOrigin) fun B a p hpS => ?_
  haveI : Fact p.Prime := ⟨(o.Or B a).𝔐.S_prime p hpS⟩
  exact GlobalTheory.T.exists_sandwich_of_hodge_tate_free hF E H D l (Xo l) c _ _ Y (o.S B) _ _ _ _ (o.Or B a).𝔐 p hpS (by omega) (o.omVB B a p hpS)

end RootFieldNumerics
