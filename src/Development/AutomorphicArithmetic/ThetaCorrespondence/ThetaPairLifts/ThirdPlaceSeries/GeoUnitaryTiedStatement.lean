module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoUnitaryTied
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop

theorem _root_.GlobalTheory.T.row_inner_product_invariant_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → GlobalTheory.CovTop.RecTied D L →
    ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (g : p.P.Gp) x y,
      inner ℂ ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) ((p.R.toRealDat.FW i).ρ g x))
        ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) ((p.R.toRealDat.FW i).ρ g y)) =
      inner ℂ ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) x)
        ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) y) := by
  first | exact @_root_.GlobalTheory.CovTop.geoUnitary_tied_alt | exact _root_.GlobalTheory.CovTop.geoUnitary_tied_alt | (intros; apply _root_.GlobalTheory.CovTop.geoUnitary_tied_alt <;> assumption)
end
