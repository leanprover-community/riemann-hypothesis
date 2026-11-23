module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwDet
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwMb
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwSub
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwTate
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem tw_ok : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s) (g : HostAut H) (a : TwIso D g), TwOK o g a := by
  intro E _ _ _ H D l B _ b S s o g a
  obtain ⟨hm1, hm2⟩ := tw_mb E H l g
  refine ⟨fun x hx => o.eta_ker _ (tw_sub _ g.s D.La (a.a l.M) l.Mb hm1.le x hx), fun k _ _ x β hx => ?_⟩
  obtain ⟨hd, I, h1, h2, h3⟩ := o.geom k x β hx
  obtain ⟨J, hJ1, hJ2⟩ := tw_tate E H D g a k _ _ _ I
  refine ⟨tw_det E H D g S _ _ k x _ hd, J, by rw [hJ1]; exact h1, fun y => ?_, fun y hy => ?_⟩
  · rw [hJ2]
    exact h2 _
  · rw [hJ2]
    exact h3 _ (tw_sub _ g.s D.La (a.a l.M) _ hm2.le y hy)

end PositivityTheory.UnitarySelfGeneration
