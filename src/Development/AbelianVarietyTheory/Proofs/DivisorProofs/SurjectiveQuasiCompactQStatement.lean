module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveQuasiCompactQ
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.ray_q_surjective_and_quasiCompact : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X] {oa : D.OAct O} (Y : Ray oa), Surjective Y.q.left ∧ QuasiCompact Y.q.left := by
  first | exact @GlobalTheory.RayEv.Ray.surjective_quasiCompact_q | exact GlobalTheory.RayEv.Ray.surjective_quasiCompact_q | (intros; apply GlobalTheory.RayEv.Ray.surjective_quasiCompact_q <;> assumption)
