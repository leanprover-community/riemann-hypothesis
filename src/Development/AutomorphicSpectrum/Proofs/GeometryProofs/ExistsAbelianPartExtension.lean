module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTorusExtensionFiniteStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionAbelianQuotientStatement
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

theorem abPart_exists (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S)
    (L : Type) [Field L] [NumberField L] (z : Sp L ⟶ S) :
    ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (e : L →+* L'), Nonempty (AbPart t (spMap e ≫ z)) := by
  obtain ⟨L', _, _, hfin, ⟨τ⟩⟩ := GlobalTheory.T.exists_torus_extension_finite S t.G t.semi L z
  have : CharZero L' := charZero_of_injective_algebraMap (algebraMap L L').injective
  have : NumberField L' := NumberField.of_module_finite L L'
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.proved_CubePullSt (spMap (algebraMap L L') ≫ z) t
  obtain ⟨tB, e, he, ha, hp⟩ := GlobalTheory.T.torus_extension_abelian_quotient E H L'
    ⟨(Over.pullback (spMap (algebraMap L L') ≫ z)).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
      OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩ τ
  exact ⟨L', _, inferInstance, algebraMap L L', ⟨⟨_, m, τ, tB, e, he, ha, hp⟩⟩⟩

end GlobalTheory.CompanionTheory.Ar
