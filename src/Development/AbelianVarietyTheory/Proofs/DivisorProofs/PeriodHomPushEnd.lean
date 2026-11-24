module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicPeriodsNaturalAlongCoveredMorphismStatement
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem periodHom_push_end : PEnd := by
  intro A _ g hA L u P hP α _ M hM x x' hx
  have hsep : A.left.IsSeparated := by
    haveI : IsProper A.hom := hA.proper
    refine ⟨?_⟩
    rw [← terminal.comp_from A.hom]
    infer_instance
  have hΛ : ∀ l : u.Λ, M l ∈ u.Λ := fun l ↦ by
    rw [← u.ker, hM, (u.ker _).2 l.2, MonObj.one_comp]
  let N : u.Λ →+ u.Λ :=
    { toFun l := ⟨M l, hΛ l⟩
      map_zero' := Subtype.ext (map_zero M)
      map_add' a b := Subtype.ext (map_add M _ _) }
  obtain rfl : x' = N x := Subtype.ext hx
  refine LinearMap.ext fun c ↦ ?_
  have key := GlobalTheory.T.holomorphicPeriods_natural_along_covered_morphism (fibUnif u) (fibUnif u) hsep hsep id analyticOnNhd_id (fun _ h ↦ h) M N
    (fun _ _ _ ↦ rfl) (RingHom.id ℂ) α.left (homMor (dp0 ℂ) (𝟙 _) α).isMor (fun _ ↦ rfl)
    (fun p _ ↦ (congrArg Over.Hom.left (hM p.2)).symm) c.1 _ _ (hP c)
    (hP (primPull (dp0 ℂ) (𝟙 _) α c)) x
  exact congrArg (fun f : Hol (fibFam u).V ↦ f.1 ⟨0, trivial⟩) key

end GlobalTheory.AnPer
