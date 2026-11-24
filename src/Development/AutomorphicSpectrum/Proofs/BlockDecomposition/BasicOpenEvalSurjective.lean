module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.Geo

theorem evV_surjective : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), IsClosedImmersion i → ∀ {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ} (hg : g ∈ grK K N e), 0 < e → Function.Surjective (evV i g (i ⁻¹ᵁ Proj.basicOpen (grK K N) g) le_rfl) := by
  intro K _ X N i hi g e hg he
  have hU : IsAffineOpen (Proj.basicOpen (grK K N) g) := Proj.isAffineOpen_basicOpen (grK K N) g hg he
  have hiso : IsIso (Proj.awayToSection (grK K N) g) := (Proj.basicOpenIsoAway (grK K N) g hg he).isIso_hom
  have h1 : Function.Surjective (Proj.awayToSection (grK K N) g).hom :=
    (ConcreteCategory.bijective_of_isIso (Proj.awayToSection (grK K N) g)).2
  have h2 : Function.Surjective (i.appLE _ (i ⁻¹ᵁ Proj.basicOpen (grK K N) g) le_rfl).hom := by
    rw [Scheme.Hom.appLE_eq_app]
    exact i.app_surjective _ hU
  exact h2.comp h1

end GlobalTheory.CompanionTheory.Geo
