module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjSpaceHom
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.Geo

theorem preimage_basicOpen_nonempty_of_mk_ne_zero {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ}
    (i : X ⟶ PSpace K N) (hX : IsIntegral X) {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ} (he : 0 < e)
    (hg : g ∈ grK K N e) (hne : Ideal.Quotient.mk (homIdeal i) g ≠ 0) :
    ((i ⁻¹ᵁ Proj.basicOpen (grK K N) g : X.Opens) : Set X).Nonempty := by
  by_contra hE
  apply hne
  rw [Ideal.Quotient.eq_zero_iff_mem]
  apply Ideal.subset_span
  have hg' : g ∈ grK K N (e • 1) := by simpa using hg
  refine ⟨e, hg', fun j => ?_⟩
  have hy : HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) e g hg' =
      HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hg := by
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.Away.isLocalizationElem, HomogeneousLocalization.Away.val_mk]
  rw [hy, ← basicOpen_eq_bot_iff]
  have hb := GroundTheory.Arith.SchemeCoh.ProjHom.basicOpen_awayToSection_isLocalizationElem (grK K N)
    (xv_mem K N j) one_pos hg he
  have h2 : X.basicOpen (evV i (MvPolynomial.X j) (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) le_rfl
      (HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hg)) =
      i ⁻¹ᵁ (PSpace K N).basicOpen (Proj.awayToSection (grK K N) (MvPolynomial.X j)
        (HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hg)) := by
    rw [Scheme.preimage_basicOpen]
    simp only [evV, Scheme.Hom.appLE_eq_app]
    rfl
  rw [h2, hb, eq_bot_iff]
  intro x hx
  exact hE ⟨x, hx.2⟩

end GlobalTheory.CompanionTheory.Geo
