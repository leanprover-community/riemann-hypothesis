module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GeoCoord

theorem exists_coord_basicOpen {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    {W : X.Opens} (hW : IsAffineOpen W) (g : Γ(X, W)) {d : ℕ} (s : Fin d → Γ(X, W)) :
    letI := (strV q W).toAlgebra
    (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g))
      (fun k => algebraMap Γ(X, W) (Localization.Away g) (s k)) :
        MvPolynomial (Fin d) K →+* Localization.Away g).Etale →
    ∃ c : Coord q (X.basicOpen g) d, ∀ k, c.t k = resO (X.basicOpen_le g) (s k) := by
  letI := (strV q W).toAlgebra
  intro h
  haveI := hW.isLocalization_basicOpen g
  let φ := IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) Γ(X, X.basicOpen g)
  have hφ : ∀ x, φ (algebraMap Γ(X, W) (Localization.Away g) x) = resO (X.basicOpen_le g) x :=
    fun x => φ.commutes x
  refine ⟨⟨hW.basicOpen g, fun k => resO (X.basicOpen_le g) (s k), ?_⟩, fun _ => rfl⟩
  have h2 := RingHom.Etale.stableUnderComposition _ _ h
    (RingHom.Etale.of_bijective (f := (φ : Localization.Away g →+* Γ(X, X.basicOpen g))) φ.bijective)
  have e : (MvPolynomial.eval₂Hom (strV q (X.basicOpen g)) (fun k => resO (X.basicOpen_le g) (s k)) :
        MvPolynomial (Fin d) K →+* Γ(X, X.basicOpen g)) =
      (φ : Localization.Away g →+* Γ(X, X.basicOpen g)).comp
        (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g))
          (fun k => algebraMap Γ(X, W) (Localization.Away g) (s k))) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun k => ?_)
    · simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, RingHom.comp_apply]
      rw [strV_res q (X.basicOpen_le g), RingHom.comp_apply, IsScalarTower.algebraMap_apply K Γ(X, W) (Localization.Away g)]
      exact (hφ _).symm
    · simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, RingHom.comp_apply]
      exact (hφ _).symm
  rw [e]
  exact h2

end GlobalTheory.CompanionTheory.GeoCoord
