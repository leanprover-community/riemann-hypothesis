module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ConeSite
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusCoordinateIsUnit
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

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.ConeUnit

theorem yQ_appLE_isUnit {K : Type} [Field K] {X : Scheme.{0}} {N m e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (k k' : Fin m)
    (W : X.Opens) (h1 : W ≤ uy i y k) (h2 : W ≤ uy i y k') :
    IsUnit ((i.appLE _ W h2).hom (yQ y hy k k')) := by
  have ha : y k' ∈ grK K N e := (MvPolynomial.mem_homogeneousSubmodule e (y k')).2 (hy k')
  have hb : y k ∈ grK K N e := (MvPolynomial.mem_homogeneousSubmodule e (y k)).2 (hy k)
  have ha1 : y k' ∈ grK K N (1 • e) := by simpa using ha
  have hb1 : y k ∈ grK K N (1 • e) := by simpa using hb
  have hVx : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k' * y k) := by
    rw [Proj.basicOpen_mul]
    exact le_inf h2 h1
  have e1 := congrArg (fun φ => φ.hom (HomogeneousLocalization.Away.mk _ ha 1 (y k) hb1))
    (Proj.awayMap_awayToSection (grK K N) hb (x := y k' * y k) rfl)
  have e2 := congrArg (fun φ => φ.hom (HomogeneousLocalization.Away.mk _ hb 1 (y k') ha1))
    (Proj.awayMap_awayToSection (grK K N) ha (x := y k' * y k) (mul_comm _ _))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at e1 e2
  have e3 : (i.appLE _ W h2).hom (yQ y hy k k') = (i.appLE _ W hVx).hom
      ((Proj.awayToSection (grK K N) (y k' * y k)).hom
        (HomogeneousLocalization.awayMap (grK K N) hb (x := y k' * y k) rfl
          (HomogeneousLocalization.Away.mk _ ha 1 (y k) hb1))) := by
    rw [e1, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  refine IsUnit.of_mul_eq_one ((i.appLE _ W hVx).hom ((Proj.awayToSection (grK K N) (y k' * y k)).hom
        (HomogeneousLocalization.awayMap (grK K N) ha (x := y k' * y k) (mul_comm _ _)
          (HomogeneousLocalization.Away.mk _ hb 1 (y k') ha1)))) ?_
  rw [e3, ← map_mul, ← map_mul, GlobalTheory.CompanionTheory.GeoUnit.awayMap_ratio_mul ha hb hb1 ha1, map_one, map_one]

end GlobalTheory.CompanionTheory.ConeUnit
