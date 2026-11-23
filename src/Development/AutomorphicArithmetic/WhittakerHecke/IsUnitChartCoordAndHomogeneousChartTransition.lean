module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjSpaceHom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.ResolutionOfSingularities.Foundations.Blowup.ReesGrading

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor FunctorialResolution.Blowup
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem projective_chart_overlap {R : Type} [CommRing R] {N : ℕ} {W : Scheme.{0}} (h : W ⟶ PSpace R N)
    (O : W.Opens) (a b : Fin (N + 1))
    (ha : O ≤ h ⁻¹ᵁ Proj.basicOpen (grading R N) (X a))
    (hb : O ≤ h ⁻¹ᵁ Proj.basicOpen (grading R N) (X b))
    (n : ℕ) (F : MvPolynomial (Fin (N + 1)) R) (hF : F ∈ grading R N (n • 1)) :
    h.appLE _ O ha (chartHom a F) *
        h.appLE _ O hb (chartHom b (X a : MvPolynomial (Fin (N + 1)) R)) ^ n =
      h.appLE _ O hb (chartHom b F) := by
  have hO : O ≤ h ⁻¹ᵁ Proj.basicOpen (grading R N) (X b * X a) := by
    rw [Proj.basicOpen_mul]
    exact fun x hx => ⟨hb hx, ha hx⟩
  have e1 : h.appLE _ O ha =
      (PSpace R N).presheaf.map (homOfLE (basicOpen_mul_le_right a b)).op ≫ h.appLE _ O hO :=
    (Scheme.Hom.map_appLE h hO _).symm
  have e2 : h.appLE _ O hb =
      (PSpace R N).presheaf.map (homOfLE (basicOpen_mul_le_left a b)).op ≫ h.appLE _ O hO :=
    (Scheme.Hom.map_appLE h hO _).symm
  have hF' : F ∈ grading R N n := by simpa using hF
  rw [e1, e2]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  rw [chartHom_of_mem a hF']
  exact map_mul_pow_eq _ _ (chart_identity a b hF)

theorem UpperTheory.isUnit_chart_coord_and_homogeneous_chart_transition :
    ∀ {R : Type} [CommRing R] {N : ℕ} {W : Scheme.{0}} (h : W ⟶ PSpace R N) (O : W.Opens) (a b : Fin (N + 1))
        (ha : O ≤ h ⁻¹ᵁ Proj.basicOpen (grading R N) (X a)) (hb : O ≤ h ⁻¹ᵁ Proj.basicOpen (grading R N) (X b)),
        IsUnit (h.appLE _ O hb (chartHom b (X a : MvPolynomial (Fin (N + 1)) R))) ∧
        ∀ (n : ℕ) (F : MvPolynomial (Fin (N + 1)) R), F.IsHomogeneous n →
          h.appLE _ O ha (chartHom a F) * h.appLE _ O hb (chartHom b (X a : MvPolynomial (Fin (N + 1)) R)) ^ n =
            h.appLE _ O hb (chartHom b F) := by
  intro R _ N W h O a b ha hb
  refine ⟨?_, fun n F hF => projective_chart_overlap h O a b ha hb n F ?_⟩
  · have key := projective_chart_overlap h O a b ha hb 1 (X b) (by simpa using X_mem b)
    rw [pow_one, chartHom_X_self, map_one] at key
    exact IsUnit.of_mul_eq_one_right _ key
  · have : F ∈ grading R N n := hF
    simpa using this
