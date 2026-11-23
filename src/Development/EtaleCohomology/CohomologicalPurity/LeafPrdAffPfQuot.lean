module

public import Development.EtaleCohomology.CohomologicalPurity.LeafPrdAffPf
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
public import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem quotC_bij (d : ℕ) (R : Type) [CommRing R] :
    Function.Bijective ((Ideal.Quotient.mk (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R)))).comp
      MvPolynomial.C) := by
  have hJ : Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R) = MvPolynomial.X '' Set.univ := Set.image_univ.symm
  constructor
  · rw [injective_iff_map_eq_zero]
    intro r hr
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, hJ, MvPolynomial.mem_ideal_span_X_image] at hr
    by_contra h
    obtain ⟨i, -, hi⟩ := hr 0 (by rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C, if_pos rfl]; exact h)
    exact hi rfl
  · intro y
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨MvPolynomial.constantCoeff p, ?_⟩
    rw [RingHom.comp_apply, Ideal.Quotient.eq, hJ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra hcon
    push_neg at hcon
    have : m = 0 := Finsupp.ext fun i => hcon i (Set.mem_univ i)
    subst this
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, MvPolynomial.coeff_C, if_pos rfl,
      ← MvPolynomial.constantCoeff_eq, sub_self] at hm
    exact hm rfl

theorem leafAffQuot_pf : LeafAffQuot := by
  intro hQ d R B C _ _ _ ψ η hψ I K hη hK hI
  subst hK
  have hJI : (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R))).map ψ = I := by
    rw [Ideal.map_span, ← Set.range_comp]; exact hI
  subst hJI
  have b2 := hψ.2
  have b3 := hQ B C η _ hη
  have e : (Ideal.Quotient.mk _).comp (η.comp (ψ.comp MvPolynomial.C)) =
      ((Ideal.quotientMap _ η Ideal.le_comap_map).comp (Ideal.quotientMap _ ψ Ideal.le_comap_map)).comp
        ((Ideal.Quotient.mk (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R)))).comp
          MvPolynomial.C) := by
    ext r; simp [Ideal.quotientMap_mk]
  rw [e]
  exact (b3.comp b2).comp (quotC_bij d R)

theorem LeafPrdAff_of' (hT : LeafThom) (hA : LeafActNat) (h1 : LeafHensH) (h3 : LeafExcAff)
    (hQ : LeafQuot) (hI : LeafIndExc) : LeafPrdAff :=
  LeafPrdAff_of hT hA h1 leafAffQuot_pf h3 hQ hI

end LateralTheory.CohomologicalPurity.TubeCut
