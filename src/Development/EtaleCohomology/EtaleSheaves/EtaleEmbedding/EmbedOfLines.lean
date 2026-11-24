module

public import Development.EtaleCohomology.EtaleSheaves.EtaleEmbedding
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut

namespace LateralTheory.E.EmbedPf

def LineChart : Prop := ∀ {L S : Scheme.{0}} (l : L ⟶ S), IsLine l → ∀ (R : Type) [CommRing R]
  (j0 : Spec (CommRingCat.of R) ⟶ S), IsOpenImmersion j0 →
    ∃ j : Spec (CommRingCat.of (Polynomial R)) ⟶ L, IsOpenImmersion j ∧
      j ≫ l = Spec.map (CommRingCat.ofHom Polynomial.C) ≫ j0

theorem chart_of (hEx : LineEx) (hLC : LineChart) : Chart := by
  intro A _ n
  induction n with
  | zero =>
    let E := (MvPolynomial.isEmptyAlgEquiv A (Fin 0)).symm.toRingEquiv.toCommRingCatIso
    have hE : E.hom = CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin 0) A)) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact (MvPolynomial.isEmptyAlgEquiv A (Fin 0)).symm.commutes a
    refine ⟨Spec (CommRingCat.of A), 𝟙 _, Spec.map E.hom, IterLine.iso _ inferInstance, inferInstance, ?_⟩
    rw [Category.comp_id, hE]
  | succ n ih =>
    obtain ⟨P, q, j, hq, hj, hjq⟩ := ih
    obtain ⟨L, l, hl⟩ := hEx P
    obtain ⟨j1, hj1, hj1l⟩ := hLC l hl (MvPolynomial (Fin n) A) j hj
    let F := (MvPolynomial.finSuccEquiv A n).symm
    let E := F.toRingEquiv.toCommRingCatIso
    have hE : CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A)) ≫ CommRingCat.ofHom Polynomial.C ≫ E.hom =
        CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin (n + 1)) A)) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      have h1 : (Polynomial.C (algebraMap A (MvPolynomial (Fin n) A) a)) =
          algebraMap A (Polynomial (MvPolynomial (Fin n) A)) a := rfl
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
      rw [h1]
      exact F.commutes a
    have hj1' := hj1
    refine ⟨L, l ≫ q, Spec.map E.hom ≫ j1, IterLine.comp l q hl hq, inferInstance, ?_⟩
    rw [Category.assoc, reassoc_of% hj1l, hjq, ← hE, Spec.map_comp, Spec.map_comp, Category.assoc]

end LateralTheory.E.EmbedPf
