module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyContinuousCofilteredAffineLimitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfEtaleCohomologyEquivalenceDiagramStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem eqv_of_iso (R : Type) [CommRing R] (F : Shv R) {E E' : Spc} (f : E ≅ E') : Eqv R f.hom F := by
  intro n
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R f.inv F n, fun x => ?_, fun y => ?_⟩
  · rw [← pull_comp, Iso.inv_hom_id, pull_id]
  · rw [← pull_comp, Iso.hom_inv_id, pull_id]

theorem contCone_of_represented : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (D : I ⥤ PSh) (c : Cone D), IsLimit c → (∀ i, ∃ Z : Scheme.{0}, IsAffine Z ∧ Nonempty (yoneda.obj Z ≅ D.obj i)) → (∃ Z : Scheme.{0}, Nonempty (yoneda.obj Z ≅ c.pt)) → ContCone R F (disc.mapCone c) := by
  intro R _ F hF I _ _ D c hc hD hpt
  choose Z hZ he using hD
  obtain ⟨Z0, ⟨e0⟩⟩ := hpt
  let e : ∀ i, yoneda.obj (Z i) ≅ D.obj i := fun i => (he i).some

  let G : I ⥤ Scheme.{0} :=
    { obj := Z
      map := fun {i j} f => yoneda.preimage ((e i).hom ≫ D.map f ≫ (e j).inv)
      map_id := fun i => yoneda.map_injective (by simp)
      map_comp := fun {i j k} f g => yoneda.map_injective (by simp) }
  let isoYD : G ⋙ yoneda ≅ D := NatIso.ofComponents e (fun {i j} f => by simp [G])

  let s : Cone G :=
    { pt := Z0
      π :=
        { app := fun i => yoneda.preimage (e0.hom ≫ c.π.app i ≫ (e i).inv)
          naturality := fun i j f => yoneda.map_injective (by simp [G]) } }
  have hs : IsLimit s := by
    apply isLimitOfReflects yoneda
    have h1 : IsLimit ((Cone.postcompose isoYD.inv).obj c) := (IsLimit.postcomposeInvEquiv isoYD c).symm hc
    refine h1.ofIsoLimit (Cone.ext e0.symm (fun i => ?_))
    simp [s]
    rfl
  have h0 : ContCone R F (sch.mapCone s) := GlobalTheory.T.cohomologyContinuous_cofiltered_affine_limit R F hF I G s hs hZ
  let αI : G ⋙ sch ≅ D ⋙ disc := (Functor.associator G yoneda disc).symm ≪≫ Functor.isoWhiskerRight isoYD disc
  let βI : sch.obj Z0 ≅ disc.obj c.pt := disc.mapIso e0
  refine (GlobalTheory.T.of_etaleCohomologyEquivalence_diagram R F I (G ⋙ sch) (D ⋙ disc) (sch.mapCone s) (disc.mapCone c) αI.hom βI.hom
    (fun i => ?_) (fun i => eqv_of_iso R F (αI.app i)) (eqv_of_iso R F βI)).mp h0
  simp only [Functor.mapCone_π_app, αI, βI, s, sch, Functor.comp_map]
  simp [isoYD, ← Functor.map_comp]

end GlobalTheory
