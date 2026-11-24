module

public import GroundTheory.LocalFields.NormCorrespondence
public import GroundTheory.LocalFields.OpenCompletion
public import GroundTheory.LocalFields.LocalArtinMap
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
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

namespace GroundTheory.LocalField

open Abstract ValuativeRel

section Restrict

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]

theorem restrictAb_eq_of_le {E E' : IntermediateField F Ω} [Normal F E] [Normal F E']
    (hE' : E' ≤ maximalAbelianExtension F Ω) (hEE' : E ≤ E')
    {σ τ : maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω}
    (h : restrictAb E' hE' σ = restrictAb E' hE' τ) :
    restrictAb E (hEE'.trans hE') σ = restrictAb E (hEE'.trans hE') τ := by
  ext y
  have := congrArg (fun ρ : E' ≃ₐ[F] E' => ((ρ ⟨y, hEE' y.2⟩ : E') : Ω)) h
  simp only [restrictAb_apply] at this ⊢
  exact this

end Restrict

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

section ClassField


variable (K Ω) in
def classField (H : openFiniteIndex Kˣ) : finiteAbelianExtensions K Ω :=
  (normGroupOrderIso K Ω).symm (OrderDual.toDual ⟨H.1, H.2⟩)

theorem range_normUnits_classField (H : openFiniteIndex Kˣ) :
    (normUnits K (classField K Ω H : IntermediateField K Ω)).range = H.1 :=
  congrArg (fun y => (OrderDual.ofDual y).1)
    ((normGroupOrderIso K Ω).apply_symm_apply (OrderDual.toDual ⟨H.1, H.2⟩))

end ClassField

section Coord


variable (K Ω) in
def artinCoord (H : openFiniteIndex Kˣ) :
    (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) →* Kˣ ⧸ H.1 :=
  have := (classField K Ω H).2.1
  have := (classField K Ω H).2.2
  (QuotientGroup.quotientMulEquivOfEq (range_normUnits_classField H)).toMonoidHom.comp
    ((localReciprocityAbelian (classField K Ω H : IntermediateField K Ω)).toMonoidHom.comp
      (restrictAb _ (le_maximalAbelianExtension _)))

theorem artinCoord_eq_of (H : openFiniteIndex Kˣ)
    (σ : maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) (x : Kˣ)
    (h : have := (classField K Ω H).2.1; have := (classField K Ω H).2.2
      restrictAb (classField K Ω H : IntermediateField K Ω) (le_maximalAbelianExtension _) σ =
        restrictAb _ (le_maximalAbelianExtension _) (localArtinMap K Ω x)) :
    artinCoord K Ω H σ = (x : Kˣ ⧸ H.1) := by
  have := (classField K Ω H).2.1
  have := (classField K Ω H).2.2
  simp only [artinCoord, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [h, restrictAb_localArtinMap, MulEquiv.apply_symm_apply, QuotientGroup.quotientMulEquivOfEq_mk]

theorem artinCoord_localArtinMap (H : openFiniteIndex Kˣ) (x : Kˣ) :
    artinCoord K Ω H (localArtinMap K Ω x) = (x : Kˣ ⧸ H.1) :=
  artinCoord_eq_of H _ x rfl

theorem continuous_artinCoord (H : openFiniteIndex Kˣ) : Continuous (artinCoord K Ω H) := by
  have := (classField K Ω H).2.1
  have := (classField K Ω H).2.2
  change Continuous ((fun ρ => (QuotientGroup.quotientMulEquivOfEq (range_normUnits_classField (Ω := Ω) H)).toFun
    (localReciprocityAbelian (classField K Ω H : IntermediateField K Ω) ρ)) ∘
      restrictAb _ (le_maximalAbelianExtension _))
  exact continuous_of_discreteTopology.comp (continuous_restrictAb _ _)

end Coord

section Completion



end Completion

end GroundTheory.LocalField
