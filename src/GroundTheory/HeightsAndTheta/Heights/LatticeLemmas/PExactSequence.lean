module

public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField TensorProduct ComplexAt

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace HermitianBundle

variable (M : HermitianBundle K) (F : Submodule (𝓞 K) M.carrier) (hF : M.Saturated F)

theorem quotFibreMap_mkQ_of_orthogonal (σ : K →+* ℂ) (x : Fibre σ M.carrier)
    (hx : FibreSpace.equiv M.metric σ x ∈ (subFibre M.metric σ F)ᗮ) :
    quotFibreMap M F hF σ (fibreMap σ F.mkQ x) = FibreSpace.equiv M.metric σ x := by
  have := quot_projective hF
  set V := subFibre M.metric σ F
  set z := fibreMap σ (quotSection M F hF) (fibreMap σ F.mkQ x) - x with hzdef
  have hex := lTensor_exact (ComplexAt σ) (LinearMap.exact_subtype_mkQ F) F.mkQ_surjective
  have h0 : F.mkQ.lTensor (ComplexAt σ) z = 0 := by
    change fibreMap σ F.mkQ z = 0
    rw [hzdef, map_sub, fibreMap_fibreMap, fibreMap_fibreMap,
      mkQ_comp_quotSection, LinearMap.id_comp, sub_self]
  obtain ⟨y, hy⟩ := (hex z).mp h0
  have hz : FibreSpace.equiv M.metric σ z ∈ V := ⟨y, congrArg (FibreSpace.equiv M.metric σ) hy⟩
  have hsplit : FibreSpace.equiv M.metric σ (fibreMap σ (quotSection M F hF) (fibreMap σ F.mkQ x)) =
      FibreSpace.equiv M.metric σ x + FibreSpace.equiv M.metric σ z := by
    rw [hzdef, map_sub]
    abel
  change Vᗮ.starProjection
      (FibreSpace.equiv M.metric σ (fibreMap σ (quotSection M F hF) (fibreMap σ F.mkQ x))) = _
  rw [hsplit, map_add (f := _), Submodule.starProjection_orthogonal_apply_eq_zero hz, add_zero,
    Submodule.starProjection_eq_self_iff.mpr hx]

def subQuotExtension : HermitianExtension (M.sub F) M (M.quot F hF) where
  incl := F.subtype
  proj := F.mkQ
  incl_injective := F.injective_subtype
  proj_surjective := F.mkQ_surjective
  exact := LinearMap.exact_subtype_mkQ F
  incl_isometric _ _ _ := rfl
  proj_coisometric σ x y hx hy := by
    have hmem : ∀ z : Fibre σ M.carrier,
        (∀ w, (M.metric.form σ).inner (F.subtype.lTensor (ComplexAt σ) w) z = 0) →
          FibreSpace.equiv M.metric σ z ∈ (subFibre M.metric σ F)ᗮ := by
      intro z hz
      rw [Submodule.mem_orthogonal]
      rintro u ⟨w, rfl⟩
      exact hz w
    change inner ℂ (quotFibreMap M F hF σ (fibreMap σ F.mkQ x))
      (quotFibreMap M F hF σ (fibreMap σ F.mkQ y)) = _
    rw [quotFibreMap_mkQ_of_orthogonal M F hF σ x (hmem x hx),
      quotFibreMap_mkQ_of_orthogonal M F hF σ y (hmem y hy)]
    rfl

end HermitianBundle

namespace LatticeLemmas

end LatticeLemmas

end

end GroundTheory.Heights₂.Heights
