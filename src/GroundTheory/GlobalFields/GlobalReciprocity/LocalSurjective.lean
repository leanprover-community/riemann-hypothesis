module

public import GroundTheory.GlobalFields.NormResidueSymbol.RangeFiniteLocalNormLeKerLocalSymbol
public import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialLocal
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
import Mathlib.Tactic.TypeStar

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField SemiLocal AdeleBaseChange IdeleGroup
open scoped Pointwise

noncomputable section

section NormResidue

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [CharZero k] {M : Type*} [Field M] [Algebra k M] [FiniteDimensional k M] [IsGalois k M]
  [IsMulCommutative (M ≃ₐ[k] M)]

theorem normResidueSymbol_surjective : Function.Surjective (normResidueSymbol k M) := by
  have := isAbelianGalois_of_isGalois (k := k) (M := M)
  intro τ
  obtain ⟨x, hx⟩ := LocalField.surjective_localArtinMapOfField (K := k) (L := M) τ
  refine ⟨x, ?_⟩
  rw [← hx]
  exact congrArg (fun f : kˣ →* (M ≃ₐ[k] M) ↦ f x) normResidueSymbol_eq_localArtinMapOfField

end NormResidue

section Place

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] (v : HeightOneSpectrum (𝓞 K))

theorem exists_localSymbol_eq (w : PlacesOver L v) {τ : L ≃ₐ[K] L}
    (hτ : τ ∈ MulAction.stabilizer (L ≃ₐ[K] L) w.1.asIdeal) :
    ∃ x : (v.adicCompletion K)ˣ, localSymbol L v x = τ := by
  obtain ⟨x, hx⟩ := normResidueSymbol_surjective (decompositionMulEquiv v w.1 ⟨τ, hτ⟩)
  refine ⟨x, ?_⟩
  rw [localSymbol_eq_symbolAt L v w]
  change (((decompositionMulEquiv v w.1).symm
    (normResidueSymbol (v.adicCompletion K) (w.1.adicCompletion L) x)) : L ≃ₐ[K] L) = τ
  rw [hx, MulEquiv.symm_apply_apply]


omit [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] in
theorem mk_finiteEmbedding_normUnits (w : PlacesOver L v) (z : (w.1.adicCompletion L)ˣ) :
    IdeleClassGroup.mk K (finiteEmbedding v
        (LocalField.normUnits (v.adicCompletion K) (w.1.adicCompletion L) z)) =
      ideleClassNorm K L (IdeleClassGroup.mk L (finiteEmbedding w.1 z)) := by
  rw [ideleClassNorm_mk, ideleNorm_finiteEmbedding]
  obtain ⟨w, hw⟩ := w
  have h := (below_eq_iff w v).2 hw
  subst h
  rfl

end Place

end

end GroundTheory.Global
