module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlagNeZero
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlagRatioTrdeg
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Assembly
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.CoordinateConeArithVar

theorem HodgeFlagArith.proof (hNe : HodgeFlagNeZero.Statement) (hTr : HodgeFlagRatioTrdeg.Statement) :
    HodgeFlagArith.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl H B
  choose cX hcX using D.arith.2.1.2.2
  choose cP hcP using hNe II Ψ K ι Ω E D Pl H B
  let c : ∀ k, Pl.ιY k := fun
    | Sum.inl k => cX k
    | Sum.inr q => cP q.1 q.2
  have hc : ∀ k, Pl.flagGenericPoint B ⟨k, c k⟩ ≠ 0 := by
    rintro (k | q)
    · intro h
      have h0 : D.y ⟨k, cX k⟩ = 0 := by
        have h' : Pl.ofΩ (D.y ⟨k, cX k⟩) = 0 := h
        have h2 : (C (D.y ⟨k, cX k⟩) : MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) = 0 :=
          IsFractionRing.injective (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY (by rw [map_zero]; exact h')
        exact C_injective _ _ (h2.trans C_0.symm)
      apply hcX k
      rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]
    · exact hcP q.1 q.2
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : CharZero Pl.ΩY :=
    charZero_of_injective_algebraMap (IsFractionRing.injective (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY)
  have hhor : IsHorizontal (Pl.flagPrime B) := horizontal (Pl.flagGenericPoint B)
  refine ⟨⟨Sum.inl D.arith.1.some⟩, ⟨RingHom.ker_isPrime _, isMultiHomogIdeal (Pl.flagGenericPoint B),
    relevant (Pl.flagGenericPoint B) c hc⟩, hhor, ?_⟩
  have htr := ConeTrdeg.full _ Pl.ιY (ratioField (Pl.flagGenericPoint B) c) (ratioPtL (Pl.flagGenericPoint B) c)
    (birational (Pl.flagGenericPoint B) c hc)
    (fun k ↦ ⟨c k, fun h0 ↦ by
      have h1 := congrArg Subtype.val h0
      simp [ratioPtL, ratioPt, hc] at h1⟩)
    (by rw [mCoordIdeal_ratioPtL (Pl.flagGenericPoint B) c hc]; exact hhor)
  have hL : Algebra.trdeg ℤ (ratioField (Pl.flagGenericPoint B) c) = ((D.n + D.flagDim0 : ℕ) : Cardinal) := by
    rw [← hTr II Ψ K ι Ω E D Pl H B c hc]
    have hsub : (ratioField (Pl.flagGenericPoint B) c).toSubfield = Subfield.closure (coneRatios (Pl.flagGenericPoint B) c) := by
      simp only [IntermediateField.adjoin_toSubfield]
      refine le_antisymm (Subfield.closure_le.2 (Set.union_subset ?_ Subfield.subset_closure))
        (Subfield.closure_mono Set.subset_union_right)
      rintro _ ⟨q, rfl⟩
      rw [eq_ratCast]
      exact SubfieldClass.ratCast_mem _ q
    rw [← (RingEquiv.subfieldCongr hsub).toIntAlgEquiv.trdeg_eq]
    exact AlgEquiv.trdeg_eq (RingEquiv.refl _).toIntAlgEquiv
  rw [mCoordIdeal_ratioPtL (Pl.flagGenericPoint B) c hc, hL] at htr
  have : (mCoordIdeal (Pl.flagGenericPoint B)).IsPrime := RingHom.ker_isPrime _
  have hA := IntDomainDim.full (MRing Pl.ιY ⧸ mCoordIdeal (Pl.flagGenericPoint B)) (algebraMap_injective _ hhor)
  show ringKrullDim (MRing Pl.ιY ⧸ mCoordIdeal (Pl.flagGenericPoint B)) = _
  rw [hA, htr]
  rw [← Nat.cast_add, Cardinal.toENat_nat,
    show D.n + 1 + D.flagDim0 + Fintype.card (K ⊕ Ψ × Fin (D.N - 1)) =
      D.n + D.flagDim0 + Fintype.card (K ⊕ Ψ × Fin (D.N - 1)) + 1 by omega]
  push_cast
  rfl

end GroundTheory.Heights₂.Heights.LowerBoundFree
