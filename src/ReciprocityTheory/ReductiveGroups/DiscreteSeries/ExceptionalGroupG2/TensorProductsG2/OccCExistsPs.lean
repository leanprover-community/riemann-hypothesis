module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CompactIsDSUniqueOfCas
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsKfin
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.ProjectionCommutesDerivedAction
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccBLowKShiftF
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.OccurrencePhiKEquivariant
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.ContinuousUnitaryMatrix
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.OccCExistsPs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumIrr
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.FormulaF
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RightDerivativeToL2

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccurrencePhiKEquivariant, ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccurrencePhiSmoothL2, ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccCExistsPs

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccurrencePhiKEquivariant =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccurrencePhiKEquivariant", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.OccurrencePhiKEquivariant\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CompactIsDSUniqueOfCas\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumA\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumIrr\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsKfin\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.ProjectionCommutesDerivedAction\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.ContinuousUnitaryMatrix\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Finset MeasureTheory
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

section Mem

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}
  {v₀ : T.V} {v₀' : T'.V}

theorem occurrence_projection_mem (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hgap' : StdGap ε lam') (hP' : IsPsiFor ε lam' T' Ψ') (hv₀' : v₀' ≠ 0)
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))
    (η f : Fin n → smD ε (rreg ε)) (hη : η ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)))
    (hf : f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))) :
    (Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η f) ∈
      (genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀')).map (smD ε (rreg ε)).subtype := by
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hV := datumV_isKIrrHW hP hv₀
  obtain ⟨j, hj⟩ := tensor_generated_mem_layer hD.glRep hV.2.1 hf
  set W := layer ε (smE ε (rreg ε)) (datumV ε Ψ v₀) j with hWdef
  have : FiniteDimensional ℂ W := finiteDimensional_layer hV.1 j
  have hWM : ∀ u : Fin n → W, (fun c => ((u c : W) : smD ε (rreg ε))) ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) :=
    fun u => (tset_mem).2 fun c => layer_le_genSub j (u c).2
  let P := (Hlam ε Ψ' v₀').starProjection
  let Φ : (Fin n → W) →ₗ[ℂ] L2 ε :=
    { toFun := fun u => P (occC2phi dual ε η (fun c => ((u c : W) : smD ε (rreg ε))))
      map_add' := fun u u' => by
        have e : (fun c => (((u + u') c : W) : smD ε (rreg ε))) =
            (fun c => ((u c : W) : smD ε (rreg ε))) + (fun c => ((u' c : W) : smD ε (rreg ε))) := by
          funext c; simp
        rw [e, occurrence_phi_add dual hW hη (hWM u) (hWM u'), map_add (f := _)]
      map_smul' := fun a u => by
        have e : (fun c => (((a • u) c : W) : smD ε (rreg ε))) = a • (fun c => ((u c : W) : smD ε (rreg ε))) := by
          funext c; simp
        simp only [RingHom.id_apply]
        rw [e, occurrence_phi_smul, map_smul] }
  have hSf : FiniteDimensional ℂ (LinearMap.range Φ) := LinearMap.finiteDimensional_range Φ
  have hS : LinearMap.range Φ ≤ closGen (smE ε (rreg ε)) (datumV ε Ψ' v₀') := by
    rintro x ⟨u, rfl⟩
    exact Submodule.starProjection_apply_mem (Hlam ε Ψ' v₀') _
  have hSK : ∀ k ∈ Kset ε, ∀ x ∈ LinearMap.range Φ, rreg ε k x ∈ LinearMap.range Φ := by
    rintro k hk x ⟨u, rfl⟩
    have hy := fun d => layer_k_stable hσ hD hV.2.1 (datumV_kStable hP v₀) j k hk (u d : W) (u d).2
    choose y hyW hy using hy
    let u' : Fin n → W := fun c => ∑ d, (cond dual (star (k c d)) (k c d)) • (⟨y d, hyW d⟩ : W)
    refine ⟨u', ?_⟩
    show P _ = rreg ε k (P _)
    rw [← projection_commutes_right_regular hgap' hP' hv₀' k (cf_kset_sub hk)]
    congr 1
    refine (occurrence_phi_k_equivariant dual η _ _ hk ?_).symm
    funext c
    simp only [u', kDiag, Submodule.coe_sum, Submodule.coe_smul, hy]
  have hle := data_kfin_le hgap' hσ hD (datumV_isKIrrHW hP' hv₀') (datumV_casimir hP' v₀') (datumV_kStable hP' v₀')
    (LinearMap.range Φ) hS hSf hSK
  apply hle
  refine ⟨fun c => ⟨f c, hj c⟩, ?_⟩
  rfl

end Mem

end ReciprocityTheory.ChartRestriction.DS.G2
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccurrencePhiKEquivariant =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccurrencePhiSmoothL2 =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccurrencePhiSmoothL2", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccBLowKShiftF\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Ring.IsFormallyReal\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumA\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.FormulaF\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.OccCExistsPs\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Finset MeasureTheory
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

section Psi

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}
  {v₀ : T.V} {v₀' : T'.V}

theorem occurrence_pairing (dual : Bool) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hP' : IsPsiFor ε lam' T' Ψ')
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))
    (hB : ∃ (ξ ζ : Fin n → T.V) (v' : T'.V), ∫ g : Formalism.REAL.UJ ε,
      starRingEnd ℂ (occPsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) * inner ℂ v₀' (Ψ' (Formalism.MainNotions.S.umat g) v')
        ∂(Formalism.REAL.muG ε) ≠ 0) :
    ∃ η ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), ∃ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      ∃ x' ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'),
        inner ℂ (toL2 ε (occCoef dual (rreg ε) (fun c => ((η c : smD ε (rreg ε)) : L2 ε))
          (fun c => ((f c : smD ε (rreg ε)) : L2 ε)))) ((x' : smD ε (rreg ε)) : L2 ε) ≠ 0 := by
  obtain ⟨ξ, ζ, v', hI⟩ := hB
  have hσ := rreg_isURepOn ε
  let jm : T.V → smD ε (rreg ε) := fun v => ⟨uniformisationL2 ε Ψ v₀ v, datumEmbedding_mem_smooth hP v₀ v⟩
  have hjm : ∀ v, jm v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀) := fun v =>
    layer_le_genSub (ε := ε) 0 ((mem_datumV_iff hP v₀ _).2 ⟨v, rfl⟩)
  have hη : (fun c => jm (ξ c)) ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) := tset_mem.2 fun c => hjm _
  have hf : (fun c => jm (ζ c)) ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) := tset_mem.2 fun c => hjm _
  refine ⟨fun c => jm (ξ c), hη, fun c => jm (ζ c), hf, ⟨uniformisationL2 ε Ψ' v₀' v', datumEmbedding_mem_smooth hP' v₀' v'⟩,
    layer_le_genSub (ε := ε) 0 ((mem_datumV_iff hP' v₀' _).2 ⟨v', rfl⟩), ?_⟩
  have hF : ∀ g, inUJ ε g → occCoef dual (rreg ε) (fun c => ((jm (ξ c) : smD ε (rreg ε)) : L2 ε))
      (fun c => ((jm (ζ c) : smD ε (rreg ε)) : L2 ε)) g =
      ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) * occPsiCoef dual Ψ ξ ζ g := by
    intro g hg
    have hg' : g ∈ UJset ε := hg
    simp only [occCoef, occPsiCoef, tensGrp, jm, inner_sum, inner_smul_right, formulaF hgap hP hv₀ hg',
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  have hM1 : MemLp (fun g : Formalism.REAL.UJ ε => (fun g => ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) *
      occPsiCoef dual Ψ ξ ζ g) (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) :=
    (occA_coef_memLp dual hσ hW _ _ hη hf).ae_eq (Filter.Eventually.of_forall fun g => hF _ g.2)
  have e1 : toL2 ε (occCoef dual (rreg ε) (fun c => ((jm (ξ c) : smD ε (rreg ε)) : L2 ε))
      (fun c => ((jm (ζ c) : smD ε (rreg ε)) : L2 ε))) =
      toL2 ε (fun g => ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) * occPsiCoef dual Ψ ξ ζ g) := toL2_congr_of_forall_inUJ_eq hF
  have e2 : inner ℂ (toL2 ε (fun g => ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) * occPsiCoef dual Ψ ξ ζ g))
      (toL2 ε (jfun Ψ' v₀' v')) = starRingEnd ℂ (((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ)) *
        ∫ g : Formalism.REAL.UJ ε, starRingEnd ℂ (occPsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) *
          inner ℂ v₀' (Ψ' (Formalism.MainNotions.S.umat g) v') ∂(Formalism.REAL.muG ε) := by
    rw [inner_toL2_eq_theta_pairing ε (F := fun g => ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) * occPsiCoef dual Ψ ξ ζ g)
      (G := jfun Ψ' v₀' v') hM1 (dt_memLp hP' v₀' v'), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [map_mul, jfun, mul_assoc]
  have hC : starRingEnd ℂ (((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    rw [Complex.conj_ofReal]
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.2 (datumEmbedding_highest_ne_zero hgap hP hv₀))
  have ex : ((⟨uniformisationL2 ε Ψ' v₀' v', datumEmbedding_mem_smooth hP' v₀' v'⟩ : smD ε (rreg ε)) : L2 ε) = toL2 ε (jfun Ψ' v₀' v') := rfl
  rw [ex]
  show inner ℂ (toL2 ε (occCoef dual (rreg ε) (fun c => ((jm (ξ c) : smD ε (rreg ε)) : L2 ε))
      (fun c => ((jm (ζ c) : smD ε (rreg ε)) : L2 ε)))) (toL2 ε (jfun Ψ' v₀' v')) ≠ 0
  rw [e1, e2]
  exact mul_ne_zero hC hI

end Psi

end ReciprocityTheory.ChartRestriction.DS.G2
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccurrencePhiSmoothL2 =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccCExistsPs =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccCExistsPs", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccBLowKShiftF\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CompactIsDSUniqueOfCas\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumA\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RightDerivativeToL2\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccurrencePhiKEquivariant\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccurrencePhiSmoothL2\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.ProjectionCommutesDerivedAction\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.OccCExistsPs\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Finset MeasureTheory
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

section Psi

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}
  {v₀ : T.V} {v₀' : T'.V}

theorem occC_pairing (dual : Bool) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hP' : IsPsiFor ε lam' T' Ψ')
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))
    (hB : ∃ (ξ ζ : Fin n → T.V) (v' : T'.V), ∫ g : Formalism.REAL.UJ ε,
      starRingEnd ℂ (occPsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) * inner ℂ v₀' (Ψ' (Formalism.MainNotions.S.umat g) v')
        ∂(Formalism.REAL.muG ε) ≠ 0) :
    ∃ η ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), ∃ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      ∃ x' ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'),
        inner ℂ (toL2 ε (occCoef dual (rreg ε) (fun c => ((η c : smD ε (rreg ε)) : L2 ε))
          (fun c => ((f c : smD ε (rreg ε)) : L2 ε)))) ((x' : smD ε (rreg ε)) : L2 ε) ≠ 0 := by
  exact occurrence_pairing dual hgap hP hv₀ hP' hW hB

theorem occC_exists_ps (dual : Bool) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hgap' : StdGap ε lam') (hP' : IsPsiFor ε lam' T' Ψ') (hv₀' : v₀' ≠ 0)
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))
    (hne : ∃ η ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), ∃ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      ∃ x' ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'),
        inner ℂ (toL2 ε (occCoef dual (rreg ε) (fun c => ((η c : smD ε (rreg ε)) : L2 ε))
          (fun c => ((f c : smD ε (rreg ε)) : L2 ε)))) ((x' : smD ε (rreg ε)) : L2 ε) ≠ 0) :
    ∃ ps : (Fin n → smD ε (rreg ε)) →ₗ[ℂ] smD ε (rreg ε),
      occPsOK dual ε (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) (genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀')) ps ∧
      ∃ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), ps f ≠ 0 := by
  obtain ⟨η, hη, f₀, hf₀, x', hx', hne0⟩ := hne
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hsm : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), occC2phi dual ε η f ∈ smD ε (rreg ε) :=
    fun f hf => toL2_mem_smD_of_isSmoothL2 (occurrence_phi_smooth_L2 dual hW hη hf)
  have hsmP : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      (Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η f) ∈ smD ε (rreg ε) :=
    fun f hf => projection_preserves_smooth hgap' hP' hv₀' _ (hsm f hf)
  let ps0 : tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) →ₗ[ℂ] smD ε (rreg ε) :=
    { toFun := fun f => ⟨(Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η f.1), hsmP f.1 f.2⟩
      map_add' := fun f f' => Subtype.ext (by
        show (Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η (f.1 + f'.1)) = _
        rw [occurrence_phi_add dual hW hη f.2 f'.2, map_add (f := _)]
        rfl)
      map_smul' := fun a f => Subtype.ext (by
        show (Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η (a • f.1)) = _
        rw [occurrence_phi_smul, map_smul]
        rfl) }
  obtain ⟨ps, hps⟩ := LinearMap.exists_extend ps0
  have hpsf : ∀ f (hf : f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))),
      ps f = ⟨(Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η f), hsmP f hf⟩ :=
    fun f hf => LinearMap.congr_fun hps ⟨f, hf⟩
  refine ⟨ps, ⟨fun f hf => ?_, fun a b f hf => ?_, fun k hk f hf f' hf' hff => ?_⟩, f₀, hf₀, ?_⟩
  · obtain ⟨y, hy, hyeq⟩ := occurrence_projection_mem dual hP hv₀ hgap' hP' hv₀' hW η f hη hf
    have e : ps f = y := by rw [hpsf f hf]; exact Subtype.ext hyeq.symm
    rw [e]; exact hy
  · have hf2 := tensSub_stable dual a b f hf
    rw [hpsf _ hf2, hpsf f hf]
    have h3 := projection_commutes_derived_action hgap' hP' hv₀' (⟨occC2phi dual ε η f, hsm f hf⟩ : smD ε (rreg ε)) (hsmP f hf) a b
    apply Subtype.ext
    refine Eq.trans ?_ h3.symm
    show (Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η (tensF dual (smE ε (rreg ε)) a b f)) =
      (Hlam ε Ψ' v₀').starProjection ((smE ε (rreg ε) a b ⟨occC2phi dual ε η f, hsm f hf⟩ : smD ε (rreg ε)) : L2 ε)
    congr 1
    refine Eq.trans ?_ (rightDerivative_toL2 (occurrence_phi_smooth_L2 dual hW hη hf) a b).symm
    apply toL2_congr_of_forall_inUJ_eq
    intro g hg
    exact (occA_coef_Eab dual hσ hD _ f a b hg).symm
  · rw [hpsf f' hf', hpsf f hf]
    show (Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η f') =
      rreg ε k ((Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η f))
    rw [← occurrence_phi_k_equivariant dual η f f' hk hff, projection_commutes_right_regular hgap' hP' hv₀' k (cf_kset_sub hk)]
  · intro h0
    apply hne0
    have hP0 : (Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η f₀) = 0 := by
      have := congrArg Subtype.val ((hpsf f₀ hf₀).symm.trans h0)
      exact this
    have hx'H : ((x' : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ' v₀' :=
      Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem hx')
    rw [← (Submodule.starProjection_eq_self_iff (K := Hlam ε Ψ' v₀')).2 hx'H,
      ← Submodule.inner_starProjection_left_eq_right]
    show inner ℂ ((Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η f₀)) _ = 0
    rw [hP0, inner_zero_left]

end Psi

end ReciprocityTheory.ChartRestriction.DS.G2
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccCExistsPs =====
