module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamMemLpOfNe
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaF
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaI
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothDefs
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.MultOne
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsEquiv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Decomp
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaG
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaH
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdegTransfer
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaL
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormula
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaC
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ClosureK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ExistsExpEqOfMemKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Taylor
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RightDerivativeToL2
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsKfin
import Mathlib.RingTheory.PiTensorProduct
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.ClosGenStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.RorthFunctionalEqZero

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaL, ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaM, ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormula

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaL =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaL", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaL\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ClosureK\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ExistsExpEqOfMemKset\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Taylor\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RightDerivativeToL2\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaF\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaA\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

section Datum

variable [CompleteSpace H]

theorem tf_phi (dual : Bool) {lam : Fin n → ℝ} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hsm : ∀ v : D, IsSmoothVecU ε σ v) {V : Submodule ℂ D} (hgap : StdGap ε lam)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) {y : D} (hy : y ∈ genSub E V) :
    ∃ Φ : tensSub (n := n) (genSub E V) →ₗ[ℂ] smD ε (tfRdiag ε),
      (∀ f, ((Φ f : smD ε (tfRdiag ε)) : tfL2n ε) = tfPh dual ε σ (y : H) (fun c => ((f.1 c : D) : H))) ∧
      ∀ a b (f : tensSub (n := n) (genSub E V)), smE ε (tfRdiag ε) a b (Φ f) =
        Φ ⟨tensF dual E a b f.1, tensSub_stable dual a b f.1 f.2⟩ := by
  have hce := fun c f hf => coef_embed dual hσ hD hsm hgap hV hc hVK hW _
    (tf_single_smul_mem c (tfSgn ε c) hy) f hf
  simp only [tf_coe_single] at hce
  let Φ : tensSub (n := n) (genSub E V) →ₗ[ℂ] smD ε (tfRdiag ε) :=
    { toFun := fun f => ⟨tfPh dual ε σ (y : H) (fun c => ((f.1 c : D) : H)),
        tfRdiag_smooth fun c => toL2_mem_smD_of_isSmoothL2 (hce c f.1 f.2).1⟩
      map_add' := fun f f' => Subtype.ext (vectorL2_ext fun c => by
        refine Eq.trans ?_ (toL2_add_smooth ε ((hce c f.1 f.2).1.2 []) ((hce c f'.1 f'.2).1.2 []))
        refine toL2_congr_of_eq_on_UJset fun g _ => ?_
        simp [coefMap, tensGrp, sum_add_distrib])
      map_smul' := fun a f => Subtype.ext (vectorL2_ext fun c => by
        refine Eq.trans ?_ (toL2_smul_smooth ε a _)
        refine toL2_congr_of_eq_on_UJset fun g _ => ?_
        simp only [coefMap, tensGrp, Submodule.coe_smul, Pi.smul_apply, map_smul,
          smul_comm _ a, ← Finset.smul_sum, inner_smul_right, smul_eq_mul, ← Finset.mul_sum]) }
  refine ⟨Φ, fun f => rfl, fun a b f => Subtype.ext (vectorL2_ext fun c => ?_)⟩
  refine (tfRdiag_smE (fun c => toL2_mem_smD_of_isSmoothL2 (hce c f.1 f.2).1) a b c).trans ?_
  refine (rightDerivative_toL2 (hce c f.1 f.2).1 a b).trans (toL2_congr_of_eq_on_UJset fun g hg => ?_)
  exact (hce c f.1 f.2).2.1 a b g hg

end Datum

end ReciprocityTheory.ChartRestriction.DS.G2
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaL =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaM =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaM", "h": "module\n\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsKfin\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaF\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaI\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaL\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaC\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem tf_datum2 (dual : Bool) {lam lam' : Fin n → ℝ} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hsm : ∀ v : D, IsSmoothVecU ε σ v) {V : Submodule ℂ D} (hgap : StdGap ε lam)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ (closGen E V)) d) {y : D} (hy : y ∈ genSub E V)
    (hy0 : (y : H) ≠ 0) {V' : Submodule ℂ D} (hV' : IsKIrrHW ε E (lowK ε lam') V')
    (hc' : ∀ v ∈ V', casimir E v = (casVal lam' : ℂ) • v)
    (hVK' : ∀ k ∈ Kset ε, ∀ v ∈ V', ∃ w ∈ V', (w : H) = σ k v)
    {ι : D →ₗ[ℂ] (Fin n → D)} (hι : IsGKEmb dual ε σ E (genSub E V) (genSub E V') ι) :
    ∃ V₂ : Submodule ℂ (smD ε (tfRdiag ε)), IsKIrrHW ε (smE ε (tfRdiag ε)) (lowK ε lam') V₂ ∧
      (∀ v ∈ V₂, casimir (smE ε (tfRdiag ε)) v = (casVal lam' : ℂ) • v) ∧
      (∀ k ∈ Kset ε, ∀ v ∈ V₂, ∃ w ∈ V₂, (w : tfL2n ε) = tfRdiag ε k v) ∧ V₂ ≠ ⊥ ∧
      (∀ v ∈ genSub (smE ε (tfRdiag ε)) V₂, ∃ x ∈ genSub E V',
        (v : tfL2n ε) = tfPh dual ε σ (y : H) (fun c => ((ι x c : D) : H))) ∧
      (∀ x ∈ genSub E V', ∃ v ∈ genSub (smE ε (tfRdiag ε)) V₂,
        (v : tfL2n ε) = tfPh dual ε σ (y : H) (fun c => ((ι x c : D) : H))) := by
  obtain ⟨Φ, hΦ, hΦE⟩ := tf_phi dual hσ hD hsm hgap hV hc hVK hW hy
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (tensSub (n := n) (genSub E V))
  let π := Submodule.projectionOnto _ q hq
  let Ψ : D →ₗ[ℂ] smD ε (tfRdiag ε) := Φ ∘ₗ π ∘ₗ ι
  have hΨ : ∀ x (hx : x ∈ genSub E V'), Ψ x = Φ ⟨ι x, hι.1 x hx⟩ := by
    intro x hx
    show Φ (π (ι x)) = _
    congr 1
    exact Submodule.projectionOnto_apply_left hq ⟨ι x, hι.1 x hx⟩
  have hΨc : ∀ x ∈ genSub E V', (Ψ x : tfL2n ε) = tfPh dual ε σ (y : H) (fun c => ((ι x c : D) : H)) :=
    fun x hx => by rw [hΨ x hx, hΦ]
  have hΨE : ∀ a b, ∀ x ∈ genSub E V', Ψ (E a b x) = smE ε (tfRdiag ε) a b (Ψ x) := by
    intro a b x hx
    rw [hΨ _ (tset_genSub_E E V' a b hx), hΨ x hx, hΦE]
    congr 1
    exact Subtype.ext (hι.2.2.1 a b x hx)
  have hV'le : V' ≤ genSub E V' := fun x hx => Submodule.mem_sInf.mpr fun _ hT => hT.1 hx
  have hinj : ∀ x ∈ genSub E V', Ψ x = 0 → x = 0 := by
    intro x hx h
    have h1 : tfPh dual ε σ (y : H) (fun c => ((ι x c : D) : H)) = 0 := by
      rw [← hΨc x hx, h]; rfl
    exact hι.2.1 x hx (tf_ph_inj dual hσ hD hsm hgap hV hc hVK hW hd hy hy0 (hι.1 x hx) h1)
  have hK2 := tf_kirr_map hV' Ψ (fun a b x hx => hΨE a b x (hV'le hx)) (fun x hx => hinj x (hV'le hx))
  refine ⟨V'.map Ψ, hK2, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxG := hV'le hx
    have e : casimir (smE ε (tfRdiag ε)) (Ψ x) = Ψ (casimir E x) := by

      simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
      refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      rw [hΨE a b _ (tset_genSub_E E V' b a hxG), hΨE b a x hxG]
    rw [e, hc' x hx, map_smul]
  · rintro k hk _ ⟨x, hx, rfl⟩
    obtain ⟨x', hx', hxx'⟩ := hVK' k hk x hx
    refine ⟨Ψ x', ⟨x', hx', rfl⟩, ?_⟩
    have hk' : k ∈ UJset ε := closure_inUJ_of_mem_Kset hk
    rw [hΨc x' (hV'le hx'), hΨc x (hV'le hx), tfRdiag_tfPh dual hσ hk', tf_tensGrp_kDiag dual hk,
      ← hι.2.2.2 k hk x (hV'le hx) x' (hV'le hx') hxx']
  · intro h
    obtain ⟨w, hw, hw0, -⟩ := hK2.2.2.2
    apply hw0
    have hwb : w ∈ (⊥ : Submodule ℂ (smD ε (tfRdiag ε))) := h ▸ hw
    exact (Submodule.mem_bot ℂ).1 hwb
  · intro v hv
    have hle : genSub (smE ε (tfRdiag ε)) (V'.map Ψ) ≤ (genSub E V').map Ψ := by
      refine sInf_le ⟨Submodule.map_mono hV'le, ?_⟩
      rintro a b _ ⟨x, hx, rfl⟩
      exact ⟨E a b x, tset_genSub_E E V' a b hx, hΨE a b x hx⟩
    obtain ⟨x, hx, rfl⟩ := hle hv
    exact ⟨x, hx, hΨc x hx⟩
  · intro x hx
    have hle : genSub E V' ≤ (genSub (smE ε (tfRdiag ε)) (V'.map Ψ)).comap Ψ ⊓ genSub E V' := by
      refine sInf_le ⟨fun z hz => ⟨Submodule.mem_sInf.mpr fun _ hT => hT.1 ⟨z, hz, rfl⟩, hV'le hz⟩, ?_⟩
      rintro a b z ⟨hz1, hz2⟩
      refine ⟨?_, tset_genSub_E E V' a b hz2⟩
      show Ψ (E a b z) ∈ genSub (smE ε (tfRdiag ε)) (V'.map Ψ)
      rw [hΨE a b z hz2]
      exact tset_genSub_E _ _ a b hz1
    exact ⟨Ψ x, (hle hx).1, hΨc x hx⟩

theorem tf_eq_case (dual : Bool) {lam lam' : Fin n → ℝ} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hsm : ∀ v : D, IsSmoothVecU ε σ v) {V : Submodule ℂ D} (hgap : StdGap ε lam)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ (closGen E V)) d) {y : D} (hy : y ∈ genSub E V)
    (hy0 : (y : H) ≠ 0) {P : Module.End ℂ (Fin n → D)} (hP : IsGKEndo dual ε σ E (genSub E V) P)
    {V' : Submodule ℂ D} {ι : D →ₗ[ℂ] (Fin n → D)} (hι : ∀ x ∈ genSub E V', ι x ∈ tensSub (genSub E V))
    (hgap' : StdGap ε lam') {V₂ : Submodule ℂ (smD ε (tfRdiag ε))}
    (hV₂ : IsKIrrHW ε (smE ε (tfRdiag ε)) (lowK ε lam') V₂)
    (hc₂ : ∀ v ∈ V₂, casimir (smE ε (tfRdiag ε)) v = (casVal lam' : ℂ) • v)
    (hVK₂ : ∀ k ∈ Kset ε, ∀ v ∈ V₂, ∃ w ∈ V₂, (w : tfL2n ε) = tfRdiag ε k v)
    (hgen : ∀ v ∈ genSub (smE ε (tfRdiag ε)) V₂, ∃ x ∈ genSub E V',
        (v : tfL2n ε) = tfPh dual ε σ (y : H) (fun c => ((ι x c : D) : H)))
    (hin : ∀ f ∈ tensSub (genSub E V),
      tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H)) ∈ closGen (smE ε (tfRdiag ε)) V₂) :
    ∀ f ∈ tensSub (genSub E V), ∃ x ∈ genSub E V', P f = ι x := by
  obtain ⟨Φ, hΦ, -⟩ := tf_phi dual hσ hD hsm hgap hV hc hVK hW hy
  intro f hf
  obtain ⟨W, hWf, hfW, hWle, hWK⟩ := tf_kfin_tens dual hσ hD hV.1 hV.2.1 hf
  let P' : Module.End ℂ (tensSub (n := n) (genSub E V)) := P.restrict hP.1
  let W' : Submodule ℂ (tensSub (n := n) (genSub E V)) := W.comap (tensSub (genSub E V)).subtype
  have hW'f : FiniteDimensional ℂ W' := Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe hWle).symm
  let S0 : Submodule ℂ (tfL2n ε) := W'.map ((smD ε (tfRdiag ε)).subtype ∘ₗ Φ ∘ₗ P')
  have hS0v : ∀ w : tensSub (n := n) (genSub E V),
      ((smD ε (tfRdiag ε)).subtype ∘ₗ Φ ∘ₗ P') w = tfPh dual ε σ (y : H) (fun c => ((P w.1 c : D) : H)) :=
    fun w => hΦ (P' w)
  have hS0 : S0 ≤ closGen (smE ε (tfRdiag ε)) V₂ := by
    rintro _ ⟨w, -, rfl⟩
    rw [hS0v]
    exact hin w.1 w.2
  have hS0f : FiniteDimensional ℂ S0 := Module.Finite.map _ _
  have hS0K : ∀ k ∈ Kset ε, ∀ x ∈ S0, tfRdiag ε k x ∈ S0 := by
    rintro k hk _ ⟨w, hw, rfl⟩
    obtain ⟨w', hw', hww'⟩ := hWK k hk w.1 hw
    refine ⟨⟨w', hWle hw'⟩, hw', ?_⟩
    rw [hS0v, hS0v, tfRdiag_tfPh dual hσ (closure_inUJ_of_mem_Kset hk), tf_tensGrp_kDiag dual hk,
      hP.2.2 k hk w.1 w.2 w' (hWle hw') hww']
  have hkf := data_kfin_le hgap' (tfRdiag_isURepOn ε) (isDerivedOn_smE (tfRdiag_isURepOn ε)) hV₂ hc₂ hVK₂
    S0 hS0 hS0f hS0K
  have hfS0 : tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H)) ∈ S0 :=
    ⟨⟨f, hf⟩, hfW, hS0v ⟨f, hf⟩⟩
  obtain ⟨v, hv, hve⟩ := hkf hfS0
  obtain ⟨x, hx, hxe⟩ := hgen v hv
  refine ⟨x, hx, ?_⟩
  have hd0 : (P f - ι x) ∈ tensSub (genSub E V) := Submodule.sub_mem _ (hP.1 f hf) (hι x hx)
  have e1 : Φ ⟨P f - ι x, hd0⟩ = Φ ⟨P f, hP.1 f hf⟩ - Φ ⟨ι x, hι x hx⟩ := by
    rw [← map_sub]; rfl
  have h0 : tfPh dual ε σ (y : H) (fun c => (((P f - ι x) c : D) : H)) = 0 := by
    calc tfPh dual ε σ (y : H) (fun c => (((P f - ι x) c : D) : H))
        = ((Φ ⟨P f - ι x, hd0⟩ : smD ε (tfRdiag ε)) : tfL2n ε) := (hΦ ⟨P f - ι x, hd0⟩).symm
      _ = ((Φ ⟨P f, hP.1 f hf⟩ : smD ε (tfRdiag ε)) : tfL2n ε) -
          ((Φ ⟨ι x, hι x hx⟩ : smD ε (tfRdiag ε)) : tfL2n ε) := by rw [e1, Submodule.coe_sub]
      _ = 0 := by
        rw [sub_eq_zero]
        exact ((hΦ ⟨P f, hP.1 f hf⟩).trans hve.symm).trans (hxe.trans (hΦ ⟨ι x, hι x hx⟩).symm)
  exact sub_eq_zero.1 (tf_ph_inj dual hσ hD hsm hgap hV hc hVK hW hd hy hy0 hd0 h0)

end ReciprocityTheory.ChartRestriction.DS.G2
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaM =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormula =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormula", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormula\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap\npublic import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothDefs\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.MultOne\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamMemLpOfNe\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsEquiv\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.ClosGenStable\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Decomp\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaG\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaH\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaI\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaM\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdegTransfer\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.RorthFunctionalEqZero\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaA\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

open MeasureTheory

def closRep {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (S : Submodule ℂ H) [S.HasOrthogonalProjection] (g : Matrix (Fin n) (Fin n) ℂ) : S →L[ℂ] S :=
  S.orthogonalProjection ∘L σ g ∘L S.subtypeL

theorem trace_nonneg (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε))
    {P : Module.End ℂ (Fin n → D)} (hP : IsGKEndo dual ε σ E (genSub E V) P)
    (hPP : ∀ f ∈ tensSub (genSub E V), P (P f) = P f)
    (hPB : ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V), formB ε (P f) g = formB ε f (P g))
    {z : ℂ} (hEP : ∀ f ∈ tensSub (genSub E V), eeF dual E (P f) = z • P f)
    {c : ℂ} (hc : ∀ x ∈ genSub E V, ptr P x = c • x) :
    c.im = 0 ∧ 0 ≤ c.re ∧ (c = 0 → ∀ f ∈ tensSub (genSub E V), P f = 0) := by
  rename_i hcas
  have hPB' : ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V),
      tfFormBH ε (fun c => ((P f c : D) : H)) (fun c => ((g c : D) : H)) =
        tfFormBH ε (fun c => ((f c : D) : H)) (fun c => ((P g c : D) : H)) := hPB
  have hcore : ∀ y ∈ V, (y : H) ≠ 0 → ∃ r : ℝ, 0 ≤ r ∧ c = r ∧ (c = 0 → ∀ b, P (Pi.single b y) = 0) :=
    fun y hy hy0 => tf_trace_core dual hσ hD hsm hgap hV hcas hVK hW hP hPP hPB' hEP hc hy hy0
  obtain ⟨y0, hy0V, hy00, -⟩ := hV.2.2.2
  have hy0H : (y0 : H) ≠ 0 := fun h => hy00 (Subtype.ext h)
  obtain ⟨r, hr, hcr, -⟩ := hcore y0 hy0V hy0H
  refine ⟨by rw [hcr, Complex.ofReal_im], by rw [hcr, Complex.ofReal_re]; exact hr, fun h0 => ?_⟩
  have hV0 : ∀ y ∈ V, ∀ b, P (Pi.single b y) = 0 := by
    intro y hy b
    by_cases hyz : (y : H) = 0
    · have hy' : y = 0 := Subtype.ext hyz
      rw [hy', Pi.single_zero, map_zero]
    · obtain ⟨-, -, -, h⟩ := hcore y hy hyz
      exact h h0 b
  have hVt : ∀ f ∈ tensSub V, P f = 0 := by
    intro f hf

    rw [← Finset.univ_sum_single f, map_sum]
    exact sum_eq_zero fun b _ => hV0 _ ((tset_mem.1 hf) b) b
  have hle : tensSub (genSub E V) ≤ tensSub (genSub E V) ⊓ LinearMap.ker P := by
    refine tfg_gen dual E V _ (fun f hf => ⟨tset_mem.2 fun b => rorth_le_genSub ((tset_mem.1 hf) b), hVt f hf⟩) ?_
    intro a b f hf
    refine ⟨tensSub_stable dual a b f hf.1, ?_⟩
    show P (tensF dual E a b f) = 0
    rw [hP.2.1 a b f hf.1, show P f = 0 from hf.2, map_zero]
  intro f hf
  exact (hle hf).2

theorem trace_ge (dual : Bool) {lam lam' : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε))
    {V' : Submodule ℂ D} (hgap' : StdGap ε lam') (hV' : IsKIrrHW ε E (lowK ε lam') V')
    (hc' : ∀ v ∈ V', casimir E v = (casVal lam' : ℂ) • v)
    (hVK' : ∀ k ∈ Kset ε, ∀ v ∈ V', ∃ w ∈ V', (w : H) = σ k v)
    (hSq : Formalism.MainNotions.S.IsSqIntOn ε (closRep σ (closGen E V)))
    (hSq' : Formalism.MainNotions.S.IsSqIntOn ε (closRep σ (closGen E V')))
    {P : Module.End ℂ (Fin n → D)} (hP : IsGKEndo dual ε σ E (genSub E V) P)
    (hPP : ∀ f ∈ tensSub (genSub E V), P (P f) = P f)
    (hPB : ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V), formB ε (P f) g = formB ε f (P g))
    {z : ℂ} (hEP : ∀ f ∈ tensSub (genSub E V), eeF dual E (P f) = z • P f)
    {c : ℂ} (hc : ∀ x ∈ genSub E V, ptr P x = c • x)
    {ι : D →ₗ[ℂ] (Fin n → D)} (hι : IsGKEmb dual ε σ E (genSub E V) (genSub E V') ι)
    (hιP : ∀ x ∈ genSub E V', P (ι x) = ι x) {w : closGen E V} (hw : w ≠ 0) {w' : closGen E V'} (hw' : w' ≠ 0) :
    Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) (closRep σ (closGen E V')) w' /
              Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) (closRep σ (closGen E V)) w ≤ c.re ∧
      (c.re = Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) (closRep σ (closGen E V')) w' /
          Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) (closRep σ (closGen E V)) w →
        ∀ f ∈ tensSub (genSub E V), ∃ x ∈ genSub E V', P f = ι x) := by
  rename_i hcas
  have hPB' : ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V),
      tfFormBH ε (fun c => ((P f c : D) : H)) (fun c => ((g c : D) : H)) =
        tfFormBH ε (fun c => ((f c : D) : H)) (fun c => ((P g c : D) : H)) := hPB
  obtain ⟨d, hd⟩ := tfClRep_fdeg hgap hσ hD hV hcas hVK hSq
  obtain ⟨d', hd'⟩ := tfClRep_fdeg hgap' hσ hD hV' hc' hVK' hSq'
  have hfd : Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) (closRep σ (closGen E V)) w = d :=
    fdegOf_of_isFdeg' hd hw
  have hfd' : Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) (closRep σ (closGen E V')) w' = d' :=
    fdegOf_of_isFdeg' hd' hw'
  rw [hfd, hfd']
  obtain ⟨y0, hy0V, hy00, -⟩ := hV.2.2.2
  have hy0H : (y0 : H) ≠ 0 := fun h => hy00 (Subtype.ext h)
  have hy0G : y0 ∈ genSub E V := rorth_le_genSub hy0V
  obtain ⟨HP, wv, hHPc, hHPeq, hst, hrep, hc0eq⟩ :=
    tf_trace_data dual hσ hD hsm hgap hV hcas hVK hW hP hPP hPB' hEP hc hy0V hy0H hd
  obtain ⟨V₂, hV₂, hc₂, hVK₂, hV₂0, hgen1, -⟩ :=
    tf_datum2 dual hσ hD hsm hgap hV hcas hVK hW hd hy0G hy0H hV' hc' hVK' hι
  have hV'0 : V' ≠ ⊥ := by
    obtain ⟨u, hu, hu0, -⟩ := hV'.2.2.2
    intro h
    apply hu0
    have hub : u ∈ (⊥ : Submodule ℂ D) := h ▸ hu
    exact (Submodule.mem_bot ℂ).1 hub
  have hR := tfRdiag_isURepOn ε
  have hDR := isDerivedOn_smE hR
  obtain ⟨U, hU⟩ := data_unitary_equiv hgap' hσ hD hV' hc' hVK' hV'0 hR hDR hV₂ hc₂ hVK₂ hV₂0
  have hschur := tf_schur_transfer (closGen E V') (closGen (smE ε (tfRdiag ε)) V₂) U hU
    (closGen_stable hgap' hσ hD hV' hc' hVK') hd'
  have hH'c : IsClosed ((closGen (smE ε (tfRdiag ε)) V₂ : Submodule ℂ (tfL2n ε)) : Set (tfL2n ε)) :=
    Submodule.isClosed_topologicalClosure _
  have hst2 := closGen_stable hgap' hR hDR hV₂ hc₂ hVK₂
  have hH'P : closGen (smE ε (tfRdiag ε)) V₂ ≤ HP := by
    refine Submodule.topologicalClosure_minimal _ ?_ hHPc
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨x, hx, hxe⟩ := hgen1 v hv
    rw [hHPeq]
    refine Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨ι x, hι.1 x hx, ?_⟩)
    show (v : tfL2n ε) = _
    rw [hxe, hιP x hx]
  have hH'0 : closGen (smE ε (tfRdiag ε)) V₂ ≠ ⊥ := by
    obtain ⟨u, hu, hu0, -⟩ := hV₂.2.2.2
    intro h
    apply hu0
    have h1 : ((u : smD ε (tfRdiag ε)) : tfL2n ε) ∈ closGen (smE ε (tfRdiag ε)) V₂ :=
      Submodule.le_topologicalClosure _ ⟨u, Submodule.mem_sInf.mpr fun _ hT => hT.1 hu, rfl⟩
    have h2 : ((u : smD ε (tfRdiag ε)) : tfL2n ε) ∈ (⊥ : Submodule ℂ (tfL2n ε)) := h ▸ h1
    exact Subtype.ext ((Submodule.mem_bot ℂ).1 h2)
  have hone : tfRdiag ε (Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε)) = 1 := hR.1.1
  have hmul : ∀ a b : Formalism.REAL.UJ ε, tfRdiag ε (Formalism.MainNotions.S.umat (a * b)) =
      (tfRdiag ε (Formalism.MainNotions.S.umat a)).comp (tfRdiag ε (Formalism.MainNotions.S.umat b)) := fun a b =>
    hR.1.2 _ (umat_mem_UJset ε a) _ (umat_mem_UJset ε b)
  have hiso : ∀ (g : Formalism.REAL.UJ ε) v, ‖tfRdiag ε (Formalism.MainNotions.S.umat g) v‖ = ‖v‖ := fun g v =>
    hR.2.1 _ (umat_mem_UJset ε g) v
  obtain ⟨hge, heq⟩ := tf_ge_abstract (μ := Formalism.REAL.muG ε) (fun g => tfRdiag ε (Formalism.MainNotions.S.umat g)) hone hmul hiso
    HP _ hH'c hH'P (fun g v hv => hst2 _ (umat_mem_UJset ε g) v hv) hH'0 wv hrep hd'.1 hschur
  have hdpos : 0 < d := hd.1
  have hre : c.re = (∑ i, ‖wv i‖ ^ 2) / d := by rw [hc0eq, Complex.ofReal_re]
  refine ⟨by rw [hre]; exact div_le_div_of_nonneg_right hge hdpos.le, fun h => ?_⟩
  have hT : ∑ i, ‖wv i‖ ^ 2 = d' := by
    rw [hre, div_left_inj' hdpos.ne'] at h
    exact h
  have hle := heq hT
  refine tf_eq_case dual hσ hD hsm hgap hV hcas hVK hW hd hy0G hy0H hP hι.1 hgap' hV₂ hc₂ hVK₂ hgen1 ?_
  intro f hf
  apply hle
  rw [hHPeq]
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, hf, rfl⟩)

theorem eigenProj_formB (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (z : ℂ) {P : Module.End ℂ (Fin n → D)}
    (hPM : ∀ f ∈ tensSub (genSub E V), P f ∈ tensSub (genSub E V)) (hPz : ∀ f ∈ tensSub (genSub E V), eeF dual E (P f) = z • P f)
    (hP1 : ∀ f ∈ tensSub (genSub E V), eeF dual E f = z • f → P f = f)
    (hP0 : ∀ f ∈ tensSub (genSub E V), ∀ z' : ℂ, z' ≠ z → eeF dual E f = z' • f → P f = 0) :
    ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V), formB ε (P f) g = formB ε f (P g) := by
  obtain ⟨Bs, hdec, hreal⟩ := ee_decomp dual hσ hD hgap hV hc hVK hW
  have horth : ∀ x y : Fin n → D, ∀ a b : ℂ, a.im = 0 → eeF dual E x = a • x → eeF dual E y = b • y → a ≠ b →
      formB ε x y = 0 := by
    intro x y a b ha hx hy hab
    have h := eeF_formB_symm dual hσ hD (ε := ε) x y
    rw [hx, hy, formB_smul_left, formB_smul_right] at h
    have hca : starRingEnd ℂ a = a := Complex.conj_eq_iff_im.mpr ha
    rw [hca] at h
    have h2 : (a - b) * formB ε x y = 0 := by rw [sub_mul, h, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd (sub_eq_zero.mp h3) hab
    · exact h3
  have hL : ∀ f ∈ tensSub (genSub E V), ∀ h ∈ tensSub (genSub E V), formB ε (P f) (h - P h) = 0 := by
    intro f hf h hh
    obtain ⟨hb, hbe, rfl⟩ := hdec h hh

    rw [map_sum, ← sum_sub_distrib, formB_sum_right]
    refine sum_eq_zero fun b _ => ?_
    by_cases hbz : ((b : ℝ) : ℂ) = z
    · rw [hP1 _ (hbe b).1 (by rw [(hbe b).2, hbz]), sub_self, formB_zero_right]
    · rw [hP0 _ (hbe b).1 _ hbz (hbe b).2, sub_zero]
      by_cases hPf : P f = 0
      · rw [hPf, formB_zero_left]
      · obtain ⟨b0, _, hb0⟩ := hreal z (P f) (hPM f hf) hPf (hPz f hf)
        exact horth _ _ z _ (by rw [hb0]; simp) (hPz f hf) (hbe b).2 (Ne.symm hbz)
  intro f hf g hg
  have e1 : formB ε (P f) g = formB ε (P f) (P g) := by
    have := hL f hf g hg
    rw [formB_sub_right, sub_eq_zero] at this
    exact this
  have e2 : formB ε f (P g) = formB ε (P f) (P g) := by
    have := hL g hg f hf
    rw [formB_sub_right, sub_eq_zero] at this
    rw [← formB_conj, this, formB_conj]
  rw [e1, e2]

end ReciprocityTheory.ChartRestriction.DS.G2
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormula =====
