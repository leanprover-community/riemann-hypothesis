module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaL
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaC
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ClosureK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ExistsExpEqOfMemKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Taylor
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RightDerivativeToL2
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaF

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem tf_kstable_fin (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {V0 : Submodule ℂ D}
    (hVf : FiniteDimensional ℂ V0) (hVK : IsKStableSub ε E V0) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    {v : D} (hv : v ∈ V0) : σ k (v : H) ∈ V0.map D.subtype := by
  apply ReciprocityTheory.ChartRestriction.DS.tf_kstable_fin <;> assumption

theorem tf_tensGrp_kDiag (dual : Bool) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (f : Fin n → H) :
    tensGrp dual σ k f = kDiag dual σ k f := by
  have hu : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk.1
  have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv hu
  funext c
  simp only [tensGrp, kDiag, hinv, Matrix.conjTranspose_apply]

theorem tf_kirr_map {M M' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']
    {E₁ : Fin n → Fin n → Module.End ℂ M} {E₂ : Fin n → Fin n → Module.End ℂ M'} {Λ : Fin n → ℝ}
    {V : Submodule ℂ M} (hV : IsKIrrHW ε E₁ Λ V) (Ψ : M →ₗ[ℂ] M')
    (hΨ : ∀ a b, ∀ x ∈ V, Ψ (E₁ a b x) = E₂ a b (Ψ x)) (hinj : ∀ x ∈ V, Ψ x = 0 → x = 0) :
    IsKIrrHW ε E₂ Λ (V.map Ψ) := by
  apply ReciprocityTheory.ChartRestriction.DS.tf_kirr_map <;> assumption

theorem tf_kfin_tens (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {V : Submodule ℂ D}
    (hVf : FiniteDimensional ℂ V) (hVk : IsKStableSub ε E V) {f : Fin n → D} (hf : f ∈ tensSub (genSub E V)) :
    ∃ W : Submodule ℂ (Fin n → D), FiniteDimensional ℂ W ∧ f ∈ W ∧ W ≤ tensSub (genSub E V) ∧
      ∀ k ∈ Kset ε, ∀ w ∈ W, ∃ w' ∈ W,
        (fun c => ((w' c : D) : H)) = kDiag dual σ k (fun c => ((w c : D) : H)) := by
  apply ReciprocityTheory.ChartRestriction.DS.tf_kfin_tens <;> assumption

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
