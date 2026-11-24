module

import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamMemLpOfNe
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SqIntA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.ClosGenStable
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaD
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaF
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaG
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.RorthFunctionalEqZero

import all ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaH
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaC
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaB

@[expose] public section

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem tf_trace_data (dual : Bool) {lam : Fin n → ℝ} [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε))
    {P : Module.End ℂ (Fin n → D)} (hP : IsGKEndo dual ε σ E (genSub E V) P)
    (hPP : ∀ f ∈ tensSub (genSub E V), P (P f) = P f)
    (hPB : ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V),
      tfFormBH ε (fun c => ((P f c : D) : H)) (fun c => ((g c : D) : H)) =
        tfFormBH ε (fun c => ((f c : D) : H)) (fun c => ((P g c : D) : H)))
    {z : ℂ} (hEP : ∀ f ∈ tensSub (genSub E V), eeF dual E (P f) = z • P f)
    {c0 : ℂ} (hc0 : ∀ x ∈ genSub E V, ptr P x = c0 • x) {y : D} (hyV : y ∈ V) (hy0 : (y : H) ≠ 0) {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ (closGen E V)) d) :
    ∃ (HP : Submodule ℂ (tfL2n ε)) (w : Fin n → tfL2n ε), IsClosed (HP : Set (tfL2n ε)) ∧
      HP = (Submodule.span ℂ {v : tfL2n ε | ∃ f ∈ tensSub (genSub E V),
        v = tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H))}).topologicalClosure ∧
      (∀ g ∈ UJset ε, ∀ v ∈ HP, tfRdiag ε g v ∈ HP) ∧
      (∀ v ∈ HP, ∀ c, ((v c : L2 ε) : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε]
        fun g => inner ℂ (w c) (tfRdiag ε (Formalism.MainNotions.S.umat g) v)) ∧
      c0 = (((∑ c, ‖w c‖ ^ 2) / d : ℝ) : ℂ) := by
  have hyG : y ∈ genSub E V := rorth_le_genSub hyV
  have hyC : (y : H) ∈ closGen E V := Submodule.le_topologicalClosure _ ⟨y, hyG, rfl⟩
  exact ReciprocityTheory.ChartRestriction.DS.tf_trace_data_of_closed_stability dual hσ hP hPP hPB hc0 hyV hy0 hd
    (closGen_stable hgap hσ hD hV hc hVK)
    (tf_closure_stable dual hσ hD hsm hgap hV hc hVK hW hP hEP hyG)
    (fun hf => tf_ph_memLp dual hσ hD hsm hgap hV hc hVK hW hyG hf)
    (fun hζ hζ' hm hm' => tensor_functor_separation dual hσ hD hgap hV hc hVK hd hyC hζ hζ' hm hm')

end ReciprocityTheory.ChartRestriction.DS.G2
