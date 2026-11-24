module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedEmbeddingToM
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroDecay
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaD
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaF
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaH
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaC
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
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
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamMemLpOfNe
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SqIntA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.ClosGenStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.RorthFunctionalEqZero
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaE, ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaI

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaE =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaE", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedEmbeddingToM\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaA\nimport Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian\nimport Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamMemLpOfNe\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroDecay\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SqIntA\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.ClosGenStable\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.RorthFunctionalEqZero\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Finset MeasureTheory
open Formalism.MainNotions.S (umat)

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

private theorem memLp_of_weighted_diagonal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) (y : H)
    (hW : MemLp (fun g : Formalism.REAL.UJ ε =>
      (Real.sqrt (S7.hs (umat g)) : ℂ) * inner ℂ y (σ (umat g) y)) 2 (Formalism.REAL.muG ε)) :
    MemLp (fun g : Formalism.REAL.UJ ε => inner ℂ y (σ (umat g) y)) 2 (Formalism.REAL.muG ε) := by
  have hcont : Continuous (fun g : Formalism.REAL.UJ ε => inner ℂ y (σ (umat g) y)) :=
    continuous_const.inner ((hσ.2.2 y).comp_continuous Formalism.MainNotions.BridgeCSchur.continuous_umat
      (fun g => umat_mem_UJset ε g))
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have : Subsingleton (Formalism.REAL.UJ ε) :=
      ⟨fun a b => Subtype.ext (Units.ext (Matrix.ext fun i => Fin.elim0 (Fin.cast hn i)))⟩
    have : CompactSpace (Formalism.REAL.UJ ε) := Finite.compactSpace
    refine MemLp.of_bound hcont.aestronglyMeasurable (‖y‖ * ‖y‖)
      (Filter.Eventually.of_forall fun g => ?_)
    calc ‖inner ℂ y (σ (umat g) y)‖ ≤ ‖y‖ * ‖σ (umat g) y‖ := norm_inner_le_norm _ _
      _ = _ := by rw [hσ.2.1 _ (umat_mem_UJset ε g)]
  · refine hW.of_le hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    have hs : 1 ≤ Real.sqrt (S7.hs (umat g)) :=
      Real.one_le_sqrt.mpr (sigZeroDecay_one_le_hs (umat_mem_UJset ε g) ⟨0, hn⟩)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact le_mul_of_one_le_left (norm_nonneg _) hs

private theorem memLp_coefficients {G : Type*} [Group G] [MeasurableSpace G] {μ : Measure G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ρ : G → (H →L[ℂ] H)} (hR : ∀ h : G, MeasurePreserving (fun g => g * h) μ μ)
    (hInv : MeasurePreserving (Inv.inv : G → G) μ μ)
    (hone : ρ 1 = 1) (hmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b))
    (hiso : ∀ g v, ‖ρ g v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) →
      (∀ g, ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (y : H) (hy : y ≠ 0) (h0 : MemLp (fun g => inner ℂ y (ρ g y)) 2 μ) (v w : H) :
    MemLp (fun g => inner ℂ w (ρ g v)) 2 μ := by
  have hall (x : H) : MemLp (fun g => inner ℂ y (ρ g x)) 2 μ :=
    GraphTrick.memLp_of_ne hR hone hmul hiso hirr y y hy h0 x
  have hinv := ((hall w).comp_measurePreserving hInv).star
  have e : star ((fun g => inner ℂ y (ρ g w)) ∘ Inv.inv) = fun g => inner ℂ w (ρ g y) := by
    funext g
    have hs := GraphTrick.star_eq (ρ := ρ) hone hmul hiso g⁻¹
    simp only [Pi.star_apply, Function.comp_apply, RCLike.star_def, inner_conj_symm]
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint, hs, inv_inv]
  rw [e] at hinv
  exact GraphTrick.memLp_of_ne hR hone hmul hiso hirr w y hy hinv v

theorem tf_sqInt_of_hW {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      (Real.sqrt (S7.hs (umat g)) : ℂ) * inner ℂ (w : H) (σ (umat g) (v : H)))
      2 (Formalism.REAL.muG ε)) :
    Formalism.MainNotions.S.IsSqIntOn ε (tfClRep σ (closGen E V)) := by
  have hU := tfClRep_isURepOn hgap hσ hD hV hc hVK
  have hst := closGen_stable hgap hσ hD hV hc hVK
  let ρ : Formalism.REAL.UJ ε → (closGen E V →L[ℂ] closGen E V) :=
    fun g => tfClRep σ (closGen E V) (umat g)
  have hone : ρ 1 = 1 := by
    change tfClRep σ (closGen E V) 1 = 1
    exact hU.1.1
  have hmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b) := by
    intro a b
    exact hU.1.2 (umat a) (umat_mem_UJset ε a) (umat b) (umat_mem_UJset ε b)
  have hiso : ∀ g v, ‖ρ g v‖ = ‖v‖ := fun g v => hU.2.1 (umat g) (umat_mem_UJset ε g) v
  have hirr := Formalism.MainNotions.BridgeCSchur.irr_of (tfClRep_irred hgap hσ hD hV hc hVK)
  obtain ⟨y, hyV, hy, -⟩ := hV.2.2.2
  have hyG : y ∈ genSub E V := rorth_le_genSub hyV
  let y0 : closGen E V := ⟨((y : D) : H), Submodule.le_topologicalClosure _ ⟨y, hyG, rfl⟩⟩
  have hy0 : y0 ≠ 0 := by
    intro h
    apply hy
    have h2 : ((y : D) : H) = 0 := congrArg Subtype.val h
    exact Subtype.ext h2
  have hcoe : (fun g => inner ℂ y0 (ρ g y0)) = fun g => inner ℂ (y : H) (σ (umat g) (y : H)) := by
    funext g
    change inner ℂ (y : H) (↑(tfClRep σ (closGen E V) (umat g) y0) : H) = _
    rw [tfClRep_coe σ _ (hst (umat g) (umat_mem_UJset ε g))]
  have h0 : MemLp (fun g => inner ℂ y0 (ρ g y0)) 2 (Formalism.REAL.muG ε) := by
    rw [hcoe]
    exact memLp_of_weighted_diagonal hσ (y : H) (hW y hyG y hyG)
  have : (Formalism.REAL.muG ε).IsMulRightInvariant :=
    ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  exact memLp_coefficients (ρ := ρ) (MeasureTheory.measurePreserving_mul_right (Formalism.REAL.muG ε))
    (Measure.measurePreserving_inv (Formalism.REAL.muG ε)) hone hmul hiso hirr y0 hy0 h0

end ReciprocityTheory.ChartRestriction.DS.G2
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaE =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaI =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaI", "h": "module\n\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Algebra.Ring.IsFormallyReal\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaD\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaE\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaF\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaH\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.RorthFunctionalEqZero\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaC\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem tf_ph_inj (dual : Bool) {lam : Fin n → ℝ} [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ (closGen E V)) d)
    {y : D} (hyG : y ∈ genSub E V) (hy0 : (y : H) ≠ 0) {g0 : Fin n → D} (hg0m : g0 ∈ tensSub (genSub E V))
    (h0 : tfPh dual ε σ (y : H) (fun i => ((g0 i : D) : H)) = 0) : g0 = 0 := by
  have hyC : (y : H) ∈ closGen E V := Submodule.le_topologicalClosure _ ⟨y, hyG, rfl⟩
  have hcoeC : ∀ f : Fin n → D, f ∈ tensSub (genSub E V) → ∀ c : Fin n, ((f c : D) : H) ∈ closGen E V :=
    fun f hf c => Submodule.le_topologicalClosure _ ⟨f c, (tset_mem.1 hf) c, rfl⟩
  set f2 : Fin n → D := fun c => tfSgn ε c • g0 c with hf2
  have hf2m : f2 ∈ tensSub (genSub E V) := by
    rw [tset_mem]; intro c; exact Submodule.smul_mem _ _ ((tset_mem.1 hg0m) c)
  have hT2b := tensor_functor_separation dual hσ hD hgap hV hc hVK hd hyC (hcoeC _ hf2m) (hcoeC _ hg0m)
    (tf_ph_memLp dual hσ hD hsm hgap hV hc hVK hW hyG hf2m) (tf_ph_memLp dual hσ hD hsm hgap hV hc hVK hW hyG hg0m)
  rw [h0, map_zero, inner_zero_right] at hT2b
  have hform : tfFormBH ε (fun i => ((f2 i : D) : H)) (fun i => ((g0 i : D) : H)) =
      ((∑ c, ‖((g0 c : D) : H)‖ ^ 2 : ℝ) : ℂ) := by
    unfold tfFormBH
    push_cast
    refine sum_congr rfl fun c _ => ?_
    rw [hf2]
    simp only [Submodule.coe_smul, inner_smul_left, ← mul_assoc, inner_self_eq_norm_sq_to_K]
    rw [show (starRingEnd ℂ) (tfSgn ε c) = tfSgn ε c from tf_star_sgn ε c, tfSgn_mul_self, one_mul]
    rfl
  have hd0 : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd.1.ne'
  have hN0 : inner ℂ (y : H) (y : H) ≠ 0 := inner_self_ne_zero.2 hy0
  rw [hform] at hT2b
  have hs0 : (∑ c, ‖((g0 c : D) : H)‖ ^ 2 : ℝ) = 0 := by
    have h1 : ((∑ c, ‖((g0 c : D) : H)‖ ^ 2 : ℝ) : ℂ) = 0 := by
      have h2 := hT2b.symm
      rw [mul_div_assoc] at h2
      exact (mul_eq_zero.1 h2).resolve_right (div_ne_zero hN0 hd0)
    exact_mod_cast h1
  funext c
  have h1 := (sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖((g0 i : D) : H)‖)).1 hs0 c (mem_univ _)
  have h2 : ((g0 c : D) : H) = 0 := norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1)
  exact Subtype.ext h2

theorem tf_trace_core (dual : Bool) {lam : Fin n → ℝ} [CompleteSpace H] {ε : Fin n → Bool}
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
    {c0 : ℂ} (hc0 : ∀ x ∈ genSub E V, ptr P x = c0 • x) {y : D} (hyV : y ∈ V) (hy0 : (y : H) ≠ 0) :
    ∃ r : ℝ, 0 ≤ r ∧ c0 = r ∧ (c0 = 0 → ∀ b, P (Pi.single b y) = 0) := by
  obtain ⟨d, hd⟩ := tfClRep_fdeg hgap hσ hD hV hc hVK (tf_sqInt_of_hW hσ hD hgap hV hc hVK hW)
  obtain ⟨HP, w, -, hHPeq, -, hrep, hc0eq⟩ :=
    tf_trace_data dual hσ hD hsm hgap hV hc hVK hW hP hPP hPB hEP hc0 hyV hy0 hd
  have hdpos : 0 < d := hd.1
  refine ⟨(∑ c, ‖w c‖ ^ 2) / d, div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) hdpos.le, hc0eq, fun h0 b => ?_⟩
  have hT0 : ∑ c, ‖w c‖ ^ 2 = 0 := by
    rw [h0] at hc0eq
    have h1 : (∑ c, ‖w c‖ ^ 2) / d = 0 := by exact_mod_cast hc0eq.symm
    exact (div_eq_zero_iff.1 h1).resolve_right hdpos.ne'
  have hw0 : ∀ c, w c = 0 := by
    intro c
    have h1 := (sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖w i‖)).1 hT0 c (mem_univ _)
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1)
  have hHP0 : ∀ v ∈ HP, v = 0 := by
    intro v hv
    refine vectorL2_ext fun c => ?_
    have h1 := hrep v hv c
    simp only [hw0, inner_zero_left] at h1
    exact Lp.ext (h1.trans (Lp.coeFn_zero ℂ 2 (Formalism.REAL.muG ε)).symm)
  have hyG : y ∈ genSub E V := rorth_le_genSub hyV
  have hsing : (Pi.single b y : Fin n → D) ∈ tensSub (genSub E V) := by
    simpa using tf_single_smul_mem b (1 : ℂ) hyG
  have hmemHP : tfPh dual ε σ (y : H) (fun i => ((P (Pi.single b y) i : D) : H)) ∈ HP := by
    rw [hHPeq]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨_, hsing, rfl⟩)
  exact tf_ph_inj dual hσ hD hsm hgap hV hc hVK hW hd hyG hy0 (hP.1 _ hsing) (hHP0 _ hmemHP)

end ReciprocityTheory.ChartRestriction.DS.G2
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaI =====
