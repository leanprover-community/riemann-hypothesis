module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothDefs
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Decomp
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormula
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.MomentMatch
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.PoleMatchA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.PtrScalar
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.PtrScalar, ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.PoleMatchA, ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.PoleMatch

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.PtrScalar =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.PtrScalar", "h": "module\n\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.PtrScalar\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
  {V : Submodule ℂ D} {A : Module.End ℂ (Fin n → D)}

end

theorem ptr_scalar (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {A : Module.End ℂ (Fin n → D)} (hA : IsGKEndo dual ε σ E (genSub E V) A) :
    ∃ c : ℂ, ∀ x ∈ genSub E V, ptr A x = c • x :=
  data_end_scalar hgap hσ hD hV hc hVK (ptr A) (ptr_mem hA) (fun a b => ptr_comm hD.glRep hA a b)
    (ptr_kcomm hσ hD hA)

end ReciprocityTheory.ChartRestriction.DS.G2
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.PtrScalar =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.PoleMatchA =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.PoleMatchA", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.PoleMatchA\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap\npublic import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothDefs\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Decomp\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.PtrScalar\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormula\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.MomentMatch\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

open MeasureTheory

section Generic

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem pm_pow_eig (A : Module.End ℂ W) {z : ℂ} {f : W} (h : A f = z • f) (k : ℕ) :
    (A ^ k) f = z ^ k • f := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, h, smul_smul, pow_succ]

theorem pm_proj_decomp (A Q : Module.End ℂ W) (T : Submodule ℂ W) (B : Finset ℝ) (z : ℂ)
    (hQ1 : ∀ f ∈ T, A f = z • f → Q f = f) (hQ0 : ∀ f ∈ T, ∀ z' : ℂ, z' ≠ z → A f = z' • f → Q f = 0)
    (fb : ℝ → W) (hfb : ∀ b, fb b ∈ T ∧ A (fb b) = ((b : ℝ) : ℂ) • fb b) :
    Q (∑ b ∈ B, fb b) = ∑ b ∈ B, if ((b : ℝ) : ℂ) = z then fb b else 0 := by
  rw [map_sum Q fb B]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · exact hQ1 _ (hfb b).1 (by rw [← h]; exact (hfb b).2)
  · exact hQ0 _ (hfb b).1 _ h (hfb b).2

end Generic

theorem pm_single_mem {M : Type*} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) {x : M} (hx : x ∈ S)
    (c : Fin n) : Pi.single c x ∈ tensSub (n := n) S := by
  refine (Submodule.mem_pi).2 fun i _ => ?_
  by_cases h : i = c <;> simp [h, hx]

theorem pm_ptr {M : Type*} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M)
    (Q : Module.End ℂ (Fin n → M)) (R : ℝ → Module.End ℂ (Fin n → M)) (B : Finset ℝ) (g : ℝ → ℂ)
    (hQ : ∀ f ∈ tensSub S, Q f = ∑ b ∈ B, g b • R b f) {x : M} (hx : x ∈ S) :
    ptr Q x = ∑ b ∈ B, g b • ptr (R b) x := by
  simp only [ptr_apply, hQ _ (pm_single_mem S hx _), Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_comm

theorem pm_core (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (hG : HasGelfandChar E lam (genSub E V)) :
    ∃ B : Finset ℝ, ∃ c : ℝ → ℂ, ∃ P : ℝ → Module.End ℂ (Fin n → D),
      (∀ z : ℂ, ∀ f ∈ tensSub (genSub E V), f ≠ 0 → eeF dual E f = z • f → ∃ b ∈ B, z = ((b : ℝ) : ℂ)) ∧
      (∀ b, ∀ f ∈ tensSub (genSub E V), P b f ∈ tensSub (genSub E V)) ∧
      (∀ b, ∀ f ∈ tensSub (genSub E V), eeF dual E (P b f) = ((b : ℝ) : ℂ) • P b f) ∧
      (∀ b, ∀ f ∈ tensSub (genSub E V), eeF dual E f = ((b : ℝ) : ℂ) • f → P b f = f) ∧
      (∀ b, ∀ x ∈ genSub E V, ptr (P b) x = c b • x) ∧
      (∀ b, c b = 0 → ∀ f ∈ tensSub (genSub E V), P b f = 0) ∧
      (∀ (Q : Module.End ℂ (Fin n → D)) (z : ℂ), (∀ f ∈ tensSub (genSub E V), eeF dual E f = z • f → Q f = f) →
        (∀ f ∈ tensSub (genSub E V), ∀ z' : ℂ, z' ≠ z → eeF dual E f = z' • f → Q f = 0) →
        ∀ x ∈ genSub E V, ptr Q x = (∑ b ∈ B, if ((b : ℝ) : ℂ) = z then c b else 0) • x) ∧
      (∀ p : ℂ, (∑ b ∈ B, if ((b : ℝ) : ℂ) = p then c b else 0) =
        ∑ s ∈ univ.filter (fun s => poleF dual lam s = p), ((ratioF dual lam s : ℝ) : ℂ)) ∧
      ∃ x₀ ∈ genSub E V, x₀ ≠ 0 := by
  obtain ⟨B, hdec, hev⟩ := ee_decomp dual hσ hD hgap hV hc hVK hW
  have hPex := fun b : ℝ => eigenProj_exists dual hσ hD hgap hV hc hVK hW ((b : ℝ) : ℂ)
  choose P hPG hPP hPz hP1 hP0 using hPex
  have hsc := fun b => ptr_scalar dual hσ hD hgap hV hc hVK (hPG b)
  choose c hcb using hsc
  have hPB := fun b => eigenProj_formB dual hσ hD hgap hV hc hVK hW _ (hPG b).1 (hPz b) (hP1 b) (hP0 b)
  have htr := fun b => trace_nonneg dual hσ hD hsm hgap hV hc hVK hW (hPG b) (hPP b) (hPB b) (hPz b) (hcb b)
  obtain ⟨hpow, hagr⟩ := pm_agree (eeF dual E) (tensSub (genSub E V)) B hdec P hP1 hP0
  have hQ : ∀ (Q : Module.End ℂ (Fin n → D)) (z : ℂ),
      (∀ f ∈ tensSub (genSub E V), eeF dual E f = z • f → Q f = f) →
      (∀ f ∈ tensSub (genSub E V), ∀ z' : ℂ, z' ≠ z → eeF dual E f = z' • f → Q f = 0) →
      ∀ x ∈ genSub E V, ptr Q x = (∑ b ∈ B, if ((b : ℝ) : ℂ) = z then c b else 0) • x := by
    intro Q z hQ1 hQ0 x hx
    rw [pm_ptr (genSub E V) Q P B (fun b => if ((b : ℝ) : ℂ) = z then 1 else 0)
      (fun f hf => by
        rw [hagr Q z hQ1 hQ0 f hf]
        exact sum_congr rfl fun b _ => by split_ifs <;> simp) hx, Finset.sum_smul]
    refine sum_congr rfl fun b _ => ?_
    rw [hcb b x hx]
    split_ifs <;> simp
  have hVle : V ≤ genSub E V := by
    unfold genSub
    exact le_sInf fun T hT => hT.1
  obtain ⟨x₀, hx₀V, hx₀0, -⟩ := hV.2.2.2
  have hx₀ : x₀ ∈ genSub E V := hVle hx₀V
  have hmom : ∀ k : ℕ, ∑ i : B, c i * ((i : ℝ) : ℂ) ^ k =
      ∑ s, resid (poleF dual lam) s * poleF dual lam s ^ k := by
    intro k
    rw [Finset.sum_coe_sort B (fun b => c b * ((b : ℝ) : ℂ) ^ k), ← resSeries_coeff_succ (pm_pole_inj dual hgap.1) k]
    apply smul_left_injective ℂ hx₀0
    beta_reduce
    rw [← pm_char dual hG k x₀ hx₀, pm_ptr (genSub E V) _ P B (fun b => ((b : ℝ) : ℂ) ^ k)
      (fun f hf => hpow f hf k) hx₀, Finset.sum_smul]
    refine sum_congr rfl fun b _ => ?_
    rw [hcb b x₀ hx₀, smul_smul, mul_comm (c b)]
  refine ⟨B, c, P, hev, fun b => (hPG b).1, hPz, hP1, hcb, fun b h0 => (htr b).2.2 h0, hQ, fun p => ?_,
    x₀, hx₀, hx₀0⟩
  have hf := moment_fibre (fun i : B => ((i : ℝ) : ℂ)) (fun i => c i) (poleF dual lam) (resid (poleF dual lam)) hmom p
  rw [Finset.sum_filter, Finset.sum_coe_sort B (fun b => if ((b : ℝ) : ℂ) = p then c b else 0)] at hf
  rw [hf]
  exact sum_congr rfl fun s _ => pm_resid dual lam s

end ReciprocityTheory.ChartRestriction.DS.G2
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.PoleMatchA =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.PoleMatch =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.PoleMatch", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormula\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.PoleMatchA\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

open MeasureTheory

theorem pole_match (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (hG : HasGelfandChar E lam (genSub E V)) :
    (∀ z : ℂ, ∀ f ∈ tensSub (genSub E V), f ≠ 0 → eeF dual E f = z • f → ∃ s, z = poleF dual lam s) ∧
      ∀ (s : Fin n) (P : Module.End ℂ (Fin n → D)), IsGKEndo dual ε σ E (genSub E V) P →
        (∀ f ∈ tensSub (genSub E V), P (P f) = P f) →
        (∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V), formB ε (P f) g = formB ε f (P g)) →
        (∀ f ∈ tensSub (genSub E V), eeF dual E (P f) = poleF dual lam s • P f) →
        (∀ f ∈ tensSub (genSub E V), eeF dual E f = poleF dual lam s • f → P f = f) →
        (∀ f ∈ tensSub (genSub E V), ∀ z' : ℂ, z' ≠ poleF dual lam s → eeF dual E f = z' • f → P f = 0) →
        ∀ x ∈ genSub E V, ptr P x = ((ratioF dual lam s : ℝ) : ℂ) • x := by
  obtain ⟨B, c, P, hev, -, -, hP1, -, hc0, hQ, hfib, -⟩ := pm_core dual hσ hD hsm hgap hV hc hVK hW hG
  refine ⟨fun z f hf hf0 hz => ?_, fun s Q _ _ _ _ hQ1 hQ0 x hx => ?_⟩
  · obtain ⟨b, hb, rfl⟩ := hev z f hf hf0 hz
    have hcne : c b ≠ 0 := fun h0 => hf0 (by rw [← hP1 b f hf hz]; exact hc0 b h0 f hf)
    have h1 := hfib ((b : ℝ) : ℂ)
    rw [pm_sum_single hb] at h1
    by_contra hne
    simp only [not_exists] at hne
    rw [Finset.filter_eq_empty_iff.2 (fun s _ h => hne s h.symm), Finset.sum_empty] at h1
    exact hcne h1
  · rw [hQ Q _ hQ1 hQ0 x hx, hfib, pm_filter_pole dual hgap.1 s, Finset.sum_singleton]

theorem pole_zero (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (hG : HasGelfandChar E lam (genSub E V)) (s : Fin n) :
    ratioF dual lam s = 0 ↔ ∀ f ∈ tensSub (genSub E V), eeF dual E f = poleF dual lam s • f → f = 0 := by
  obtain ⟨B, c, P, hev, hPM, hPz, hP1, hcb, hc0, -, hfib, x₀, hx₀, hx₀0⟩ :=
    pm_core dual hσ hD hsm hgap hV hc hVK hW hG
  have h1 := hfib (poleF dual lam s)
  rw [pm_filter_pole dual hgap.1 s, Finset.sum_singleton] at h1
  constructor
  · intro h0 f hf hz
    by_contra hf0
    obtain ⟨b, hb, hzb⟩ := hev _ f hf hf0 hz
    have hcne : c b ≠ 0 := fun h => hf0 (by rw [← hP1 b f hf (hzb ▸ hz)]; exact hc0 b h f hf)
    rw [hzb, pm_sum_single hb, h0, Complex.ofReal_zero] at h1
    exact hcne h1
  · intro hno
    have hsum : (∑ b ∈ B, if ((b : ℝ) : ℂ) = poleF dual lam s then c b else 0) = 0 := by
      refine sum_eq_zero fun b _ => ?_
      split_ifs with h
      · have hz : ∀ f ∈ tensSub (genSub E V), P b f = 0 := fun f hf =>
          hno _ (hPM b f hf) (by rw [hPz b f hf, h])
        have h2 : c b • x₀ = 0 := by
          rw [← hcb b x₀ hx₀, ptr_apply]
          exact sum_eq_zero fun i _ => by rw [hz _ (pm_single_mem _ hx₀ _)]; rfl
        exact (smul_eq_zero.1 h2).resolve_right hx₀0
      · rfl
    rw [hsum] at h1
    exact_mod_cast h1.symm

end ReciprocityTheory.ChartRestriction.DS.G2
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.PoleMatch =====
