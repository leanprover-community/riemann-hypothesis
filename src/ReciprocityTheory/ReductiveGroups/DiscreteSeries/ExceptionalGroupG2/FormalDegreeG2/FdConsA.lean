module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
public import Mathlib.Analysis.InnerProductSpace.Positive
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Transported
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExistsMu
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.GelfandG
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Integr
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiMExpFormula
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.EquivSigLamOfIsDS
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.IsDSSigLam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.CcARatioZero
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Weighted
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PsiPos
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Residue
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.StdGapOfGapLap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.PsiFor
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdCons
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
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LholClmEventually
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ToMKMulInv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdegTransfer
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarMirror
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.SandwichA

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.SandwichA, ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Sandwich, ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdConsA

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.SandwichA =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.SandwichA", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap\npublic import Mathlib.Analysis.InnerProductSpace.Positive\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Transported\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting\npublic import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExistsMu\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.GelfandG\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Integr\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LholClmEventually\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiMExpFormula\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ToMKMulInv\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.EquivSigLamOfIsDS\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.IsDSSigLam\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.CcARatioZero\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Weighted\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdegTransfer\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PsiPos\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.SandwichA\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Finset MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

theorem swA_thr {ε : Fin n → Bool} {h : ℝ} (hth : thrS ε < h) :
    2 * (n : ℝ) < h ∧
      16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)) < h :=
  ⟨lt_of_le_of_lt (le_max_left _ _) hth, lt_of_le_of_lt (le_max_right _ _) hth⟩

theorem swA_model {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : S7.IsHCParam lam) (hq : 1 ≤ S7.q0 ε) {h : ℝ}
    (hh : GapAtLeast ε lam h) (hth : thrS ε < h) (T : S7.KType ε (lowK ε lam)) :
    ∃ Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V), StdGap ε lam ∧ IsPsiFor ε lam T Ψ ∧
      (∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive) ∧
      (∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w),
        MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
          inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε)))
          2 (Formalism.REAL.muG ε)) ∧
      HasGelfandChar (smE ε (rreg ε)) lam (genSub (smE ε (rreg ε)) (datumV ε Ψ T.w)) := by
  obtain ⟨m, hm⟩ := S7.exists_mu hlam
  obtain ⟨h1, h2⟩ := swA_thr hth
  have hq1 : (0 : ℝ) ≤ (S7.q0 ε : ℝ) := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hsq : 0 ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
  have hnq : 0 ≤ (n : ℝ) * (S7.q0 ε : ℝ) := mul_nonneg hn0 hq1
  have h8 : 8 * (n : ℝ) * S7.q0 ε < h := by nlinarith
  have hs2 : 8 * (n : ℝ) * S7.q0 ε + 4 * 2 * Real.sqrt (2 * S7.q0 ε) < h := by nlinarith
  have hgap : StdGap ε lam := ⟨hlam.1, h, hh, h1⟩
  have hP : IsPsiFor ε lam T (S7.PsiM T m) :=
    ⟨fun k₁ k₂ g hg => S7.psiM_equiv T m k₁ k₂ hg, S7.psiM_one T m, S7.psiM_smooth T m hm,
      fun g hg => S7.psiM_casimir T m hm hg, fun ν hν => by
        have := hν
        exact (S7.psiM_integrable T m hm hlam hh hq ν).2.1 h8⟩
  have hv₀ : T.w ≠ 0 := fun h0 => by simpa [h0] using T.w_norm
  refine ⟨S7.PsiM T m, hgap, hP, psi_exp_isPositive T (S7.PsiM T m) m hm (fun X hX => S7.psiM_exp_formula T m hX),
    weighted_datum hgap hP hv₀ (fun ν hν => ?_), hasGelfandChar_sigLam hgap hP hv₀ (fun k g hg => S7.psiM_gelfand T m hm k hg)⟩
  have := hν
  exact (S7.psiM_integrable T m hm hlam hh hq ν).2.2 2 (by norm_num) hs2

theorem swB_isFdeg_pull {ε : Fin n → Bool} {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] {τA : Matrix (Fin n) (Fin n) ℂ → (A →L[ℂ] A)}
    {τB : Matrix (Fin n) (Fin n) ℂ → (B →L[ℂ] B)} (U : A ≃ₗᵢ[ℂ] B)
    (hU : ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ x : A, U (τA g x) = τB g (U x)) {ν : Measure (Formalism.REAL.UJ ε)} {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg ν τB d) : Formalism.MainNotions.S.IsFdeg ν τA d := by
  obtain ⟨hd0, h⟩ := hd
  have hc : ∀ v w : A, Formalism.MainNotions.S.coefOn (ε := ε) τA v w = Formalism.MainNotions.S.coefOn (ε := ε) τB (U v) (U w) := by
    intro v w
    funext g
    simp only [Formalism.MainNotions.S.coefOn]
    rw [← hU _ g.2, LinearIsometryEquiv.inner_map_map]
  refine ⟨hd0, fun v w v' w' => ?_⟩
  obtain ⟨hi, he⟩ := h (U v) (U w) (U v') (U w')
  rw [hc v w, hc v' w']
  refine ⟨hi, ?_⟩
  rw [he, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]

theorem swB_isFdeg_push {ε : Fin n → Bool} {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] {τA : Matrix (Fin n) (Fin n) ℂ → (A →L[ℂ] A)}
    {τB : Matrix (Fin n) (Fin n) ℂ → (B →L[ℂ] B)} (U : A ≃ₗᵢ[ℂ] B)
    (hU : ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ x : A, U (τA g x) = τB g (U x)) {ν : Measure (Formalism.REAL.UJ ε)} {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg ν τA d) : Formalism.MainNotions.S.IsFdeg ν τB d := by
  refine swB_isFdeg_pull U.symm (fun g hg y => ?_) hd
  apply U.injective
  rw [LinearIsometryEquiv.apply_symm_apply, hU g hg, LinearIsometryEquiv.apply_symm_apply]

theorem swC_gap_shift {ε : Fin n → Bool} {μ : Fin n → ℝ} {h : ℝ} (hμ : GapAtLeast ε μ h) (dual : Bool)
    (s : Fin n) : GapAtLeast ε (shiftF dual μ s) (h - 1) := by
  have key : ∀ c : Fin n → ℝ, (∀ a b : Fin n, a ≠ b → |c a - c b| ≤ 1) → GapAtLeast ε (μ + c) (h - 1) := by
    intro c hc a b hab
    have hne : a ≠ b := fun e => hab (e ▸ rfl)
    have h1 := hμ a b hab
    have h2 := hc a b hne
    have h3 : |μ a - μ b| ≤ |(μ + c) a - (μ + c) b| + |c a - c b| := by
      have : μ a - μ b = ((μ + c) a - (μ + c) b) - (c a - c b) := by simp only [Pi.add_apply]; ring
      rw [this]
      exact abs_sub _ _
    linarith
  have hsingle : ∀ t : ℝ, |t| ≤ 1 → ∀ a b : Fin n, a ≠ b → |Pi.single (M := fun _ => ℝ) s t a - Pi.single (M := fun _ => ℝ) s t b| ≤ 1 := by
    intro t ht a b hab
    by_cases ha : a = s
    · subst ha
      rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hab), sub_zero]
      exact ht
    · by_cases hb : b = s
      · subst hb
        rw [Pi.single_eq_same, Pi.single_eq_of_ne ha, zero_sub, abs_neg]
        exact ht
      · rw [Pi.single_eq_of_ne ha, Pi.single_eq_of_ne hb]
        simp
  cases dual
  · exact key _ (hsingle 1 (by simp))
  · have : shiftF true μ s = μ + Pi.single s (-1) := by
      simp only [shiftF, cond_true]
      rw [sub_eq_add_neg, Pi.single_neg]
    rw [this]
    exact key _ (hsingle (-1) (by simp))

theorem swC_hc_shift {μ : Fin n → ℝ} (hμ : S7.IsHCParam μ) (dual : Bool) (s : Fin n)
    (hs : StrictAnti (shiftF dual μ s)) : S7.IsHCParam (shiftF dual μ s) := by
  refine ⟨hs, fun a => ?_⟩
  obtain ⟨m, hm⟩ := hμ.2 a
  by_cases ha : a = s
  · subst ha
    cases dual
    · exact ⟨m + 1, by simp only [shiftF, cond_false, Pi.add_apply, Pi.single_eq_same]; push_cast; linarith⟩
    · exact ⟨m - 1, by simp only [shiftF, cond_true, Pi.sub_apply, Pi.single_eq_same]; push_cast; linarith⟩
  · cases dual
    · exact ⟨m, by simp only [shiftF, cond_false, Pi.add_apply, Pi.single_eq_of_ne ha, add_zero]; exact hm⟩
    · exact ⟨m, by simp only [shiftF, cond_true, Pi.sub_apply, Pi.single_eq_of_ne ha, sub_zero]; exact hm⟩

theorem swC_main (dual : Bool) {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) {μ : Fin n → ℝ}
    (hμ : S7.IsHCParam μ) {h : ℝ} (hgap : GapAtLeast ε μ h) (hh : thrS ε + 1 < h) (s : Fin n)
    (hs : StrictAnti (shiftF dual μ s))
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsDS ε μ σ)
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}
    (hσ' : Formalism.MainNotions.S.IsDS ε (shiftF dual μ s) σ')
    (ν : Measure (Formalism.REAL.UJ ε)) (hν : ν.IsHaarMeasure) {d : ℝ} (hd : Formalism.MainNotions.S.IsFdeg ν σ d) :
    Formalism.MainNotions.S.IsFdeg ν σ' (d * ratioF dual μ s) := by
  have := hσ.1
  have := hσ'.1
  have hq0 : 1 ≤ S7.q0 ε := le_min hp hq
  have hth : thrS ε < h := by linarith
  have hth' : thrS ε < h - 1 := by linarith
  have hlam' := swC_hc_shift hμ dual s hs
  have hgap' := swC_gap_shift hgap dual s
  obtain ⟨T⟩ := HW.kType_exists ε μ hμ
  obtain ⟨T'⟩ := HW.kType_exists ε (shiftF dual μ s) hlam'
  obtain ⟨Ψ, hS, hP, hpos, hW, hG⟩ := swA_model hμ hq0 hgap hth T
  obtain ⟨Ψ', hS', hP', hpos', hW', hG'⟩ := swA_model hlam' hq0 hgap' hth' T'
  have hv₀ : T.w ≠ 0 := fun h0 => by simpa [h0] using T.w_norm
  have hv₀' : T'.w ≠ 0 := fun h0 => by simpa [h0] using T'.w_norm
  have hDS := isDS_sigLam hS hP hv₀
  have hDS' := isDS_sigLam hS' hP' hv₀'
  have := hDS.2.1
  have := hDS'.2.1
  obtain ⟨w, hw⟩ := exists_ne (0 : Hlam ε Ψ T.w)
  obtain ⟨w', hw'⟩ := exists_ne (0 : Hlam ε Ψ' T'.w)
  have hcc := (cc_gk dual hS hP hv₀ hS' hP' hv₀' hgap hth hgap' hth' hpos hpos' hW hW' hG hG' s rfl hw hw').2
  obtain ⟨U, hU⟩ := equiv_sigLam_of_isDS hσ hS hP hv₀
  obtain ⟨U', hU'⟩ := equiv_sigLam_of_isDS hσ' hS' hP' hv₀'
  have hdL : Formalism.MainNotions.S.IsFdeg ν (sigLam ε Ψ T.w) d := swB_isFdeg_pull U hU hd
  obtain ⟨d1, hd1⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS μ (sigLam ε Ψ T.w) hDS
  obtain ⟨d2, hd2⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS (shiftF dual μ s) (sigLam ε Ψ' T'.w) hDS'
  rw [fdegOf_of_isFdeg' hd1 hw, fdegOf_of_isFdeg' hd2 hw'] at hcc
  have := hν
  obtain ⟨c, hc, hνeq⟩ := swB_haar_eq ν
  have hd1' : Formalism.MainNotions.S.IsFdeg ν (sigLam ε Ψ T.w) (d1 / c) := hνeq ▸ isFdeg_smul hc hd1
  have hd2' : Formalism.MainNotions.S.IsFdeg ν (sigLam ε Ψ' T'.w) (d2 / c) := hνeq ▸ isFdeg_smul hc hd2
  have hdd : d = d1 / c := swB_isFdeg_unique hw hdL hd1'
  have hd10 : d1 ≠ 0 := hd1.1.ne'
  have hval : d * ratioF dual μ s = d2 / c := by
    rw [hdd, ← hcc]
    field_simp
  rw [hval]
  exact swB_isFdeg_push U' hU' hd2'

end ReciprocityTheory.ChartRestriction.DS.G2
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.SandwichA =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Sandwich =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Sandwich", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Residue\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Transported\npublic import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.SandwichA\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

open MeasureTheory

theorem fdeg_ratio_V {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) {μ : Fin n → ℝ}
    (hμ : S7.IsHCParam μ) {h : ℝ} (hgap : GapAtLeast ε μ h) (hh : thrS ε + 1 < h) (s : Fin n)
    (hs : StrictAnti (μ + Pi.single s 1))
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsDS ε μ σ)
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}
    (hσ' : Formalism.MainNotions.S.IsDS ε (μ + Pi.single s 1) σ')
    (ν : Measure (Formalism.REAL.UJ ε)) (hν : ν.IsHaarMeasure) {d : ℝ} (hd : Formalism.MainNotions.S.IsFdeg ν σ d) :
    Formalism.MainNotions.S.IsFdeg ν σ' (d * ratioV μ s) := by
  exact swC_main false hp hq hμ hgap hh s hs hσ hσ' ν hν hd

end ReciprocityTheory.ChartRestriction.DS.G2
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Sandwich =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdConsA =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdConsA", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Transported\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Residue\npublic import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.EquivSigLamOfIsDS\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.IsDSSigLam\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Sandwich\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdegTransfer\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarMirror\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.StdGapOfGapLap\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.PsiFor\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdCons\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.G2

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdc_big {ε : Fin n → Bool} {h : ℝ} (hh : thrS ε + 1 < h) :
    2 * (n : ℝ) < h := by
  unfold thrS at hh
  have h1 := le_max_left (2 * (n : ℝ))
    (16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)))
  linarith

theorem fdc_eight {ε : Fin n → Bool} {h : ℝ} (hh : thrS ε + 1 < h) :
    8 * (n : ℝ) * (S7.q0 ε : ℝ) < h := by
  unfold thrS at hh
  have h1 := le_max_right (2 * (n : ℝ))
    (16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)))
  have h2 : 0 ≤ (n : ℝ) * (S7.q0 ε : ℝ) := by positivity
  have h3 : 0 ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
  nlinarith

theorem fdc_stdGap {ε : Fin n → Bool} {μ : Fin n → ℝ} {h : ℝ} (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h)
    (hh : thrS ε + 1 < h) : StdGap ε μ :=
  ⟨hμ.1, h, hg, fdc_big hh⟩

theorem fdc_model {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) {μ : Fin n → ℝ} {h : ℝ}
    (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h) (hh : thrS ε + 1 < h) (T : KType ε (lowK ε μ)) :
    ∃ m : Fin n → ℤ, IsMu μ m ∧ IsPsiFor ε μ T (PsiM T m) := by
  obtain ⟨m, hm⟩ := Lap.LemK.exists_isMu hμ
  exact ⟨m, hm, (Lap.Base.psiFor n ε μ h T m hμ hm hg (one_le_q0_of_p_q_pos hp hq) (fdc_eight hh)).1⟩

theorem fdcGood_unique {ε : Fin n → Bool} {μ : Fin n → ℝ} {h : ℝ} (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h)
    (hh : thrS ε + 1 < h) {d d' : ℝ} (h1 : FdcGood ε μ d) (h2 : FdcGood ε μ d') : d = d' := by
  obtain ⟨H, _, _, σ, hσ, hd⟩ := h1
  obtain ⟨H', _, _, σ', hσ', hd'⟩ := h2
  have := hσ.1
  have := hσ'.1
  have := hσ.2.1
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  obtain ⟨U, hU⟩ := (isDS_props_of_gap n ε μ hμ h hg (fdc_big hh) H σ hσ).2.2.2.2 H' σ' hσ'
  have hUv : U v ≠ 0 := by simpa using hv
  rw [← fdegOf_of_isFdeg' hd hv, ← fdegOf_of_isFdeg' hd' hUv, fdc_fdegOf_eq U hU]

theorem fdcD_eq {ε : Fin n → Bool} {μ : Fin n → ℝ} {h : ℝ} (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h)
    (hh : thrS ε + 1 < h) {d : ℝ} (hd : FdcGood ε μ d) : fdcD ε μ = d := by
  have hex : ∃ d, FdcGood ε μ d := ⟨d, hd⟩
  rw [fdcD, dite_eq_left hex]
  exact fdcGood_unique hμ hg hh hex.choose_spec hd

theorem fdcGood_of_isDS {ε : Fin n → Bool} {μ : Fin n → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsDS ε μ σ) :
    ∃ d, Formalism.MainNotions.S.IsFdeg (muCD ε) σ d := by
  have := hσ.1
  obtain ⟨d, hd⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS μ σ hσ
  exact isFdeg_muCD hd

theorem fdc_ds_exists {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) {μ : Fin n → ℝ} {h : ℝ}
    (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h) (hh : thrS ε + 1 < h) : ∃ d, FdcGood ε μ d := by
  obtain ⟨T⟩ := HW.kType_exists ε μ hμ
  obtain ⟨m, -, hP⟩ := fdc_model hp hq hμ hg hh T
  have hDS := isDS_sigLam (fdc_stdGap hμ hg hh) hP (_root_.ReciprocityTheory.ChartRestriction.DS.HW.KType.w_ne_zero T)
  obtain ⟨d, hd⟩ := fdcGood_of_isDS hDS
  exact ⟨d, _, inferInstance, inferInstance, _, hDS, hd⟩

theorem fdc_step {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) {h : ℝ} (hh : thrS ε + 1 < h) :
    ∀ (μ : Fin n → ℝ) (s : Fin n), IsHCParam μ → GapAtLeast ε μ h →
      GapAtLeast ε (μ + Pi.single s 1) h → StrictAnti (μ + Pi.single s 1) →
        fdcD ε (μ + Pi.single s 1) = fdcD ε μ * ratioV μ s := by
  intro μ s hμ hg hg' hs
  have hμ' : IsHCParam (μ + Pi.single s 1) := fdc_hc_add hμ hs
  obtain ⟨d, H, _, _, σ, hσ, hd⟩ := fdc_ds_exists hp hq hμ hg hh
  obtain ⟨d', H', _, _, σ', hσ', -⟩ := fdc_ds_exists hp hq hμ' hg' hh
  have hr := fdeg_ratio_V hp hq hμ hg hh s hs hσ hσ' (muCD ε) (muCD_isHaar ε) hd
  rw [fdcD_eq hμ hg hh ⟨H, inferInstance, inferInstance, σ, hσ, hd⟩,
    fdcD_eq hμ' hg' hh ⟨H', inferInstance, inferInstance, σ', hσ', hr⟩]

end ReciprocityTheory.ChartRestriction.DS.G2
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdConsA =====
