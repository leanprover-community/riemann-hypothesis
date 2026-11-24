module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.NegBound
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.ReverseCauchySchwarzHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.FinrankUperpOfDet
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.NonposCount
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.NegativeBound
public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.ENatToNat

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.ColsConjTranspose, Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.FrameInductionOf, Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.Counts, Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.QBuild, Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FrameInd

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.ColsConjTranspose =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.ColsConjTranspose", "h": "module\n\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.NegBound\npublic import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic\npublic import Formalism.FormalDegreeBessel.FormalDegreeRatio.ReverseCauchySchwarzHolds\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Coalgebra.IsFrobenius\nimport Mathlib.RingTheory.Etale.Weakly\nimport Mathlib.RingTheory.Finiteness.ModuleFinitePresentation\nimport Mathlib.RingTheory.HopfAlgebra.Basic\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.TotallySplit\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section
namespace PI.FrameInd.UPosW

def cols (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    Matrix (Fin (2 * r + k + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ :=
  Matrix.of fun p j => gramVec k r z z' γ j p

lemma cols_conjTranspose (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    (cols k r z z' γ)ᴴ = Matrix.of fun i j => star (gramVec k r z z' γ i j) := by
  ext i j
  simp only [cols, Matrix.conjTranspose_apply, Matrix.of_apply]

lemma gram_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    (cols k r z z' γ)ᴴ * Hpk k r * cols k r z z' γ = gramM k r z z' γ := by
  ext i j
  rw [cols_conjTranspose]
  simp only [Matrix.mul_apply, Matrix.of_apply, cols, gramM, herm, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

lemma herm_cols (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r)
    (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    herm (Hpk k r) (cols k r z z' γ *ᵥ c) (cols k r z z' γ *ᵥ c) = star c ⬝ᵥ (gramM k r z z' γ *ᵥ c) := by
  rw [← gram_eq]
  simp only [herm, Matrix.star_mulVec]
  rw [← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

lemma herm_perp (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r)
    (v : Fin (2 * r + k + 1) → ℂ) (hv : v ∈ Uperp k r z z' γ) (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    herm (Hpk k r) v (cols k r z z' γ *ᵥ c) = 0 := by
  have h0 : ((cols k r z z' γ)ᴴ * Hpk k r) *ᵥ v = 0 := by
    have h := hv
    simp only [Uperp, LinearMap.mem_ker, Matrix.mulVecLin_apply] at h
    rw [cols_conjTranspose]
    exact h
  simp only [herm, Matrix.star_mulVec]
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h0, dotProduct_zero]

lemma herm_perp' (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r)
    (v : Fin (2 * r + k + 1) → ℂ) (hv : v ∈ Uperp k r z z' γ) (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    herm (Hpk k r) (cols k r z z' γ *ᵥ c) v = 0 := by
  rw [ggHerm_swap _ (Formalism.QuantumDeterminants.GBasic.Hpk_herm k r), herm_perp k r z z' γ v hv c, star_zero]

lemma herm_add_smul {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (w v : Fin n → ℂ) (t : ℂ)
    (h1 : herm H v w = 0) (h2 : herm H w v = 0) :
    herm H (w + t • v) (w + t • v) = herm H w w + (star t * t) * herm H v v := by
  simp only [herm] at h1 h2 ⊢
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, star_add, star_smul, add_dotProduct,
    dotProduct_add, smul_dotProduct, dotProduct_smul, h1, h2, smul_eq_mul]
  ring

lemma blk_re {m : ℕ} (a : Fin m → ℂ) :
    (star (Sum.elim (0 : Fin m → ℂ) a) ⬝ᵥ
      (fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) 0 0 (-1) *ᵥ Sum.elim (0 : Fin m → ℂ) a)).re =
      -∑ b, Complex.normSq (a b) := by
  have hm : fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) 0 0 (-1) *ᵥ Sum.elim (0 : Fin m → ℂ) a =
      Sum.elim (0 : Fin m → ℂ) (-a) := by
    ext i
    cases i <;> simp [Matrix.fromBlocks_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec]
  rw [hm]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.star_apply,
    Pi.zero_apply, Pi.neg_apply, star_zero, zero_mul, Finset.sum_const_zero, zero_add,
    Complex.re_sum, Complex.normSq_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  ring

def emb (m : ℕ) : (Fin m → ℂ) →ₗ[ℂ] (Fin m ⊕ Fin m → ℂ) where
  toFun a := Sum.elim 0 a
  map_add' a b := by funext i; cases i <;> simp
  map_smul' c a := by funext i; cases i <;> simp

theorem uPos_of (hN : NegBound) : UPos := by
  intro k r z z' γ hs hp hdet hQ v hv hv0
  obtain ⟨Q, -, hQG⟩ := hQ
  by_contra hneg
  have hvv : (herm (Hpk k r) v v).re ≤ 0 := not_lt.mp hneg
  let L : (Fin (r + 1) → ℂ) →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ) :=
    (Matrix.mulVecLin (cols k r z z' γ * Q)).comp (emb (r + 1))
  have hLa : ∀ a, L a = cols k r z z' γ *ᵥ (Q *ᵥ Sum.elim 0 a) := by
    intro a
    show (cols k r z z' γ * Q) *ᵥ Sum.elim 0 a = _
    rw [Matrix.mulVec_mulVec]
  have hLre : ∀ a, (herm (Hpk k r) (L a) (L a)).re = -∑ b, Complex.normSq (a b) := by
    intro a
    rw [hLa, herm_cols, ← blk_re a, ← hQG, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hperp : ∀ a, herm (Hpk k r) v (L a) = 0 ∧ herm (Hpk k r) (L a) v = 0 := fun a => by
    rw [hLa]
    exact ⟨herm_perp k r z z' γ v hv _, herm_perp' k r z z' γ v hv _⟩
  let M : ((Fin (r + 1) → ℂ) × ℂ) →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ) :=
    L.coprod (LinearMap.toSpanSingleton ℂ _ v)
  have hM : ∀ p, M p = L p.1 + p.2 • v := fun p => by
    simp [M, LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply]
  have hMre : ∀ p, (herm (Hpk k r) (M p) (M p)).re =
      -∑ b, Complex.normSq (p.1 b) + Complex.normSq p.2 * (herm (Hpk k r) v v).re := by
    intro p
    have ht : star p.2 * p.2 = (Complex.normSq p.2 : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [hM, herm_add_smul _ _ _ _ (hperp p.1).1 (hperp p.1).2, Complex.add_re, hLre, ht,
      Complex.re_ofReal_mul]
  have hsum : ∀ a : Fin (r + 1) → ℂ, 0 ≤ ∑ b, Complex.normSq (a b) :=
    fun a => Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _
  have hnp : ∀ x ∈ LinearMap.range M, (herm (Hpk k r) x x).re ≤ 0 := by
    rintro x ⟨p, rfl⟩
    rw [hMre]
    have h1 := hsum p.1
    have h2 : Complex.normSq p.2 * (herm (Hpk k r) v v).re ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) hvv
    linarith
  have hinj : Function.Injective M := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp0
    have hre := hMre p
    rw [hp0] at hre
    have h0 : (herm (Hpk k r) (0 : Fin (2 * r + k + 1) → ℂ) 0).re = 0 := by simp [herm]
    rw [h0] at hre
    have h1 := hsum p.1
    have h2 : Complex.normSq p.2 * (herm (Hpk k r) v v).re ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) hvv
    have hs0 : ∑ b, Complex.normSq (p.1 b) = 0 := by linarith
    have ha : p.1 = 0 := by
      funext b
      have hb := (Finset.sum_eq_zero_iff_of_nonneg
        (fun b _ => Complex.normSq_nonneg (p.1 b))).1 hs0 b (Finset.mem_univ b)
      simpa using hb
    have ht : p.2 • v = 0 := by
      rw [hM, ha, map_zero, zero_add] at hp0
      exact hp0
    exact Prod.ext ha ((smul_eq_zero.1 ht).resolve_right hv0)
  have hdim := hN k r (LinearMap.range M) hnp
  rw [LinearMap.finrank_range_of_inj hinj] at hdim
  simp [Module.finrank_prod] at hdim

end PI.FrameInd.UPosW
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.ColsConjTranspose =====

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.FrameInductionOf =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.FrameInductionOf", "h": "module\n\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.NegBound\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.FinrankUperpOfDet\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.FrameInd

theorem frame_induction_of (hS : SignStep) (hU : UPos) : GramIndependentSignature := by
  intro k r z z' γ hs hp
  have hdet := det_ne k r z z' γ hs hp
  have hQ := hS k r z z' γ hs hp hdet
  exact ⟨indep_of_det k r z z' γ hdet, hQ, hU k r z z' γ hs hp hdet hQ,
    finrank_Uperp_of_det k r z z' γ hdet⟩

end PI.FrameInd
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.FrameInductionOf =====

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.Counts =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.Counts", "h": "module\n\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.NonposCount\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.NegBound\nimport Formalism.FormalDegreeBessel.FormalDegreeRatio.ReverseCauchySchwarzHolds\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.FinrankUperpOfDet\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Coalgebra.IsFrobenius\nimport Mathlib.RingTheory.HopfAlgebra.Basic\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section
namespace PI.FrameInd.CountsW

open PI.FrameInd

def extZ {n : Type*} (p : n → Prop) [DecidablePred p] : ({i // p i} → ℂ) →ₗ[ℂ] (n → ℂ) where
  toFun y i := if h : p i then y ⟨i, h⟩ else 0
  map_add' y y' := by funext i; by_cases h : p i <;> simp [h]
  map_smul' c y := by funext i; by_cases h : p i <;> simp [h]

lemma extZ_apply {n : Type*} (p : n → Prop) [DecidablePred p] (y : {i // p i} → ℂ) (i : n) :
    extZ p y i = if h : p i then y ⟨i, h⟩ else 0 := rfl

lemma extZ_eq_zero {n : Type*} (p : n → Prop) [DecidablePred p] (y : {i // p i} → ℂ)
    (hy : extZ p y = 0) : y = 0 := by
  funext ⟨i, h⟩
  have h1 := congrFun hy i
  simpa [extZ_apply, h] using h1

lemma diag_eq {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * A * (hA.eigenvectorUnitary : Matrix n n ℂ) =
      diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) := by
  have h := hA.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_apply] at h
  simpa [Matrix.star_eq_conjTranspose, Function.comp_def] using h

lemma U_eq_zero {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (w : n → ℂ) (hw : (hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ w = 0) : w = 0 := by
  have hu : star (hA.eigenvectorUnitary : Matrix n n ℂ) * (hA.eigenvectorUnitary : Matrix n n ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 hA.eigenvectorUnitary.2
  calc w = (star (hA.eigenvectorUnitary : Matrix n n ℂ) * (hA.eigenvectorUnitary : Matrix n n ℂ)) *ᵥ w := by
        rw [hu, Matrix.one_mulVec]
    _ = star (hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ ((hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ w) := by
        rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [hw, Matrix.mulVec_zero]

lemma re_diag {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (w : n → ℂ) :
    (herm A ((hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ w) ((hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ w)).re =
      ∑ i, hA.eigenvalues i * Complex.normSq (w i) := by
  rw [herm_mulVec_mulVec, diag_eq, herm, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [mulVec_diagonal, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

lemma blockA_re (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (hz : inWb k r z)
    (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) (hc : ∀ b, c (Sum.inr b) = 0) :
    (herm (gramM k r z z' γ) c c).re =
      (herm (Hpk k r) z z).re * Complex.normSq (c (Sum.inl (Fin.last r))) := by
  have hb : ∀ a b, gramM k r z z' γ (Sum.inl a) (Sum.inl b) = (herm (Hpk k r) z z • ggLastU r) a b :=
    fun a b => ggBlockA k r z hz a b
  simp only [herm, dotProduct, mulVec, Fintype.sum_sum_type, hc, star_zero, zero_mul, mul_zero,
    Finset.sum_const_zero, add_zero, hb, Matrix.smul_apply, smul_eq_mul, Pi.star_apply]
  rw [Finset.sum_eq_single (Fin.last r) (fun a _ ha => by simp [ggLastU, ha]) (by simp)]
  rw [Finset.sum_eq_single (Fin.last r) (fun b _ hb => by simp [ggLastU, hb]) (by simp)]
  simp [ggLastU, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem positive_count : PosCount := by
  intro k r z z' γ hs hp hdet
  set hA := isHerm k r z z' γ with hhA
  let p : Fin (r + 1) ⊕ Fin (r + 1) → Prop := fun i => 0 < hA.eigenvalues i
  let ψ : ({i // p i} → ℂ) →ₗ[ℂ] (Fin (r + 1) → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (Sum.inr : Fin (r + 1) → Fin (r + 1) ⊕ Fin (r + 1))).comp
      ((Matrix.mulVecLin (hA.eigenvectorUnitary : Matrix _ _ ℂ)).comp (extZ p))
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hinr : ∀ b, ((hA.eigenvectorUnitary : Matrix (Fin (r + 1) ⊕ Fin (r + 1))
        (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) *ᵥ extZ p y) (Sum.inr b) = 0 := by
      intro b
      have := congrFun hy b
      simpa [ψ, LinearMap.funLeft_apply] using this
    have h1 := re_diag hA (extZ p y)
    rw [blockA_re k r z z' γ hs.2.1.1 _ hinr] at h1
    have hT : (herm (Hpk k r) z z).re < 0 := by
      have := hs.2.1.2; simp only [Tz] at this; linarith
    have hl : (herm (Hpk k r) z z).re *
        Complex.normSq (((hA.eigenvectorUnitary : Matrix (Fin (r + 1) ⊕ Fin (r + 1))
          (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) *ᵥ extZ p y) (Sum.inl (Fin.last r))) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hT.le (Complex.normSq_nonneg _)
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin (r + 1) ⊕ Fin (r + 1))),
        0 ≤ hA.eigenvalues i * Complex.normSq (extZ p y i) := by
      intro i _
      rw [extZ_apply]
      split_ifs with h
      · exact mul_nonneg h.le (Complex.normSq_nonneg _)
      · simp
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1
      (le_antisymm (h1 ▸ hl) (Finset.sum_nonneg hnn))
    funext t
    have := hz t.1 (Finset.mem_univ _)
    rw [extZ_apply, dite_eq_left t.2] at this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (ne_of_gt t.2)
    · simpa [Complex.normSq_eq_zero] using h
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_fintype_fun_eq_card] using this

theorem nonposCount_of (hN : NegBound) : NonposCount := by
  intro k r z z' γ hs hp hdet
  set hA := isHerm k r z z' γ with hhA
  let q : Fin (r + 1) ⊕ Fin (r + 1) → Prop := fun i => ¬ 0 < hA.eigenvalues i
  let Φ : ({i // q i} → ℂ) →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ) :=
    (Matrix.mulVecLin (Vc k r z z' γ)).comp
      ((Matrix.mulVecLin (hA.eigenvectorUnitary : Matrix _ _ ℂ)).comp (extZ q))
  have hΦ : ∀ y, Φ y = Vc k r z z' γ *ᵥ ((hA.eigenvectorUnitary : Matrix _ _ ℂ) *ᵥ extZ q y) :=
    fun y => rfl
  have hre : ∀ y, (herm (Hpk k r) (Φ y) (Φ y)).re ≤ 0 := by
    intro y
    rw [hΦ, herm_Vc, re_diag]
    apply Finset.sum_nonpos
    intro i _
    rw [extZ_apply]
    split_ifs with h
    · exact mul_nonpos_of_nonpos_of_nonneg (not_lt.1 h) (Complex.normSq_nonneg _)
    · simp
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    rw [hΦ] at hy
    exact extZ_eq_zero q y (U_eq_zero hA _ (Vc_inj k r z z' γ hdet _ hy))
  have h1 := hN k r (LinearMap.range Φ) (by rintro x ⟨y, rfl⟩; exact hre y)
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card] at h1
  exact h1

end PI.FrameInd.CountsW
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.Counts =====

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.QBuild =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.QBuild", "h": "module\n\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.NegBound\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.NonposCount\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.Counts\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.NegativeBound\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.FrameInd

lemma submatrix_conj {ι κ : Type*} [Fintype ι] [Fintype κ] (W M : Matrix ι ι ℂ) (e : κ ≃ ι) :
    (W.submatrix id e)ᴴ * M * W.submatrix id e = (Wᴴ * M * W).submatrix e e := by
  ext i j
  simp [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]

theorem signStep_of (hP : PosCount) (hN : NonposCount) : SignStep := by
  intro k r z z' γ hs hp hdet
  set hA := isHerm k r z z' γ with hhA
  set ev := hA.eigenvalues with hev
  have h1 : Fintype.card {i // 0 < ev i} ≤ r + 1 := hP k r z z' γ hs hp hdet
  have h2 : Fintype.card {i // ¬ 0 < ev i} ≤ r + 1 := hN k r z z' γ hs hp hdet
  have h3 := Fintype.card_subtype_compl (fun i : Fin (r + 1) ⊕ Fin (r + 1) => 0 < ev i)
  have h4 : Fintype.card {i : Fin (r + 1) ⊕ Fin (r + 1) // 0 < ev i} ≤
      Fintype.card (Fin (r + 1) ⊕ Fin (r + 1)) := Fintype.card_subtype_le _
  simp only [Fintype.card_sum, Fintype.card_fin] at h3 h4
  have hcP : Fintype.card {i // 0 < ev i} = r + 1 := by omega
  have hcN : Fintype.card {i // ¬ 0 < ev i} = r + 1 := by omega
  have hne : ∀ i, ev i ≠ 0 := by
    intro i h0
    apply hdet
    rw [hA.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← hev, h0]; simp)
  let eP : {i // 0 < ev i} ≃ Fin (r + 1) := Fintype.equivFinOfCardEq hcP
  let eN : {i // ¬ 0 < ev i} ≃ Fin (r + 1) := Fintype.equivFinOfCardEq hcN
  let e : Fin (r + 1) ⊕ Fin (r + 1) ≃ Fin (r + 1) ⊕ Fin (r + 1) :=
    (Equiv.sumCongr eP.symm eN.symm).trans (Equiv.sumCompl fun i => 0 < ev i)
  let U : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ := hA.eigenvectorUnitary
  let s : Fin (r + 1) ⊕ Fin (r + 1) → ℂ := fun i => (((Real.sqrt |ev i|)⁻¹ : ℝ) : ℂ)
  let f : Fin (r + 1) ⊕ Fin (r + 1) → ℂ := fun i => if 0 < ev i then 1 else -1
  have hW : (U * diagonal s)ᴴ * gramM k r z z' γ * (U * diagonal s) = diagonal f := by
    have hd : Uᴴ * gramM k r z z' γ * U = diagonal (fun i => ((ev i : ℝ) : ℂ)) := CountsW.diag_eq hA
    rw [conjTranspose_mul, diagonal_conjTranspose]
    calc (star s |> diagonal) * Uᴴ * gramM k r z z' γ * (U * diagonal s)
        = diagonal (star s) * (Uᴴ * gramM k r z z' γ * U) * diagonal s := by simp only [Matrix.mul_assoc]
      _ = diagonal f := by
        rw [hd, diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 1
        funext i
        have hpos : 0 < |ev i| := abs_pos.2 (hne i)
        have hsq : Real.sqrt |ev i| * Real.sqrt |ev i| = |ev i| := Real.mul_self_sqrt hpos.le
        have hsq0 : Real.sqrt |ev i| ≠ 0 := by positivity
        simp only [s, f, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
        have : (Real.sqrt |ev i|)⁻¹ * ev i * (Real.sqrt |ev i|)⁻¹ = if 0 < ev i then 1 else -1 := by
          rw [mul_comm, ← mul_assoc, ← mul_inv, hsq]
          split_ifs with h
          · rw [abs_of_pos h, inv_mul_cancel₀ (hne i)]
          · rw [abs_of_neg (lt_of_le_of_ne (not_lt.1 h) (hne i)), inv_neg, neg_mul,
              inv_mul_cancel₀ (hne i)]
        rw [this]; split_ifs <;> simp
  have hfe : f ∘ e = Sum.elim (fun _ => 1) (fun _ => -1) := by
    funext i
    rcases i with a | a
    · simp [f, e, Equiv.sumCompl_apply_inl, (eP.symm a).2]
    · simp [f, e, Equiv.sumCompl_apply_inr, (eN.symm a).2]
  have hD : ((U * diagonal s).submatrix id e)ᴴ * gramM k r z z' γ * (U * diagonal s).submatrix id e =
      diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
    rw [submatrix_conj, hW, submatrix_diagonal_equiv, hfe]
  refine ⟨(U * diagonal s).submatrix id e, ?_, ?_⟩
  · rw [isUnit_iff_ne_zero]
    intro h0
    have := congrArg Matrix.det hD
    rw [det_mul, det_mul, h0, mul_zero, det_diagonal] at this
    refine (Finset.prod_ne_zero_iff.2 fun i _ => ?_) this.symm
    rcases i with a | a <;> simp
  · rw [hD]
    ext i j
    rcases i with a | a <;> rcases j with b | b <;> simp [diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp

theorem signStep : SignStep :=
  signStep_of PI.FrameInd.CountsW.positive_count (PI.FrameInd.CountsW.nonposCount_of negative_bound)

end PI.FrameInd
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.QBuild =====

-- ===== clump member: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FrameInd =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FrameInd", "h": "module\n\npublic import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.ColsConjTranspose\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.FrameInductionOf\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.NegativeBound\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.QBuild\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

theorem frameInd : Formalism.FourierDecayAlt.C2.GramIndependentSignature :=
  PI.FrameInd.frame_induction_of PI.FrameInd.signStep (PI.FrameInd.UPosW.uPos_of PI.FrameInd.negative_bound)
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FrameInd =====
