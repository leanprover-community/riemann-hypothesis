module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConjugateTransposeLeibniz.ExpMulVecFix
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuantumDeterminantCommute.Development
public import Formalism.FormalDegreeBessel.FinalG
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.Deriv.Linear
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

open Matrix Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

namespace QmCapCommW

section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma exp_mul_fix {n : ℕ} (X E : Matrix (Fin n) (Fin n) ℂ) (hXE : X * E = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) * E = E := by
  apply QnYLeibnizW.exp_mul_fix <;> assumption

lemma exp_curve_cont {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) := NormedSpace.exp_continuous.comp (Complex.continuous_ofReal.smul continuous_const)

end Linfty

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma exp_mulVec_fix {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (hXv : X *ᵥ v = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) *ᵥ v = v := by
  apply QnYLeibnizW.exp_mulVec_fix <;> assumption

lemma exp_mem_UH {n : ℕ} (H Y : Matrix (Fin n) (Fin n) ℂ) (hH : H * H = 1) (hY : Yᴴ * H + H * Y = 0) :
    NormedSpace.exp Y ∈ UH H := by
  apply QnYLeibnizW.exp_mem_UH <;> assumption

lemma glev_mul {k r : ℕ} {i : Fin (r + 1)} {g h : Mx k r} (hg : g ∈ Glev k r i) (hh : h ∈ Glev k r i) :
    g * h ∈ Glev k r i := by
  simp only [Glev, UH, Set.mem_setOf_eq] at hg hh ⊢
  obtain ⟨hg1, hg2⟩ := hg
  obtain ⟨hh1, hh2⟩ := hh
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · rw [Matrix.conjTranspose_mul]
    calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hg1, hh1]
  · rw [← Matrix.mulVec_mulVec, (hh2 a ha).1, (hg2 a ha).1]
  · rw [← Matrix.mulVec_mulVec, (hh2 a ha).2, (hg2 a ha).2]

lemma exp_mem_glev {k r : ℕ} {i : Fin (r + 1)} {X : Mx k r} (hX : inLieLev k r i X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i := by
  obtain ⟨hL, hF⟩ := hX
  have hH : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  refine ⟨exp_mem_UH _ _ hH ?_, fun a ha => ?_⟩
  · rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, hL, smul_zero]
  · obtain ⟨h1, h2⟩ := hF a ha
    exact ⟨exp_mulVec_fix X _ h1 t, exp_mulVec_fix X _ h2 t⟩

lemma skew_minus {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) (hh : Hᴴ = H) (hHH : H * H = 1) :
    (Z - H * Zᴴ * H)ᴴ * H + H * (Z - H * Zᴴ * H) = 0 := by
  have e1 : (Z - H * Zᴴ * H)ᴴ = Zᴴ - H * Z * H := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hh, Matrix.mul_assoc H Z H]
  rw [e1, Matrix.sub_mul, Matrix.mul_sub]
  have e2 : H * Z * H * H = H * Z := by rw [Matrix.mul_assoc (H * Z) H H, hHH, Matrix.mul_one]
  have e3 : H * (H * Zᴴ * H) = Zᴴ * H := by
    rw [← Matrix.mul_assoc H (H * Zᴴ) H, ← Matrix.mul_assoc H H Zᴴ, hHH, Matrix.one_mul]
  rw [e2, e3]
  abel

lemma skew_plus {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) (hh : Hᴴ = H) (hHH : H * H = 1) :
    H * (Z + H * Zᴴ * H) - (Z + H * Zᴴ * H)ᴴ * H = 0 := by
  have e1 : (Z + H * Zᴴ * H)ᴴ = Zᴴ + H * Z * H := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hh, Matrix.mul_assoc H Z H]
  rw [e1, Matrix.add_mul, Matrix.mul_add]
  have e2 : H * Z * H * H = H * Z := by rw [Matrix.mul_assoc (H * Z) H H, hHH, Matrix.mul_one]
  have e3 : H * (H * Zᴴ * H) = Zᴴ * H := by
    rw [← Matrix.mul_assoc H (H * Zᴴ) H, ← Matrix.mul_assoc H H Zᴴ, hHH, Matrix.one_mul]
  rw [e2, e3]
  abel

lemma hpart1_skew {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) (hh : Hᴴ = H) (hHH : H * H = 1) :
    (hpart1 H Z)ᴴ * H + H * hpart1 H Z = 0 := by
  have hinv : H⁻¹ = H := Matrix.inv_eq_left_inv hHH
  unfold hpart1
  rw [hinv, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by
    have h1 := Complex.conj_ofReal (1 / 2 : ℝ)
    push_cast at h1
    exact h1
  rw [hs, ← smul_add, skew_minus H Z hh hHH, smul_zero]

lemma hpart2_skew {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) (hh : Hᴴ = H) (hHH : H * H = 1) :
    (hpart2 H Z)ᴴ * H + H * hpart2 H Z = 0 := by
  have hinv : H⁻¹ = H := Matrix.inv_eq_left_inv hHH
  unfold hpart2
  rw [hinv, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
  have hs : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    simp only [Complex.star_def, map_div₀, map_one, map_mul, Complex.conj_I, map_ofNat]
    ring
  rw [hs, neg_smul, neg_add_eq_sub, ← smul_sub, skew_plus H Z hh hHH, smul_zero]

lemma hpk_zero {k r : ℕ} (i : Fin (r + 1)) (p : Fin (mdim k r i)) (a : Fin r) (ha : a.val < i.val) :
    Hpk k r (posL k r i p) (eI k r a) = 0 ∧ Hpk k r (posL k r i p) (esI k r a) = 0 := by
  have hp := p.isLt
  have hi := i.isLt
  unfold mdim at hp
  constructor <;> simp only [Hpk, posL, eI, esI, Fin.ext_iff, Fin.val_mk] <;> split_ifs <;>
    first | rfl | (exfalso; omega)

lemma col_zero {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) (h : ∀ j, Y j c = 0) : Y *ᵥ bvec c = 0 := by
  funext j
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, h]

lemma single_ct {n : ℕ} (a b : Fin n) : (Matrix.single a b (1 : ℂ))ᴴ = Matrix.single b a 1 := by
  ext i j
  rw [Matrix.conjTranspose_apply, Matrix.single_apply, Matrix.single_apply]
  split_ifs <;> simp_all

lemma hpart_col {k r : ℕ} {i : Fin (r + 1)} (a b : Fin (mdim k r i)) (c : Fin (2 * r + k + 1))
    (hcb : c ≠ posL k r i b) (hac : Hpk k r (posL k r i a) c = 0) (s : ℂ) (j : Fin (2 * r + k + 1)) :
    (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ) + s • ((Hpk k r)⁻¹ *
      (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ))ᴴ * Hpk k r)) j c = 0 := by
  rw [single_ct]
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, hac, Ne.symm hcb]

lemma hpart1_lie {k r : ℕ} (i : Fin (r + 1)) (a b : Fin (mdim k r i)) :
    inLieLev k r i (hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) := by
  refine ⟨hpart1_skew _ _ (hpkFacts k r).1 (hpkFacts k r).2.1, fun a' ha' => ⟨?_, ?_⟩⟩
  all_goals
    refine col_zero _ _ fun j => ?_
    unfold hpart1
    rw [Matrix.smul_apply, sub_eq_add_neg, ← neg_one_smul ℂ ((Hpk k r)⁻¹ * _ * _)]
  · rw [hpart_col a b _ (by simp only [posL, eI, ne_eq, Fin.ext_iff]; omega) (hpk_zero i a a' ha').1, smul_zero]
  · rw [hpart_col a b _ (by simp only [posL, esI, ne_eq, Fin.ext_iff]; have := b.isLt; unfold mdim at this; omega)
      (hpk_zero i a a' ha').2, smul_zero]

lemma hpart2_lie {k r : ℕ} (i : Fin (r + 1)) (a b : Fin (mdim k r i)) :
    inLieLev k r i (hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) := by
  refine ⟨hpart2_skew _ _ (hpkFacts k r).1 (hpkFacts k r).2.1, fun a' ha' => ⟨?_, ?_⟩⟩
  all_goals
    refine col_zero _ _ fun j => ?_
    unfold hpart2
    rw [Matrix.smul_apply, ← one_smul ℂ ((Hpk k r)⁻¹ * _ * _)]
  · rw [hpart_col a b _ (by simp only [posL, eI, ne_eq, Fin.ext_iff]; omega) (hpk_zero i a a' ha').1, smul_zero]
  · rw [hpart_col a b _ (by simp only [posL, esI, ne_eq, Fin.ext_iff]; have := b.isLt; unfold mdim at this; omega)
      (hpk_zero i a a' ha').2, smul_zero]

lemma rdV_congr {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r : ℕ} {i : Fin (r + 1)}
    {D : Set (Mx k r)} (hD : IsOpen D) {f f' : Mx k r → E} (h : ∀ g ∈ Glev k r i ∩ D, f g = f' g)
    {X : Mx k r} (hX : inLieLev k r i X) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    RdV X f g = RdV X f' g := by
  unfold RdV
  apply Filter.EventuallyEq.deriv_eq
  have hcont : Continuous (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) :=
    continuous_const.mul (exp_curve_cont X)
  have hmem : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), g * NormedSpace.exp ((t : ℂ) • X) ∈ D := by
    apply hcont.continuousAt.preimage_mem_nhds
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one]
    exact hD.mem_nhds hg.2
  filter_upwards [hmem] with t ht
  exact h _ ⟨glev_mul hg.1 (exp_mem_glev hX t), ht⟩

theorem capelli_operator_congruence : CapCongr := by
  intro E _ _ k r i D a b f f' hD h g hg
  show EabH (Hpk k r) _ _ f g = EabH (Hpk k r) _ _ f' g
  unfold EabH
  rw [rdV_congr hD h (hpart1_lie i a b) hg, rdV_congr hD h (hpart2_lie i a b) hg]

end QmCapCommW
