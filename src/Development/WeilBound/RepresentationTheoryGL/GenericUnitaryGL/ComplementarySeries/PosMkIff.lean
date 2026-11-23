module

import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.PosMkIff
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Filter Topology Module

namespace PositivityTheory.RgGu.NR.Sig

def qf {n : ℕ} (M : Fin n → Fin n → ℂ) (x y : Fin n → ℂ) : ℂ := ∑ i, ∑ j, x i * (star (y j) * M i j)

theorem cont_qf {n : ℕ} :
    Continuous fun p : (Fin n → Fin n → ℂ) × (Fin n → ℂ) × (Fin n → ℂ) => qf p.1 p.2.1 p.2.2 := by
  unfold qf
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((continuous_apply i).comp (continuous_fst.comp continuous_snd)).mul
    ((continuous_star.comp ((continuous_apply j).comp (continuous_snd.comp continuous_snd))).mul
      ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst)))

theorem qf_smul {n : ℕ} (M : Fin n → Fin n → ℂ) (a : ℂ) (x y : Fin n → ℂ) :
    qf M (a • x) (a • y) = a * star a * qf M x y := by
  simp only [qf, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem qf_single {n : ℕ} (M : Fin n → Fin n → ℂ) (i j : Fin n) :
    qf M (Pi.single i 1) (Pi.single j 1) = M i j := by
  classical
  simp [qf, Pi.single_apply]

variable {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

abbrev Sq (W : Type) [AddCommGroup W] [Module ℂ W] := W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ

abbrev ef (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] :
    W ≃ₗ[ℂ] (Fin (finrank ℂ W) → ℂ) := (Module.finBasis ℂ W).equivFun

def gram (B : Sq W) : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ :=
  fun i j => B (Module.finBasis ℂ W i) (Module.finBasis ℂ W j)

def mk (M : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ) : Sq W :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => qf M (ef W v) (ef W w))
    (fun v v' w => by simp only [qf, map_add (f := _), Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c v w => by
      simp only [qf, map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    (fun v w w' => by
      simp only [qf, map_add (f := _), Pi.add_apply, star_add, add_mul, mul_add, Finset.sum_add_distrib])
    (fun c v w => by
      simp only [qf, map_smul, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum, starRingEnd_apply]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)

theorem mk_apply (M : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ) (v w : W) :
    mk M v w = qf M (ef W v) (ef W w) := rfl

theorem expand (B : Sq W) (v w : W) : B v w = qf (gram B) (ef W v) (ef W w) := by
  conv_lhs => rw [← (Module.finBasis ℂ W).sum_equivFun v, ← (Module.finBasis ℂ W).sum_equivFun w]

  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul,
  qf, gram, starRingEnd_apply, Finset.mul_sum, ef]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem mk_gram (B : Sq W) : mk (gram B) = B := by
  ext v w
  rw [mk_apply, expand]

theorem gram_mk (M : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ) : gram (mk M : Sq W) = M := by
  funext i j
  have h : ∀ a, (Module.finBasis ℂ W).equivFun (Module.finBasis ℂ W a) = Pi.single a 1 := fun a => by
    funext b
    rw [Module.Basis.equivFun_self]
    simp [Pi.single_apply, eq_comm]
  simp only [gram, mk_apply, ef, h]
  exact qf_single M i j

theorem gram_smul (c : ℂ) (B : Sq W) : gram (c • B) = c • gram B := by
  funext i j
  simp [gram]

section Fam

variable {I : Type} (ι : I → I) (T : I → Module.End ℂ W)

def Inv (B : Sq W) : Prop := ∀ i v w, B (T i v) w = B v (T (ι i) w)

def Herm (B : Sq W) : Prop := ∀ v w, B w v = starRingEnd ℂ (B v w)

def Pos (B : Sq W) : Prop := ∀ v, v ≠ 0 → 0 < (B v v).re

variable {ι T}

theorem ker_bot (hsim : ∀ U : Submodule ℂ W, (∀ i, ∀ w ∈ U, T i w ∈ U) → U = ⊥ ∨ U = ⊤) (B : Sq W) (hB : B ≠ 0)
    (hinv : Inv ι T B) : LinearMap.ker B = ⊥ := by
  have hst : ∀ i, ∀ w ∈ LinearMap.ker B, T i w ∈ LinearMap.ker B := by
    intro i w hw
    rw [LinearMap.mem_ker] at hw ⊢
    ext u
    rw [hinv, hw]
    rfl
  rcases hsim (LinearMap.ker B) hst with h | h
  · exact h
  · exact absurd (LinearMap.ker_eq_top.1 h) hB

theorem inv_sub {B B' : Sq W} (h : Inv ι T B) (h' : Inv ι T B') (c : ℂ) : Inv ι T (B - c • B') := by
  intro i v w
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, h i v w, h' i v w]

theorem uniq (hsim : ∀ U : Submodule ℂ W, (∀ i, ∀ w ∈ U, T i w ∈ U) → U = ⊥ ∨ U = ⊤) (B₀ B : Sq W) (h0 : B₀ ≠ 0)
    (hinv0 : Inv ι T B₀) (hinv : Inv ι T B) : ∃ c : ℂ, B = c • B₀ := by
  apply CompanionTheory.RgGu.NR.Sig.uniq <;> assumption

theorem real_of {B₀ B : Sq W} (h0 : B₀ ≠ 0) (hh0 : Herm B₀) (hh : Herm B) (c : ℂ) (hc : B = c • B₀) :
    starRingEnd ℂ c = c := by
  obtain ⟨v, w, hvw⟩ : ∃ v w, B₀ v w ≠ 0 := by
    by_contra hn
    push Not at hn
    exact h0 (by ext v w; simp [hn])
  have e1 := hh v w
  rw [hc] at e1
  simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, hh0 v w] at e1
  have hz : starRingEnd ℂ (B₀ v w) ≠ 0 := (map_ne_zero _).2 hvw
  exact (mul_right_cancel₀ hz e1).symm

theorem pos_of (B : Sq W) (hh : Herm B) (hk : LinearMap.ker B = ⊥) (hsd : ∀ v, 0 ≤ (B v v).re) : Pos B := by
  apply CompanionTheory.RgGu.NR.Sig.pos_of <;> assumption

end Fam

theorem pos_mk_iff (M : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ) :
    (∀ v : W, v ≠ 0 → 0 < ((mk M : Sq W) v v).re) ↔ ∀ c, c ≠ 0 → 0 < (qf M c c).re := by
  constructor
  · intro h c hc
    have := h ((ef W).symm c) (((ef W).symm.map_ne_zero_iff).2 hc)
    rwa [mk_apply, LinearEquiv.apply_symm_apply] at this
  · intro h v hv
    rw [mk_apply]
    exact h _ ((LinearEquiv.map_ne_zero_iff _).2 hv)

theorem pos_open {n : ℕ} (M : Fin n → Fin n → ℂ) (hM : ∀ c : Fin n → ℂ, c ≠ 0 → 0 < (qf M c c).re) :
    ∀ᶠ M' in 𝓝 M, ∀ c : Fin n → ℂ, c ≠ 0 → 0 < (qf M' c c).re := by
  apply CompanionTheory.RgGu.NR.Sig.pos_open <;> assumption

theorem mk_smul (a : ℂ) (M : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ) : (mk (a • M) : Sq W) = a • mk M := by
  ext v w
  simp only [mk_apply, qf, Pi.smul_apply, smul_eq_mul, LinearMap.smul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

section Real

variable {I : Type} {ι : I → I} {T : I → Module.End ℂ W}

omit [FiniteDimensional ℂ W] in
theorem herm_smul {B : Sq W} (h : Herm B) (r : ℝ) : Herm ((r : ℂ) • B) := by
  intro v w
  simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal, h v w]

omit [FiniteDimensional ℂ W] in
theorem inv_smul {B : Sq W} (h : Inv ι T B) (c : ℂ) : Inv ι T (c • B) := by
  intro i v w
  simp only [LinearMap.smul_apply, h i v w]

theorem normalize (B : Sq W) (hB : B ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ‖gram ((r : ℂ) • B)‖ = 1 := by
  have hg : gram B ≠ 0 := by
    intro h
    apply hB
    rw [← mk_gram B, h]
    ext v w
    simp [mk_apply, qf]
  refine ⟨‖gram B‖⁻¹, inv_pos.2 (norm_pos_iff.2 hg), ?_⟩
  rw [gram_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (norm_pos_iff.2 hg)),
    inv_mul_cancel₀ (norm_ne_zero_iff.2 hg)]

end Real


theorem lim_form {I : Type} (ι : I → I) (T : ℝ → I → Module.End ℂ W)
    (hc : ∀ (i : I) (w : W) (l : Module.Dual ℂ W), Continuous fun s => l (T s i w))
    (s : ℕ → ℝ) (p : ℝ) (hs : Tendsto s atTop (𝓝 p)) (B : ℕ → Sq W) (hinv : ∀ k, Inv ι (T (s k)) (B k))
    (hh : ∀ k, Herm (B k)) (hn : ∀ k, ‖gram (B k)‖ = 1) :
    ∃ (φ : ℕ → ℕ) (M : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ), StrictMono φ ∧ ‖M‖ = 1 ∧
      Tendsto (fun k => gram (B (φ k))) atTop (𝓝 M) ∧ Inv ι (T p) (mk M) ∧ Herm (mk M) ∧
      ∀ v w, Tendsto (fun k => B (φ k) v w) atTop (𝓝 (mk M v w)) := by
  apply CompanionTheory.RgGu.NR.Sig.lim_form <;> assumption

end PositivityTheory.RgGu.NR.Sig

namespace PositivityTheory.RgGu.NR

open Sig


theorem signature : Signature := by
  apply CompanionTheory.RgGu.NR.signature <;> assumption

end PositivityTheory.RgGu.NR
