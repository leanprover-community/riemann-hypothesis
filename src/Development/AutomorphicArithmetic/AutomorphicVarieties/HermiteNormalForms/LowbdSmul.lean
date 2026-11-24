module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulStrictMono
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

private theorem lowbd_cont (L : Type) [Field L] [NumberField L] (N : ℕ) :
    Continuous (fun p : HS L N × VR L N => qR p.1 p.2) := by
  unfold qR mat
  simp only [dotProduct, mulVec, Matrix.of_apply, Pi.star_apply]
  have hv : Continuous fun p : HS L N × VR L N => (p.1 : InfinitePlace L → Fin N → Fin N → ℂ) :=
    continuous_subtype_val.comp continuous_fst
  have hz : Continuous fun p : HS L N × VR L N => (p.2 : InfinitePlace L → Fin N → ℂ) := continuous_snd
  refine continuous_finsetSum _ fun w _ => Complex.continuous_re.comp ?_
  refine continuous_finsetSum _ fun i _ => ?_
  refine (continuous_star.comp ((continuous_apply i).comp ((continuous_apply w).comp hz))).mul ?_
  refine continuous_finsetSum _ fun j _ => ?_
  exact ((continuous_apply j).comp ((continuous_apply i).comp ((continuous_apply w).comp hv))).mul
    ((continuous_apply j).comp ((continuous_apply w).comp hz))

private theorem lowbd_smul {L : Type} [Field L] [NumberField L] {N : ℕ} (k : HS L N) (r : ℝ)
    (z : VR L N) : qR k (r • z) = r ^ 2 * qR k z := by
  unfold qR
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Pi.smul_apply, star_smul, star_trivial, mulVec_smul, dotProduct_smul, smul_dotProduct,
    Complex.smul_re, smul_eq_mul]
  ring

private theorem lowbd_pos {L : Type} [Field L] [NumberField L] {N : ℕ} {h : HS L N}
    (hh : h ∈ Pos L N) {z : VR L N} (hz : z ≠ 0) : 0 < qR h z := by
  have hne : ∃ w, z w ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hz (funext hc)
  obtain ⟨w0, hw0⟩ := hne
  have hp : ∀ w, (mat h w).PosDef := hh
  unfold qR
  apply Finset.sum_pos'
  · intro w _
    by_cases hw : z w = 0
    · simp [hw]
    · exact le_of_lt (Complex.pos_iff.mp ((hp w).dotProduct_mulVec_pos hw)).1
  · exact ⟨w0, Finset.mem_univ _, (Complex.pos_iff.mp ((hp w0).dotProduct_mulVec_pos hw0)).1⟩

theorem UpperTheory.V.KT.lowbd :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (h : HS L N), h ∈ Pos L N →
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in nhds h, ∀ z : VR L N, c * ‖z‖ ^ 2 ≤ qR k z := by
  intro L _ _ N h hh
  have hK : IsCompact (Metric.sphere (0 : VR L N) 1) := isCompact_sphere 0 1
  have hcont := lowbd_cont L N
  have hsec : Continuous fun z : VR L N => (h, z) := by fun_prop
  obtain ⟨m, hm, hmle⟩ := hK.exists_forall_le' (f := fun z => qR h z)
    (hcont.comp hsec).continuousOn (a := 0)
    (fun z hz => lowbd_pos hh (by
      intro h0
      rw [h0] at hz
      simp at hz))
  refine ⟨m / 2, by positivity, ?_⟩
  have hev : ∀ᶠ k in nhds h, ∀ z ∈ Metric.sphere (0 : VR L N) 1, m / 2 < qR k z := by
    apply hK.eventually_forall_of_forall_eventually
    intro z hz
    have hlt : m / 2 < qR h z := by linarith [hmle z hz]
    exact (hcont.tendsto (h, z)).eventually (lt_mem_nhds hlt)
  filter_upwards [hev] with k hk z
  by_cases hz : z = 0
  · subst hz
    have h0 : qR k (0 : VR L N) = 0 := by simpa using lowbd_smul k 0 (0 : VR L N)
    simp [h0]
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hu : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : VR L N) 1 := by
      simp [norm_smul, hn.ne']
    have hzu : ‖z‖ • (‖z‖⁻¹ • z) = z := by
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have hlt := hk _ hu
    calc m / 2 * ‖z‖ ^ 2 ≤ ‖z‖ ^ 2 * qR k (‖z‖⁻¹ • z) := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left hlt.le (by positivity)
      _ = qR k (‖z‖ • (‖z‖⁻¹ • z)) := (lowbd_smul k ‖z‖ _).symm
      _ = qR k z := by rw [hzu]
