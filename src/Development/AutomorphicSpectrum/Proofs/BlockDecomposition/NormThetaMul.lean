module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.GaloisBoundSecond
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField

namespace GlobalTheory.CompanionTheory.MassCount

variable {F : Type} [Field F] [NumberField F]

theorem count_box [IsTotallyReal F] (N : ℕ) (hN : 0 < N) (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (B : ℝ) (hB : 0 ≤ B) :
    {x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = N * x) ∧ ∀ w : InfinitePlace F, w x ≤ B}.Finite ∧
    (({x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = N * x) ∧ ∀ w : InfinitePlace F, w x ≤ B}.ncard : ℕ) : ℝ) *
      (Ideal.absNorm I : ℝ) ≤ (4 * B * N) ^ Module.finrank ℚ F :=
  _root_.UpperTheory.Reformulated.B.GaloisBoundSecond.main N hN I hI B hB

theorem norm_theta_mul [IsTotallyReal F] (θ : ℝ →+* InfiniteAdeleRing F) (ε : ℝ) (x : F) (w : InfinitePlace F) :
    ‖(θ ε * algebraMap F (InfiniteAdeleRing F) x) w‖ = |ε| * w x := by
  have hw := IsTotallyReal.isReal w
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  let ev : InfiniteAdeleRing F →+* w.Completion := Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w
  have h0 : ((e : w.Completion →+* ℝ).comp (ev.comp θ)) = RingHom.id ℝ := Subsingleton.elim _ _
  have h1 : e (ev (θ ε)) = ε := DFunLike.congr_fun h0 ε
  have hn : ∀ a : w.Completion, ‖a‖ = |e a| := by
    intro a
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply, ← Real.norm_eq_abs]
    exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) a).symm
  have h2 : (θ ε * algebraMap F (InfiniteAdeleRing F) x) w = ev (θ ε) * (algebraMap F (InfiniteAdeleRing F) x) w := rfl
  rw [h2, norm_mul, hn (ev (θ ε)), h1, InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.norm_coe]
  rfl

theorem countBd : PositivityTheory.Rg.Mass.CountBd := by
  intro F _ _ hF θ _ K hK N hN
  haveI := hF
  have hb : ∀ w : InfinitePlace F, ∃ c : ℝ, ∀ a ∈ K, ‖(a : InfiniteAdeleRing F) w‖ ≤ c := fun w =>
    hK.exists_bound_of_continuousOn (f := fun a : InfiniteAdeleRing F => a w)
      (continuous_apply w).continuousOn
  choose c hc using hb
  set R : ℝ := ∑ w, |c w| with hRdef
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hcR : ∀ w, c w ≤ R := fun w =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun w => |c w|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w))
  refine ⟨(4 * R * N) ^ Module.finrank ℚ F, fun ε hε I hI => ?_⟩
  have hsub : {x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = N * x) ∧ θ ε * algebraMap F (InfiniteAdeleRing F) x ∈ K} ⊆
      {x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = N * x) ∧ ∀ w : InfinitePlace F, w x ≤ R / ε} := by
    rintro x ⟨hx, hy, hxK⟩
    refine ⟨hx, hy, fun w => ?_⟩
    have h := hc w _ hxK
    rw [norm_theta_mul, abs_of_pos hε] at h
    rw [le_div_iff₀ hε, mul_comm]
    exact h.trans (hcR w)
  obtain ⟨hfin, hcount⟩ := count_box N hN I hI (R / ε) (div_nonneg hR0 hε.le)
  refine ⟨hfin.subset hsub, ?_⟩
  have hI0 : (0 : ℝ) < Ideal.absNorm I := by
    have : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast Nat.pos_of_ne_zero this
  have hle := Set.ncard_le_ncard hsub hfin
  rw [le_div_iff₀ hI0]
  have hle' := (mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ).2 hle) hI0.le).trans hcount
  calc _ ≤ ε ^ Module.finrank ℚ F * (4 * (R / ε) * N) ^ Module.finrank ℚ F := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hle' (by positivity)
    _ = (4 * R * N) ^ Module.finrank ℚ F := by
        rw [← mul_pow]
        congr 1
        field_simp

end GlobalTheory.CompanionTheory.MassCount
end
