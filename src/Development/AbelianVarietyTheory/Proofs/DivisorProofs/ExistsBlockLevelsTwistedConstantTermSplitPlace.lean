module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DgMatOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfBlockDetIntegralGLInvariantStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockLevelsEqIntegralGLOfUnramifiedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUpperTimesUnipotentMulBlockDiagonalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenConjStableSubgroupOfSplitLevelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedIntegralMatricesTwoSidedMuStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportTwistedConstantTermSplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLevelBlockLevelsSplitPlaceStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemULOfSplit

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
  GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct

namespace GlobalTheory.BCT.SplitLevels

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_UL_split {n : ℕ} {w : Pl E} (hw : IsSplitAt w) (x : GLw n w) : x ∈ UL n w := by
  rw [UL, if_pos hw]; exact Subgroup.mem_top x

theorem toSub_of_mem {G : Type} [Group G] (H : Subgroup G) (g : G) (hg : g ∈ H) : toSub H g = ⟨g, hg⟩ := by
  simp [toSub, hg]

theorem blk_zero {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) : blk h w m 0 = dgM h w m := by
  ext1
  rw [CtLevel.blk_val, dgM_val, dgMat, Matrix.mul_zero]

theorem ct_inv_blocks {a b n : ℕ} (h : a + b = n) (w : Pl E) (N : Subgroup (GLw n w)) (F : GLw n w → ℂ)
    (hNn : ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ x ∈ N, k⁻¹ * x * k ∈ N)
    (hF : ∀ y ∈ N, ∀ x, F (y * x) = F x ∧ F (x * y) = F x)
    (k : GLw a w × GLw b w) (hk1 : k.1 ∈ GlobalTheory.LFun.KGL w (n := a)) (hk2 : k.2 ∈ GlobalTheory.LFun.KGL w (n := b)) (hkN : dgM h w k ∈ N)
    (m : GLw a w × GLw b w) : ct h w F (k * m) = ct h w F m ∧ ct h w F (m * k) = ct h w F m := by
  apply _root_.GlobalTheory.BCT.CtLevel.ct_inv <;> assumption

theorem ctMu_inv_blocks {a b n : ℕ} (h : a + b = n) (w : Pl E) (hw : IsSplitAt w) (N : Subgroup (GLw n w))
    (K' : Subgroup (UL n w)) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ) (hf : IsHecke K' f)
    (hNK : N ≤ K'.map (UL n w).subtype) (hNn : ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ x ∈ N, k⁻¹ * x * k ∈ N)
    (k : GLw a w × GLw b w) (hk : k ∈ (lev₁ h w N μ).prod (lev₂ h w N μ)) (m : GLw a w × GLw b w) :
    ctMu h w μ f (k * m) = ctMu h w μ f m ∧ ctMu h w μ f (m * k) = ctMu h w μ f m := by
  apply _root_.GlobalTheory.BCT.CtLevel.ctMu_inv <;> assumption

theorem levels_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E),
    IsSplitAt w → ∀ (μ : (w.adicCompletion E)ˣ →* ℂˣ), IsOpen {x | μ x = 1} → ∀ K' : Subgroup (UL n w),
    IsLevel (MonoidHom.id _) (KL n w) K' → ∃ (K₁ : Subgroup (GLw a w)) (K₂ : Subgroup (GLw (n - a) w))
      (K'' : Subgroup (GLw n w)), IsLevel (thL a w) (GlobalTheory.LFun.KGL w (n := a)) K₁ ∧
      IsLevel (thL (n - a) w) (GlobalTheory.LFun.KGL w (n := (n - a))) K₂ ∧
      ((K' = KL n w ∧ ∀ u ∈ (GlobalTheory.LFun.KGL w (n := 1)), μ (GeneralLinearGroup.det u) = 1) →
        K₁ = GlobalTheory.LFun.KGL w (n := a) ∧ K₂ = GlobalTheory.LFun.KGL w (n := (n - a))) ∧
      IsOpen (K'' : Set (GLw n w)) ∧ K'' ≤ K'.map (UL n w).subtype ∧
      (K''.subgroupOf (GlobalTheory.LFun.KGL w (n := n))).Normal ∧
      (∀ m₁ ∈ K₁, ∀ m₂ ∈ K₂, blk (Nat.add_sub_cancel' ha) w (m₁, m₂) 0 ∈ K'') ∧
      (∀ m₁ ∈ K₁, ∀ m₂ ∈ K₂, μ (GeneralLinearGroup.det m₁ ^ (n - a) * GeneralLinearGroup.det m₂ ^ a) = 1) ∧
      ∀ f, IsHecke K' f → IsHecke (K₁.prod K₂) (ctMu (Nat.add_sub_cancel' ha) w μ f) := by
  intro E _ _ _ n a ha w hw μ hμ K' hK'
  obtain ⟨N, hNo, hNK, hNn, hNf⟩ := GlobalTheory.T.exists_open_conjStable_subgroup_of_splitLevel E n w K' hw hK'
  have hlev := GlobalTheory.T.isLevel_blockLevels_splitPlace E a (n - a) n (Nat.add_sub_cancel' ha) w N μ hw hNo hμ
  refine ⟨lev₁ (Nat.add_sub_cancel' ha) w N μ, lev₂ (Nat.add_sub_cancel' ha) w N μ, N, hlev.1, hlev.2, ?_, hNo, hNK,
    ?_, ?_, ?_, fun f hf => ⟨GlobalTheory.T.hasCompactSupport_twistedConstantTermSplitPlace E a (n - a) n _ w μ f hw hf.1, fun k hk m =>
      ctMu_inv_blocks _ w hw N K' μ f hf hNK hNn k hk m⟩⟩
  · rintro ⟨hK'e, hμ1⟩
    rw [hNf hK'e]
    exact GlobalTheory.T.blockLevels_eq_integralGL_of_unramified E a (n - a) n _ w μ hμ1
  · refine ⟨fun x hx k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have := hNn _ (inv_mem k.2) _ hx
    simpa [mul_assoc] using this
  · intro m₁ hm₁ m₂ hm₂
    rw [blk_zero]
    have e : ((m₁, m₂) : GLw a w × GLw (n - a) w) = (m₁, 1) * (1, m₂) := by ext <;> simp
    rw [e, map_mul]
    exact N.mul_mem hm₁.1.2 hm₂.1.2
  · intro m₁ hm₁ m₂ hm₂
    have h1 : μ (GeneralLinearGroup.det m₁) = 1 := hm₁.2
    have h2 : μ (GeneralLinearGroup.det m₂) = 1 := hm₂.2
    rw [map_mul, map_pow, map_pow, h1, h2, one_pow, one_pow, mul_one]

end GlobalTheory.BCT.SplitLevels
