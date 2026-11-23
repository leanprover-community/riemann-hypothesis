module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EqIdempotentCutOfComplementKills
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MemPowSmulLe
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.maximal_ideal_image_kills :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ {Q : Type} [CommRing Q] [IsLocalRing Q] [IsNoetherianRing Q] (f : ResidueField O →+* Q) (φ : S.A →+* Q), (∀ a : O, φ (algebraMap O S.A a) = f (residue O a)) → (∀ y ∈ S.mB, φ (S.inc y) ∈ maximalIdeal Q) → (S.u.map φ).triM = ⊥ → (S.u.map φ).IsBar f → ∀ y ∈ S.mB, φ (S.inc y) = 0 := by
  intro l _ O _ _ _ _ F C₀ n hF hn S Q _ _ _ f φ hf hm htri hbar y hy
  have hK : (⨅ N : ℕ, maximalIdeal Q ^ N) = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal Q).ne_top
  rw [← Ideal.mem_bot, ← hK, Ideal.mem_iInf]
  intro N
  obtain ⟨M, hM⟩ := (cont_u hF hn S).2.2.2 0 N
  obtain ⟨z, hz, hyz⟩ := y.2 (M + 1)
  let zB : S.B := ⟨z, le_adicClosure _ hz⟩
  have hd : y - zB ∈ S.mB := by
    show (y : S.R) - z ∈ maximalIdeal S.R
    exact Ideal.pow_le_self (Nat.succ_ne_zero M) hyz
  have hzB : zB ∈ S.mB := by
    have := sub_mem hy hd
    simpa using this
  have hz0 : φ (S.inc zB) = 0 := by
    obtain ⟨c, hc⟩ := adjoin_image_in_residue_range S f φ hf htri hbar (S.inc zB) hz
    have h1 := hm zB hzB
    rw [← hc] at h1 ⊢
    by_cases h0 : c = 0
    · rw [h0, map_zero]
    · exact absurd ((IsUnit.mk0 c h0).map f) h1
  have hgr : S.inc (y - zB) ∈ S.gr 0 := by
    have h1 : (1 : S.A) ∈ S.gr 0 := Submodule.subset_span ⟨[], by simp, by simp⟩
    have h2 := Submodule.smul_mem _ (y - zB) h1
    rw [Algebra.smul_def, mul_one] at h2
    exact h2
  have ha := hM _ hgr (Ideal.pow_le_pow_right (Nat.le_succ M) hyz)
  have hle : S.mB ^ N ≤ (maximalIdeal Q ^ N).comap (φ.comp (S.inc : S.B →+* S.A)) :=
    le_trans (Ideal.pow_right_mono (fun b hb => hm b hb) N) (Ideal.le_comap_pow _ N)
  have key : φ (S.inc (y - zB)) ∈ maximalIdeal Q ^ N := by
    refine Submodule.smul_induction_on (p := fun a => φ a ∈ maximalIdeal Q ^ N) ha ?_ ?_
    · intro b hb x _
      rw [Algebra.smul_def, map_mul]
      exact Ideal.mul_mem_right _ _ (hle hb)
    · intro a b ha hb
      rw [map_add (f := _)]
      exact add_mem ha hb
  rwa [map_sub, map_sub, hz0, sub_zero] at key
