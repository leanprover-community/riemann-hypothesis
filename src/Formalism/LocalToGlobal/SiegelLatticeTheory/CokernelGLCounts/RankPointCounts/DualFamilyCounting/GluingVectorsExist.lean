module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandSt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsGlueDataPre
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CardFilterLtInj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsPrescFamily
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsTotPosCongr
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.InPOfMemPow
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem gluing_vectors_exist : GlueVecsPre := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc
  have := h𝔭.isPrime
  have hne : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField F)
  set W := orthK h U with hW
  set m := finrank K W with hm
  set P : Finset (Fin (finrank K U)) := Finset.univ.filter (fun i => vF 𝔭 (a i) ≠ 0) with hP
  have hPc : P.card < m := hc
  have hPm : ∀ i, (P.filter (· < i)).card < m := fun i =>
    lt_of_le_of_lt (Finset.card_filter_le _ _) hPc
  let τ : Fin (finrank K U) → Fin m := fun i => ⟨(P.filter (· < i)).card, hPm i⟩
  have hτ : ∀ i k, vF 𝔭 (a i) ≠ 0 → vF 𝔭 (a k) ≠ 0 → τ i = τ k → i = k := by
    intro i k hi hk e
    exact card_filter_lt_inj P (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩) (congrArg Fin.val e)
  have hτl : ∀ i, vF 𝔭 (a i) ≠ 0 → (τ i : ℕ) + 1 < m := by
    intro i hi
    have := card_filter_lt_lt P (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
    show (P.filter (· < i)).card + 1 < m
    omega
  choose nF hnpos hncong using fun i => exists_totPos_congr (K := K) h𝔭 hne (a i) (2 * vF 𝔭 (a i))
  let t : Fin m → K := fun j =>
    if hj : ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j then algebraMap F K (nF hj.choose) else 1
  have hts : ∀ j, star (t j) = t j := by
    intro j; simp only [t]; split_ifs
    · exact star_fix hF _
    · exact star_one K
  have htp : ∀ j, TotPos (t j) := by
    intro j; simp only [t]; split_ifs
    · exact hnpos _
    · intro φ; rw [map_one]; simp
  have htpart : ∀ i, vF 𝔭 (a i) ≠ 0 → t (τ i) = algebraMap F K (nF i) := by
    intro i hi
    have hj : ∃ i', vF 𝔭 (a i') ≠ 0 ∧ τ i' = τ i := ⟨i, hi, rfl⟩
    simp only [t, dif_pos hj]
    rw [hτ _ _ hj.choose_spec.1 hi hj.choose_spec.2]
  have htnp : ∀ j, (∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ j) → t j = 1 := by
    intro j hj
    have : ¬ ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j := fun ⟨i, hi, e⟩ => hj i hi e
    simp only [t, dif_neg this]
  let h' : W →ₗ⋆[K] W →ₗ[K] K := (LinearMap.lcomp K K W.subtype).comp (h.comp W.subtype)
  have h'a : ∀ x y : W, h' x y = h x y := fun x y => rfl
  have hsym' : ∀ x y : W, star (h' x y) = h' y x := by
    intro x y; rw [h'a, h'a, ← starRingEnd_apply]; exact hs.eq _ _
  have hpos' : ∀ x : W, x ≠ 0 → TotPos (h' x x) := by
    intro x hx φ; rw [h'a]; exact hpos x x.2 (fun e => hx (Subtype.ext e)) φ
  have hm1 : m - 1 + 1 = m := by omega
  obtain ⟨v, ho, hv1, hvl⟩ := exists_presc_family hK h' hsym' hpos' (m - 1) (by omega)
    (fun j => t (Fin.cast hm1 j)) (fun j => hts _) (fun j => htp _)
  let w : Fin m → V := fun j => (v (Fin.cast hm1.symm j) : V)
  have hwo : ∀ j k, j ≠ k → h (w j) (w k) = 0 := by
    intro j k hjk
    exact ho _ _ (fun e => hjk (Fin.ext (by have := congrArg Fin.val e; simpa using this)))
  have hwn : ∀ j : Fin m, (j : ℕ) + 1 < m → h (w j) (w j) = t j := by
    intro j hj
    have hne' : Fin.cast hm1.symm j ≠ Fin.last (m - 1) := by
      intro e; have := congrArg Fin.val e; simp at this; omega
    have := hv1 _ hne'
    simpa [w, h'a] using this
  have hwn0 : ∀ j, h (w j) (w j) ≠ 0 := by
    intro j
    by_cases hj : (j : ℕ) + 1 < m
    · rw [hwn j hj]; exact TotPos.ne_zero' (htp j)
    · have hjl := j.isLt
      have hl : Fin.cast hm1.symm j = Fin.last (m - 1) := by
        ext; simp; omega
      have : v (Fin.cast hm1.symm j) ≠ 0 := by rw [hl]; exact hvl
      exact TotPos.ne_zero' (hpos' _ this)
  have hfix : ∀ j, ∃ x : F, h (w j) (w j) = algebraMap F K x := fun j => by
    obtain ⟨x, hx⟩ := (hF _).1 (by rw [← starRingEnd_apply]; exact hs.eq (w j) (w j))
    exact ⟨x, hx.symm⟩
  choose c hcw using hfix
  obtain ⟨π, s₀, hu⟩ := exists_isUnif0 h𝔭
  refine ⟨π, w, c, τ, fun j => (v _).2, hwo,
    fun j => ⟨hcw j, fun h0 => hwn0 j (by rw [hcw j, h0, map_zero])⟩, hτ, ⟨s₀, hu⟩, ?_, hτl, ?_⟩
  · intro i hi
    have e : algebraMap F K (c (τ i)) = algebraMap F K (nF i) := by
      rw [← hcw, hwn _ (hτl i hi), htpart i hi]
    rw [(algebraMap F K).injective e]
    exact hncong i
  · intro j hj hnp
    have e : c j = 1 := by
      apply (algebraMap F K).injective
      rw [← hcw, hwn j hj, htnp j hnp, map_one]
    rw [e, inv_one, map_one]
    exact ⟨(SP K 𝔭).one_mem, (SP K 𝔭).one_mem⟩

end Formalism.L2.SG.Pf.GluingBases
