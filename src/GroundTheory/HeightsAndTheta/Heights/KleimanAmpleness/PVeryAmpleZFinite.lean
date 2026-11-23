module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleZFiniteSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsVeryAmpleZFinite
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u v w

namespace VeryAmpleZFinite

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {r : ℕ}

theorem ampleBase_le_chartRing {h : Fin (r + 1) → Ω} (J : Chart h) {j : Fin (r + 1)} (hj : j ∈ J.1) :
    ampleBase (S := S) h j ≤ chartRing S h J := by
  rw [ampleBase, Algebra.adjoin_le_iff]
  rintro _ ⟨l, rfl⟩
  exact ⟨MvPolynomial.X l, MvPolynomial.X j, 1, X_mem_monos hj, MvPolynomial.isHomogeneous_X S l,
    MvPolynomial.isHomogeneous_X S j, by simp⟩

end VeryAmpleZFinite


open VeryAmpleZFinite in
theorem VeryAmpleZFinite.proof (hExt : VeryAmpleZExtend.Statement.{u, v, w})
    (hSpan : VeryAmpleZChartSpan.Statement.{u, v, w}) (hRing : VeryAmpleZChartRing.Statement.{u, w}) :
    VeryAmpleZFinite.Statement.{u, v, w} := by
  classical
  intro S _ _ Ω _ _ N x E _ _ _ _ F hF H r h hH J
  obtain ⟨j, hj⟩ := J.2.1
  have hj0 : h j ≠ 0 := (mem_support h).mp (J.2.2 hj)
  have hsec : ∀ l, h l ∈ H.toSubSystem.secs := hH.mem_secs
  obtain ⟨n, a, b, Jk, ha, hb, hab, hrat⟩ := hH.affine j hj0
  have hA : ∀ z ∈ ampleRing H.toSubSystem 1 (h j), z ∈ chartRing S h J := fun z hz =>
    ampleBase_le_chartRing J hj (hH.closed j hj0 hz)
  choose g hg using fun k => hF (Jk k)

  have hext : ∀ k, ∀ᶠ M in atTop, ∀ y ∈ g k, b k ^ M • y ∈ secsOnZ F.toSubSystem H.toSubSystem h J :=
    fun k => (eventually_all_finset _).mpr fun y hy =>
      hExt S Ω N x E F H.toSubSystem r h hsec J j hj (b k) (hb k) (Jk k) (hrat k) y
        (by rw [← hg k]; exact Submodule.subset_span hy)
  choose M0 hM0 using fun k => eventually_atTop.mp (hext k)
  set T : Finset E := Finset.univ.biUnion fun k => (g k).image fun y => b k ^ M0 k • y with hT
  have hTmem : ∀ k, ∀ y ∈ g k, b k ^ M0 k • y ∈ T := fun k y hy =>
    Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_image.mpr ⟨y, hy, rfl⟩⟩
  refine ⟨T, fun z hz => ?_, fun e he => ?_⟩
  · obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hk
    exact hM0 k (M0 k) le_rfl y hy
  rw [Submodule.restrictScalars_mem]

  have hloc : ∀ k, ∀ᶠ L in atTop, b k ^ L • e ∈ Submodule.span (chartRing S h J) (T : Set E) := by
    intro k
    have heK : e ∈ secsOnZChart F.toSubSystem H.toSubSystem h (Jk k) J :=
      (Submodule.mem_iInf _).mp he (Jk k)
    obtain ⟨β, hβ, rfl⟩ := hSpan S Ω N x E F.toSubSystem H.toSubSystem r h hsec (Jk k) J (g k)
      (hg k).ge _ heK
    obtain ⟨L0, hL0⟩ := eventually_atTop.mp ((eventually_all_finset (g k)).mpr fun y hy =>
      hRing S Ω N x H r h hH J j hj (b k) (hb k) (Jk k) (hrat k) (β y) (hβ y hy))
    refine eventually_atTop.mpr ⟨L0 + M0 k, fun L hL => ?_⟩
    rw [Finset.smul_sum]
    refine Submodule.sum_mem _ fun y hy => ?_
    have hmem : b k ^ (L - M0 k) * β y ∈ chartRing S h J := hL0 _ (by omega) y hy
    have e1 : b k ^ L • (β y • y) = (⟨_, hmem⟩ : chartRing S h J) • (b k ^ M0 k • y) := by
      rw [Subalgebra.smul_def, smul_smul, smul_smul]
      congr 1
      change b k ^ L * β y = b k ^ (L - M0 k) * β y * b k ^ M0 k
      rw [mul_comm _ (b k ^ M0 k), ← mul_assoc, ← pow_add, Nat.add_sub_cancel' (by omega)]
    rw [e1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hTmem k y hy))

  choose L hL using fun k => eventually_atTop.mp (hloc k)
  set L' := Finset.univ.sup L
  let bA : Fin n → chartRing S h J := fun k => ⟨b k, hA _ (hb k)⟩
  have htop : Ideal.span (Set.range bA) = ⊤ := by
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]
    refine ⟨fun k => ⟨a k, hA _ (ha k)⟩, Subtype.ext ?_⟩
    rw [AddSubmonoidClass.coe_finsetSum, OneMemClass.coe_one]
    exact hab
  have h1 : (1 : chartRing S h J) ∈ Ideal.span (Set.range fun k => bA k ^ L') := by
    have := Ideal.span_pow_eq_top _ htop L'
    rw [← Set.range_comp] at this
    rw [← Ideal.eq_top_iff_one]
    exact this
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp h1
  have he' : e = ∑ k, c k • (b k ^ L' • e) := by
    have : ∑ k, c k • (b k ^ L' • e) = (∑ k, c k * bA k ^ L') • e := by
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_smul]
      simp [bA]
    rw [this, hc, one_smul]
  rw [he']
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (hL k L' (Finset.le_sup (Finset.mem_univ k)))

end

end GroundTheory.Heights₂.Heights.Kleiman
