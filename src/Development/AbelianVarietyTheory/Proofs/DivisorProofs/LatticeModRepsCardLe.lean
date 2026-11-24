module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem lattice_mod_reps_card_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ)
    (Λ : Submodule (𝓞 E) (Fin r → E)), 1 ≤ M → Λ.FG → ∃ T : Finset (Fin r → E),
    T.card ≤ M ^ (2 * fdeg E * r) ∧ (∀ t ∈ T, t ∈ Λ) ∧ ∀ x ∈ Λ, ∃ t ∈ T, ∃ y ∈ Λ, x = t + M • y := by
  intro E _ _ _ r M Λ hM hfg
  classical
  let L : Submodule ℤ (Fin r → E) := Λ.restrictScalars ℤ
  have hLfg : L.FG := hfg.restrictScalars
  haveI : Module.Finite ℤ L := Module.Finite.iff_fg.mpr hLfg
  haveI : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex ℤ L
  let b := Module.Free.chooseBasis ℤ L
  have hli : LinearIndependent ℤ (fun i => (b i : Fin r → E)) :=
    b.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hliQ : LinearIndependent ℚ (fun i => (b i : Fin r → E)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp hli
  have hcard : Fintype.card ι ≤ Module.finrank ℚ (Fin r → E) := hliQ.fintype_card_le_finrank
  have hfr : Module.finrank ℚ (Fin r → E) = r * Module.finrank ℚ E := by
    simp [Module.finrank_pi_fintype]
  have heven : Module.finrank ℚ E = 2 * fdeg E := by
    rw [fdeg, IsTotallyComplex.finrank E]; omega
  have hn : Fintype.card ι ≤ 2 * fdeg E * r := by
    rw [hfr, heven] at hcard; linarith [Nat.mul_comm r (2 * fdeg E)]
  have hMpos : (0 : ℤ) < M := by exact_mod_cast hM
  let f : (ι → Fin M) → (Fin r → E) := fun c => ((∑ i, ((c i : ℕ) : ℤ) • b i : L) : Fin r → E)
  refine ⟨Finset.univ.image f, ?_, ?_, ?_⟩
  · calc (Finset.univ.image f).card ≤ (Finset.univ : Finset (ι → Fin M)).card :=
          Finset.card_image_le
      _ = M ^ Fintype.card ι := by simp
      _ ≤ M ^ (2 * fdeg E * r) := Nat.pow_le_pow_right hM hn
  · intro t ht
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp ht
    exact (∑ i, ((c i : ℕ) : ℤ) • b i : L).2
  · intro x hx
    let xl : L := ⟨x, hx⟩
    let k := b.repr xl
    let c : ι → Fin M := fun i => ⟨(k i % M).toNat, by
      have := Int.emod_nonneg (k i) hMpos.ne'
      have := Int.emod_lt_of_pos (k i) hMpos
      omega⟩
    refine ⟨f c, Finset.mem_image_of_mem _ (Finset.mem_univ _),
      ((∑ i, (k i / M) • b i : L) : Fin r → E), (∑ i, (k i / M) • b i : L).2, ?_⟩
    have hsum : xl = ∑ i, ((c i : ℕ) : ℤ) • b i + (M : ℤ) • ∑ i, (k i / M) • b i := by
      conv_lhs => rw [← b.sum_repr xl]
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← add_smul]
      congr 1
      show k i = ((k i % M).toNat : ℤ) + M * (k i / M)
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hMpos.ne')]
      linarith [Int.mul_ediv_add_emod (k i) (M : ℤ)]
    have h2 := congrArg Subtype.val hsum
    calc x = (xl : Fin r → E) := rfl
      _ = _ := h2
      _ = f c + M • ((∑ i, (k i / M) • b i : L) : Fin r → E) := by
        rw [Submodule.coe_add, Submodule.coe_smul, natCast_zsmul]

end GlobalTheory
