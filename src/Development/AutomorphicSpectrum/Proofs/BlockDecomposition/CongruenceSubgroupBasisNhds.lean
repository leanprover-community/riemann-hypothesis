module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCongruenceSubset
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.CongruenceBasis

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_unif_lt_one : valuation k (algebraMap 𝒪[k] k (Zls.unif k)) < 1 := by
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 Zls.irreducible_unif.not_isUnit

theorem val_le_val_unif (x : k) (hx : valuation k x < 1) :
    valuation k x ≤ valuation k (algebraMap 𝒪[k] k (Zls.unif k)) := by
  let y : 𝒪[k] := ⟨x, hx.le⟩
  have hy : ¬ IsUnit y :=
    Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 hx
  have hmem : y ∈ IsLocalRing.maximalIdeal 𝒪[k] := hy
  rw [Zls.irreducible_unif.maximalIdeal_eq, Ideal.mem_span_singleton'] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hx' : x = algebraMap 𝒪[k] k c * algebraMap 𝒪[k] k (Zls.unif k) := by
    rw [← map_mul, hc]; rfl
  rw [hx', map_mul]
  exact mul_le_of_le_one_left' c.2

theorem val_sub_one_le_of_mem_Km {N m : ℕ} {g : GL (Fin N) k} (hg : g ∈ Zls.Km k N m) (i j : Fin N) :
    valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
      valuation k (algebraMap 𝒪[k] k (Zls.unif k) ^ m) := by
  obtain ⟨h, hker, rfl⟩ := Subgroup.mem_map.1 hg
  have h1 := congrArg (fun u : GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) =>
    u.1 i j) (MonoidHom.mem_ker.1 hker)
  have h2 : (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m}))
      ((h : Matrix (Fin N) (Fin N) 𝒪[k]) i j - (1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j) = 0 := by
    rw [map_sub, sub_eq_zero]
    simpa [Matrix.one_apply, apply_ite] using h1
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h2
  obtain ⟨c, hc⟩ := h2
  have h3 : ((Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) h : GL (Fin N) k) :
        Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j =
      algebraMap 𝒪[k] k c * algebraMap 𝒪[k] k (Zls.unif k) ^ m := by
    rw [← map_pow, ← map_mul, hc, map_sub]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  rw [h3, map_mul]
  exact mul_le_of_le_one_left' c.2

theorem exists_Km_subset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (U : Set (GL (Fin N) k)), IsOpen U →
    (1 : GL (Fin N) k) ∈ U → ∃ m : ℕ, 1 ≤ m ∧ (Zls.Km k N m : Set (GL (Fin N) k)) ⊆ U := by
  intro k _ _ _ _ N U hU h1
  have hne : algebraMap 𝒪[k] k (Zls.unif k) ≠ 0 :=
    (map_ne_zero_iff (algebraMap 𝒪[k] k) (IsFractionRing.injective 𝒪[k] k)).2
      Zls.irreducible_unif.ne_zero
  obtain ⟨m, hm, hsub⟩ := exists_congruence_subset k N (algebraMap 𝒪[k] k (Zls.unif k)) hne
    val_unif_lt_one val_le_val_unif U (hU.mem_nhds h1)
  exact ⟨m, hm, fun g hg => hsub fun i j => val_sub_one_le_of_mem_Km hg i j⟩

end GlobalTheory.CompanionTheory.CongruenceBasis
