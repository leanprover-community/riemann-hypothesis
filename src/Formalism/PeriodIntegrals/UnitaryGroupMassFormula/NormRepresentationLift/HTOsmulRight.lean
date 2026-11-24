module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.CoeCj
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.ActsByFrameAct
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

noncomputable section

open scoped Classical

namespace PI.NRL

open NumberField IsDedekindDomain Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem hT_osmul_left (a : 𝓞 E) (y w : S.V) : S.hT (a • y) w = star (a : E) * S.hT y w := by
  rw [← smul_coe, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]

theorem hT_osmul_right (a : 𝓞 E) (y w : S.V) : S.hT y (a • w) = (a : E) * S.hT y w := by
  rw [← smul_coe, map_smul, smul_eq_mul]

theorem hT_cj_left (a : 𝓞 E) (y w : S.V) : S.hT (cj a • y) w = (a : E) * S.hT y w := by
  rw [hT_osmul_left, coe_cj, star_star]

section Prime

variable (Λ : Submodule (𝓞 E) S.V) (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (hint : IntLat Λ)
  (e : Fin r → S.V) (hind : LinearIndependent E e) (he : ∀ i, e i ∈ Λ) (P : HeightOneSpectrum (𝓞 E))
  (hloc : ∀ x ∈ Λ, x ∈ Submodule.span E (Set.range e) →
    ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Submodule.span (𝓞 E) (Set.range e))

include hU hind hloc in
theorem coeff_mem_P (α : Fin r → 𝓞 E)
    (hα : ∀ y ∈ Λ, ∃ o ∈ P.asIdeal, S.hT y (∑ i, α i • e i) = (o : E)) : ∀ i, α i ∈ P.asIdeal := by
  obtain ⟨β, hβ1, hβ2⟩ := exists_beta P
  set x := ∑ i, α i • e i with hx
  have hxE : x = ∑ i, (α i : E) • e i := by simp only [hx, smul_coe]
  have hβx : β • x ∈ Λ := by
    rw [← hU]
    refine (Submodule.mem_iInf _).mpr fun y => (Submodule.mem_iInf _).mpr fun hy => ?_
    obtain ⟨o, ho, hxo⟩ := hα y hy
    obtain ⟨o', ho'⟩ := hβ1 o ho
    show S.hT y (β • x) ∈ (1 : Submodule (𝓞 E) E)
    rw [map_smul, smul_eq_mul, hxo, ho']
    exact Submodule.mem_one.mpr ⟨o', rfl⟩
  have hβxE : β • x ∈ Submodule.span E (Set.range e) := by
    refine Submodule.smul_mem _ _ ?_
    rw [hxE]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨s, hs, hsx⟩ := hloc _ hβx hβxE
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mp hsx
  have hcoef : ∀ i, (c i : E) = (s : E) * β * (α i : E) := by
    have h1 : ∑ i, (c i : E) • e i = ∑ i, ((s : E) * β * (α i : E)) • e i := by
      have : s • β • x = ∑ i, ((s : E) * β * (α i : E)) • e i := by
        rw [← smul_coe, hxE, Finset.smul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, smul_smul]
      rw [← this, ← hc]
      simp only [smul_coe]
    intro i
    have := (Fintype.linearIndependent_iff.mp hind) (fun i => (c i : E) - (s : E) * β * (α i : E))
      (by simp only [sub_smul, Finset.sum_sub_distrib, h1, sub_self]) i
    exact sub_eq_zero.mp this
  intro i
  by_contra hi
  have hsα : s * α i ∉ P.asIdeal := fun h => (P.isPrime.mem_or_mem h).elim hs hi
  exact hβ2 (s * α i) hsα (c i) (by rw [hcoef]; push_cast; ring)

end Prime

end PI.NRL
