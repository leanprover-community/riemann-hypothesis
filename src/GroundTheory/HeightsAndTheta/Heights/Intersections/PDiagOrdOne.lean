module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.AtPrime.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace DiagonalOrderOne

section Length

variable {A : Type*} [CommRing A]

theorem length_eq_one_of_sat (J W : Ideal A) [W.IsPrime] (hJ : J ≤ W) (hs : ∀ d ∈ W, ∃ u ∉ W, u * d ∈ J) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) = 1 := by
  have hz : ∀ (r : A) (s : W.primeCompl),
      LocalizedModule.mk (Ideal.Quotient.mk J r) s = 0 ↔ r ∈ W := by
    intro r s
    rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
    constructor
    · rintro ⟨u, hu⟩
      rw [smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def, Algebra.smul_def, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hu
      rcases ‹W.IsPrime›.mem_or_mem (hJ hu) with h | h
      · exact absurd h u.2
      rcases ‹W.IsPrime›.mem_or_mem h with h | h
      · exact absurd h s.2
      · exact h
    · intro hr
      obtain ⟨u, hu, hud⟩ := hs r hr
      refine ⟨⟨u, hu⟩, ?_⟩
      rw [smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def, Algebra.smul_def, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      have e : u * ((s : A) * r) = u * r * s := by ring
      rw [show ((⟨u, hu⟩ : W.primeCompl) : A) = u from rfl, e]
      exact J.mul_mem_right _ hud
  have hgen : ∀ (q : A) (t : W.primeCompl) (r : A) (s : W.primeCompl) (hr : r ∉ W),
      LocalizedModule.mk (Ideal.Quotient.mk J q) t =
        Localization.mk (q * s) (t * ⟨r, hr⟩) • LocalizedModule.mk (Ideal.Quotient.mk J r) s := by
    intro q t r s hr
    rw [LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      ← map_mul]
    congr 1
    ring
  have h1 : LocalizedModule.mk (Ideal.Quotient.mk J 1) (1 : W.primeCompl) ≠ 0 :=
    fun h => ‹W.IsPrime›.ne_top ((Ideal.eq_top_iff_one W).2 ((hz 1 1).1 h))
  have : Nontrivial (LocalizedModule W.primeCompl (A ⧸ J)) := ⟨⟨_, 0, h1⟩⟩
  rw [Module.length_eq_one_iff, isSimpleModule_iff]
  refine { eq_bot_or_eq_top := fun N => ?_ }
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  obtain ⟨n, hnN, hn0⟩ := (Submodule.ne_bot_iff N).1 hN
  induction n using LocalizedModule.induction_on with
  | h m s =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
    have hr : r ∉ W := fun h => hn0 ((hz r s).2 h)
    rw [eq_top_iff]
    intro y _
    induction y using LocalizedModule.induction_on with
    | h m' t =>
      obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective m'
      rw [hgen q t r s hr]
      exact N.smul_mem _ hnN

end Length


variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]


end DiagonalOrderOne


end

end GroundTheory.Heights₂.Heights.Inter
