module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIdealIsPrime
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatVal

variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

theorem f_mem_IB : f ξ ∈ Lat.IB f ξ := Ideal.subset_span (Set.mem_singleton _)

theorem η_mem_IB : Lat.η f ξ l M ∈ Lat.IB f ξ := by
  unfold Lat.η
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ (f_mem_IB f ξ)

theorem dpE_succ_mem_IB (i : ℕ) : Lat.dpE f ξ l M (i + 1) ∈ Lat.IB f ξ := by
  unfold Lat.dpE
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (η_mem_IB f ξ l M) _ (Nat.succ_pos i))

theorem dpE_zero_eq : Lat.dpE f ξ l M 0 = 1 := by simp [Lat.dpE]

theorem exists_rep_B (x : B) (hx : x ∈ Lat.sub f ξ l M) : ∃ a : W, x - f a ∈ Lat.IB f ξ := by
  apply GlobalTheory.CompanionTheory.LatPrime.exists_sub_mem_IB <;> assumption

theorem exists_rep (x : Lat.A f ξ l M) : ∃ a : W, Lat.ι f ξ l M x - f a ∈ Lat.IB f ξ :=
  exists_rep_B f ξ l M _ x.2

theorem mem_of_dvd {a b : W} {x y : Lat.A f ξ l M}
    (hx : Lat.ι f ξ l M x - f a ∈ Lat.IB f ξ) (hy : Lat.ι f ξ l M y - f b ∈ Lat.IB f ξ)
    (h : Ideal.Quotient.mk (Ideal.span {ξ}) a ∣ Ideal.Quotient.mk (Ideal.span {ξ}) b) :
    y ∈ Ideal.span {x} ⊔ Lat.I f ξ l M := by
  obtain ⟨c', hc⟩ := h
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c'
  rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hc
  obtain ⟨d, hd⟩ := hc
  have hI : y - Lat.ofW f ξ l M c * x ∈ Lat.I f ξ l M := by
    show Lat.ι f ξ l M (y - Lat.ofW f ξ l M c * x) ∈ Lat.IB f ξ
    have h1 : f (b - a * c) ∈ Lat.IB f ξ := by
      rw [hd, map_mul]; exact Ideal.mul_mem_right _ _ (f_mem_IB f ξ)
    have h2 := Ideal.add_mem _ (Ideal.sub_mem _ hy (Ideal.mul_mem_left _ (f c) hx)) h1
    have e : Lat.ι f ξ l M (y - Lat.ofW f ξ l M c * x)
        = Lat.ι f ξ l M y - f b - f c * (Lat.ι f ξ l M x - f a) + f (b - a * c) := by
      rw [map_sub, map_mul, Lat.ι_ofW, map_sub, map_mul]; ring
    rw [e]; exact h2
  have hs : Lat.ofW f ξ l M c * x ∈ Ideal.span {x} :=
    Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
  have e : y = Lat.ofW f ξ l M c * x + (y - Lat.ofW f ξ l M c * x) := by ring
  rw [e]
  exact Submodule.add_mem_sup hs hI

theorem val : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ),
    Lat.Hyp f ξ l m → ∀ x y : Lat.A f ξ l M,
      x ∈ Ideal.span {y} ⊔ Lat.I f ξ l M ∨ y ∈ Ideal.span {x} ⊔ Lat.I f ξ l M := by
  intro W B _ _ _ f ξ l M m h x y
  obtain ⟨a, ha⟩ := exists_rep f ξ l M x
  obtain ⟨b, hb⟩ := exists_rep f ξ l M y
  rcases h.val (Ideal.Quotient.mk _ a) (Ideal.Quotient.mk _ b) with hd | hd
  · exact Or.inr (mem_of_dvd f ξ l M ha hb hd)
  · exact Or.inl (mem_of_dvd f ξ l M hb ha hd)

end GlobalTheory.CompanionTheory.LatVal
