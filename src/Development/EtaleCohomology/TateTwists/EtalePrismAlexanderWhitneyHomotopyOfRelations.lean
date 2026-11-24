module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.EtaleCohomology.TateTwists.PrismAlexanderWhitneySwapChainHomotopy, Development.EtaleCohomology.TateTwists.EtalePrismAlexanderWhitneyHomotopyOfRelations

-- ===== clump member: Development.EtaleCohomology.TateTwists.PrismAlexanderWhitneySwapChainHomotopy =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.PrismAlexanderWhitneySwapChainHomotopy", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.PrismAlexanderWhitneySwapChainHomotopy : Prop :=
  ∃ h : ∀ N, Pr N →₀ ℤ, (∀ N, Pr.Deg (N + 1) (h N)) ∧ Pr.d 0 (h 0) = Pr.aw 0 - Pr.wa 0 ∧ ∀ N, Pr.d (N + 1) (h (N + 1)) + Pr.bd (h N) = Pr.aw (N + 1) - Pr.wa (N + 1)
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.PrismAlexanderWhitneySwapChainHomotopy =====

-- ===== clump member: Development.EtaleCohomology.TateTwists.EtalePrismAlexanderWhitneyHomotopyOfRelations =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.EtalePrismAlexanderWhitneyHomotopyOfRelations", "h": "module\n\npublic import Development.EtaleCohomology.TateTwists.PrismAlexanderWhitneySwapChainHomotopy\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.SteenPf

def leaf_acyc : Prop := ∀ (N k : ℕ) (c : Pr N →₀ ℤ), Pr.Deg (k + 1) c → Pr.d N c = 0 →
  ∃ b : Pr N →₀ ℤ, Pr.Deg (k + 2) b ∧ Pr.d N b = c

def leaf_dbd : Prop := ∀ (N : ℕ) (c : Pr N →₀ ℤ), Pr.d (N + 1) (Pr.bd c) = Pr.bd (Pr.d N c)

def leaf_bdbd : Prop := ∀ (N : ℕ) (c : Pr N →₀ ℤ), Pr.bd (Pr.bd c) = 0

def leaf_aw : Prop := ∀ N : ℕ, Pr.d (N + 1) (Pr.aw (N + 1)) = Pr.bd (Pr.aw N)

def leaf_wa : Prop := ∀ N : ℕ, Pr.d (N + 1) (Pr.wa (N + 1)) = Pr.bd (Pr.wa N)

lemma deg_zero {N k : ℕ} : Pr.Deg k (0 : Pr N →₀ ℤ) := by
  intro z hz; simp at hz

lemma deg_sub {N k : ℕ} {a b : Pr N →₀ ℤ} (ha : Pr.Deg k a) (hb : Pr.Deg k b) : Pr.Deg k (a - b) := by
  intro z hz
  rcases Finset.mem_union.1 (Finsupp.support_sub hz) with h | h
  · exact ha z h
  · exact hb z h

lemma deg_bd {N k : ℕ} {c : Pr N →₀ ℤ} (hc : Pr.Deg k c) : Pr.Deg k (Pr.bd c) := by
  intro z hz
  unfold Pr.bd at hz
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hz)
  have h2 := Finsupp.support_smul hi
  unfold Pr.push at h2
  simp only [Finsupp.lmapDomain_apply] at h2
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support h2)
  exact hc w hw

lemma deg_aw (N : ℕ) : Pr.Deg N (Pr.aw N) := by
  intro z hz
  unfold Pr.aw at hz
  obtain ⟨p, -, hp⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hz)
  have := Finsupp.support_single_subset hp
  rw [Finset.mem_singleton] at this
  subst this
  have := p.isLt
  show (p : ℕ) + (N - p) = N
  omega

lemma deg_wa (N : ℕ) : Pr.Deg N (Pr.wa N) := by
  intro z hz
  unfold Pr.wa at hz
  obtain ⟨p, -, hp⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hz)
  have := Finsupp.support_single_subset hp
  rw [Finset.mem_singleton] at this
  subst this
  have := p.isLt
  show (N - p) + (p : ℕ) = N
  omega

lemma bd_sub {N : ℕ} (a b : Pr N →₀ ℤ) : Pr.bd (a - b) = Pr.bd a - Pr.bd b := by
  unfold Pr.bd
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sub, smul_sub]

lemma bd_zero {N : ℕ} : Pr.bd (0 : Pr N →₀ ℤ) = 0 := by
  simpa using bd_sub (0 : Pr N →₀ ℤ) 0

lemma aw_zero_eq : Pr.aw 0 = Pr.wa 0 := by
  simp [Pr.aw, Pr.wa]

def Good (N : ℕ) (x : Pr N →₀ ℤ) : Prop :=
  Pr.Deg (N + 1) x ∧ Pr.bd (Pr.aw N - Pr.wa N - Pr.d N x) = 0

lemma step (hA : leaf_acyc) (hD : leaf_dbd) (hB : leaf_bdbd) (hAW : leaf_aw) (hWA : leaf_wa)
    (N : ℕ) (x : Pr N →₀ ℤ) (hx : Good N x) :
    ∃ y : Pr (N + 1) →₀ ℤ, Good (N + 1) y ∧ Pr.d (N + 1) y + Pr.bd x = Pr.aw (N + 1) - Pr.wa (N + 1) := by
  set c := Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.bd x with hcdef
  have hcdeg : Pr.Deg (N + 1) c := deg_sub (deg_sub (deg_aw _) (deg_wa _)) (deg_bd hx.1)
  have hcyc : Pr.d (N + 1) c = 0 := by
    rw [hcdef, map_sub, map_sub, hAW, hWA, hD, ← bd_sub, ← bd_sub]
    exact hx.2
  obtain ⟨b, hbdeg, hb⟩ := hA (N + 1) N c hcdeg hcyc
  refine ⟨b, ⟨hbdeg, ?_⟩, ?_⟩
  · have : Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.d (N + 1) b = Pr.bd x := by
      rw [hb, hcdef]; abel
    rw [this]; exact hB N x
  · rw [hb, hcdef]; abel

lemma good_zero : Good 0 0 := by
  refine ⟨deg_zero, ?_⟩
  rw [aw_zero_eq, map_zero, sub_self, sub_zero, bd_zero]

end LateralTheory.EtaleFoundations.SteenPf

open LateralTheory.EtaleFoundations.SteenPf in
theorem LateralTheory.EtaleFoundations.etale_prism_alexander_whitney_homotopy_of_relations (hA : leaf_acyc) (hD : leaf_dbd) (hB : leaf_bdbd)
    (hAW : leaf_aw) (hWA : leaf_wa) : LateralTheory.EtaleFoundations.PrismAlexanderWhitneySwapChainHomotopy := by
  classical
  let seq : ∀ N, {x : Pr N →₀ ℤ // Good N x} := fun N =>
    Nat.rec (motive := fun N => {x : Pr N →₀ ℤ // Good N x}) ⟨0, good_zero⟩
      (fun N x => ⟨Classical.choose (step hA hD hB hAW hWA N x.1 x.2),
        (Classical.choose_spec (step hA hD hB hAW hWA N x.1 x.2)).1⟩) N
  refine ⟨fun N => (seq N).1, fun N => (seq N).2.1, ?_, fun N => ?_⟩
  · show Pr.d 0 0 = _
    rw [map_zero, aw_zero_eq, sub_self]
  · exact (Classical.choose_spec (step hA hD hB hAW hWA N (seq N).1 (seq N).2)).2
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.EtalePrismAlexanderWhitneyHomotopyOfRelations =====
