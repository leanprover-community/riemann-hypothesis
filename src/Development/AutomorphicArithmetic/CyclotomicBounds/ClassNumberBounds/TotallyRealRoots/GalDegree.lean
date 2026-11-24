module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalDefs
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalRoots
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

variable {E : Type*} [Field E]

private theorem mem_fixingSubgroup_adjoinRoots (m : ℕ) (g : Gal(AlgebraicClosure E/E)) :
    g ∈ (adjoinRoots E m).fixingSubgroup ↔ ∀ ζ : AlgebraicClosure E, ζ ^ m = 1 → g ζ = ζ := by
  constructor
  · intro hg ζ hζ
    exact (IntermediateField.mem_fixingSubgroup_iff _ g).1 hg ζ
      (IntermediateField.subset_adjoin E _ hζ)
  · intro h
    have hle : adjoinRoots E m ≤ IntermediateField.fixedField (Subgroup.zpowers g) := by
      refine IntermediateField.adjoin_le_iff.2 ?_
      intro ζ hζ
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      have : Subgroup.zpowers g ≤ MulAction.stabilizer Gal(AlgebraicClosure E/E) ζ := by
        rw [Subgroup.zpowers_le]
        exact h ζ hζ
      exact fun f hf => this hf
    exact (IntermediateField.le_iff_le _ _).1 hle (Subgroup.mem_zpowers g)

private theorem comap_princ_eq [CharZero E] (n : ℕ) :
    (princ l n).comap (eps l E) = (adjoinRoots E (l ^ n)).fixingSubgroup := by
  ext g
  rw [Subgroup.mem_comap, eps_mem_princ_iff, mem_fixingSubgroup_adjoinRoots]

theorem card_map_redPow_galImage [CharZero E] (n : ℕ) :
    Nat.card ((galImage l E).map (redPow l n)) = Module.finrank E (adjoinRoots E (l ^ n)) := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, ← comap_princ_eq, princ,
    MonoidHom.comap_ker, Subgroup.index_ker, galImage, MonoidHom.map_range]

end KStar.TotallyRealRoots
