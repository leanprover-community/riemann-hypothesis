module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FullEnum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.IndexLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.MaxIndep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.TorsSat
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
import Mathlib.Tactic.Linter.HaveILetI
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

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.cokerTors :
    ∀ (ι : Type) (A b : ℕ) (L : Set (ι →₀ ℤ)), CardLe ι A → 1 ≤ b → (∀ x ∈ L, l1 x ≤ b) →
      TorsLe ((ι →₀ ℤ) ⧸ Submodule.span ℤ L) (b ^ A) := by
  intro ι A b L hι hb hL
  obtain ⟨hfin, hA⟩ := hι
  haveI : IsAddTorsionFree (ι →₀ ℤ) :=
    Function.Injective.isAddTorsionFree (Finsupp.coeFnAddHom : (ι →₀ ℤ) →+ (ι → ℤ))
      DFunLike.coe_injective
  obtain ⟨b₀, -, hb₀L, hb₀i, hb₀⟩ := maxIndep (ι →₀ ℤ) ∅ L (Set.empty_subset _)
    (linearIndepOn_empty _ _)
  obtain ⟨b₁, h01, hb₁s, hb₁i, hb₁⟩ := maxIndep (ι →₀ ℤ) b₀
    (b₀ ∪ Set.range fun k : ι => Finsupp.single k (1 : ℤ)) Set.subset_union_left hb₀i
  obtain ⟨v, hv, hvr⟩ := fullEnum ι b₁ hb₁i fun k => hb₁ _ (Or.inr ⟨k, rfl⟩)
  have hshort : ∀ i, l1 (v i) ≤ b := by
    intro i
    have hi : v i ∈ b₁ := hvr ▸ Set.mem_range_self i
    rcases hb₁s hi with h | ⟨k, hk⟩
    · exact hL _ (hb₀L h)
    · rw [← hk]
      unfold l1
      rw [Finsupp.sum_single_index (by simp)]
      simpa using hb
  have hc := indexLe ι v b hv hshort
  have ht := torsSat (ι →₀ ℤ) ι L v _ hv (fun x hx => by
    obtain ⟨n, hn, hnx⟩ := hb₀ x hx
    refine ⟨n, hn, Submodule.span_mono ?_ hnx⟩
    rw [hvr]
    exact Set.subset_inter h01 hb₀L) hc
  exact ⟨ht.1, ht.2.trans (Nat.pow_le_pow_right hb hA)⟩
