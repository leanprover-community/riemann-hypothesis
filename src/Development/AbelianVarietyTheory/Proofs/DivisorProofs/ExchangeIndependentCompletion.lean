module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentBasisCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.PointHeight
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
public import Mathlib.Data.Fintype.Sum
public import Mathlib.LinearAlgebra.Dimension.Constructions
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA
import ReciprocityTheory.SemistableReduction.DetGramEqProdGramSchmidt

@[expose] public section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory

theorem exchange_independent_completion (E M : Type) [Field E] [AddCommGroup M] [Module E M]
    (n d : ℕ) (v : Fin n → M) (w : Fin d → M) (hv : LinearIndependent E v)
    (hw : LinearIndependent E w) (hvw : ∀ k, v k ∈ Submodule.span E (Set.range w)) :
    ∃ K : Finset (Fin d), n + K.card = d ∧ LinearIndependent E (Sum.elim v fun k : K => w k) := by
  classical
  obtain ⟨b, hbt, hsb, htb, hb⟩ := exists_linearIndepOn_id_extension
    (s := Set.range v) (t := Set.range v ∪ Set.range w) (K := E)
    hv.linearIndepOn_id Set.subset_union_left
  let K : Finset (Fin d) := Finset.univ.filter (fun k => w k ∈ b ∧ w k ∉ Set.range v)
  let u : Fin n ⊕ K → M := Sum.elim v fun k : K => w k
  have hK : ∀ k : K, w k ∈ b ∧ w k ∉ Set.range v := fun k => (Finset.mem_filter.1 k.2).2
  have hu_inj : Function.Injective u := by
    rintro (i | i) (j | j) h
    · simp only [u, Sum.elim_inl] at h; rw [hv.injective h]
    · simp only [u, Sum.elim_inl, Sum.elim_inr] at h; exact absurd ⟨i, h⟩ (hK j).2
    · simp only [u, Sum.elim_inl, Sum.elim_inr] at h; exact absurd ⟨j, h.symm⟩ (hK i).2
    · simp only [u, Sum.elim_inr] at h; rw [Subtype.ext (hw.injective h)]
  have hu_mem : ∀ x, u x ∈ b := by
    rintro (i | i)
    · exact hsb ⟨i, rfl⟩
    · exact (hK i).1
  have hu_range : Set.range u = b := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩; exact hu_mem x
    · intro x hx
      by_cases hxv : x ∈ Set.range v
      · obtain ⟨i, rfl⟩ := hxv; exact ⟨Sum.inl i, rfl⟩
      · rcases hbt hx with ⟨i, rfl⟩ | ⟨k, rfl⟩
        · exact absurd ⟨i, rfl⟩ hxv
        · have hk : k ∈ K := Finset.mem_filter.2 ⟨Finset.mem_univ _, hx, hxv⟩
          exact ⟨Sum.inr ⟨k, hk⟩, rfl⟩
  have hli : LinearIndependent E u :=
    LinearIndependent.comp (show LinearIndependent E (fun x : b => (x : M)) from hb) (fun x => (⟨u x, hu_mem x⟩ : b)) (fun x y h => hu_inj (congrArg Subtype.val h))
  refine ⟨K, ?_, hli⟩
  have hspan : Submodule.span E (Set.range u) = Submodule.span E (Set.range w) := by
    apply le_antisymm
    · rw [Submodule.span_le, hu_range]
      intro x hx
      rcases hbt hx with ⟨i, rfl⟩ | ⟨k, rfl⟩
      · exact hvw i
      · exact Submodule.subset_span ⟨k, rfl⟩
    · rw [Submodule.span_le, hu_range]; exact Set.subset_union_right.trans htb
  have h1 := finrank_span_eq_card hli
  have h2 := finrank_span_eq_card hw
  rw [hspan, h2] at h1
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe] at h1
  omega

end GlobalTheory
