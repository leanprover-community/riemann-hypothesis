module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing

theorem UpperTheory.V.AlgebraTools.exists_isRegular_of_free_quotient :
    ∀ (L B : Type) [CommRing L] [IsRegularLocalRing L] [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
      [Algebra L B] [IsLocalHom (algebraMap L B)] (M : Type) [AddCommGroup M] [Module B M] [Module L M]
      [IsScalarTower L B M] [Module.Finite B M] [Nontrivial M] (r e : ℕ) (y : Fin r → B),
      ringKrullDim L = e → (∀ i, y i ∈ maximalIdeal B) → GlobalTheory.IsQuasiRegularSeq M y →
      Module.Free L (M ⧸ Ideal.span (Set.range y) • (⊤ : Submodule B M)) →
      ∃ xs : List B, xs.length = r + e ∧ (∀ x ∈ xs, x ∈ maximalIdeal B) ∧ RingTheory.Sequence.IsRegular M xs := by
  intro L B _ _ _ _ _ _ _ M _ _ _ _ _ _ r e y he hy hq hfree
  obtain ⟨zs, h, hd⟩ := GlobalTheory.exists_ofList_eq_maximalIdeal_length_eq L
  have hreg := (GlobalTheory.isRegular_of_ofList_eq_maximalIdeal h hd.le).toIsWeaklyRegular
  have hlen : zs.length = e := by
    rw [he] at hd
    exact_mod_cast hd
  have hmem : ∀ x ∈ List.ofFn y ++ zs.map (algebraMap L B), x ∈ maximalIdeal B := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hy i
    · refine map_maximalIdeal_le (algebraMap L B) ?_
      rw [← h, Ideal.map_ofList]
      exact Ideal.subset_span hx
  refine ⟨List.ofFn y ++ zs.map (algebraMap L B), by simp [hlen], hmem, ?_⟩
  rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem,
    RingTheory.Sequence.isWeaklyRegular_append_iff, GlobalTheory.ofList_ofFn_eq_span_range,
    RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff]
  refine ⟨hq.isWeaklyRegular ?_, ?_⟩
  · exact fun i => maximalIdeal_le_jacobson _ (hy i)
  · exact ((TensorProduct.lid L _).isWeaklyRegular_congr zs).mp hreg.isWeaklyRegular_rTensor
