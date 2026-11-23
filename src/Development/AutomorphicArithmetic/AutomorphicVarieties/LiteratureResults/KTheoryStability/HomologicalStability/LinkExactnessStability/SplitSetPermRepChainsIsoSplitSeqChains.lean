module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.MemSplitSeqIff
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
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem

@[expose] public section

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

namespace GlobalTheory.HomStab

private theorem split_set_boundary_comp_face_sum (R : Type) [CommRing R] (n p : ℕ) :
    (Finsupp.lmapDomain ℤ ℤ (fun x : SplitSet R n p => (x.1 : List ((Fin n → R) × (Fin n → R))))) ∘ₗ
      (∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ) • Finsupp.lmapDomain ℤ ℤ (face R n p i)) =
    bd _ ∘ₗ Finsupp.lmapDomain ℤ ℤ
      (fun x : SplitSet R n (p + 1) => (x.1 : List ((Fin n → R) × (Fin n → R)))) := by
  apply Finsupp.lhom_ext
  intro l a
  have hlen : l.1.length = p + 1 := l.2.2

  simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul,
  Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  unfold bd
  rw [Finsupp.linearCombination_single, hlen, Finset.smul_sum]
  rw [← Fin.sum_univ_eq_sum_range (fun i => a • ((-1 : ℤ) ^ i • Finsupp.single (l.1.eraseIdx i) (1 : ℤ)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (l.1.eraseIdx i) a =
    a • ((-1 : ℤ) ^ (i : ℕ) • Finsupp.single (l.1.eraseIdx i) (1 : ℤ))
  simp [Finsupp.smul_single, mul_comm]

theorem splitSet_chains_incl : ∀ (R : Type) [CommRing R] (n p : ℕ), Function.Injective (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n p → _)) ∧ LinearMap.range (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n p → _)) = chains (splitSeq R n) p ∧ ∀ c : SplitSet R n (p + 1) →₀ ℤ, Finsupp.mapDomain (Subtype.val : SplitSet R n p → _) ((splitD R n p).hom c) = bd _ (Finsupp.mapDomain (Subtype.val : SplitSet R n (p + 1) → _) c) := by
  intro R _ n p
  have hD : ∀ c : SplitSet R n (p + 1) →₀ ℤ, (splitD R n p).hom c =
      (∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ) • Finsupp.mapDomain (face R n p i) c : SplitSet R n p →₀ ℤ) := by
    intro c
    simp [splitD, permMap, Rep.sum_hom, Rep.hom_ofHom, Rep.zsmul_hom, Rep.smul_hom,
      Representation.IntertwiningMap.sum_apply, Representation.IntertwiningMap.smul_apply]
  refine ⟨?_, ?_, ?_⟩
  · exact Finsupp.mapDomain_injective Subtype.val_injective
  · rw [LinearMap.range_eq_map, ← Finsupp.supported_univ, Finsupp.lmapDomain_supported, Set.image_univ]
    unfold chains
    congr 1
    ext l
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hl
      exact ⟨⟨l, hl⟩, rfl⟩
  · intro c
    rw [hD]
    have key := LinearMap.congr_fun (split_set_boundary_comp_face_sum R n p) c
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      Finsupp.lmapDomain_apply] at key
    exact key

end GlobalTheory.HomStab

section
theorem _root_.GlobalTheory.T.splitSet_permRep_chains_iso_splitSeq_chains : ∀ (R : Type) [CommRing R] (n p : ℕ), Function.Injective (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n p → _)) ∧ LinearMap.range (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n p → _)) = chains (splitSeq R n) p ∧ ∀ c : SplitSet R n (p + 1) →₀ ℤ, Finsupp.mapDomain (Subtype.val : SplitSet R n p → _) ((splitD R n p).hom c) = bd _ (Finsupp.mapDomain (Subtype.val : SplitSet R n (p + 1) → _) c) := by
  first
  | exact @GlobalTheory.HomStab.splitSet_chains_incl
end
