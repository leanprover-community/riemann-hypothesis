module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem ker_map_residue_eq_span {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) {σ : Type*} :
    RingHom.ker (MvPolynomial.map (IsLocalRing.residue O) : MvPolynomial σ O →+* _) =
      Ideal.span {C ϖ} := by
  rw [MvPolynomial.ker_map, IsLocalRing.ker_residue,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
    Set.image_singleton]

theorem SpecialIdealCorresp.proof : SpecialIdealCorresp.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P W hW hϖW
  obtain ⟨π, hπ⟩ : ∃ π : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O),
      π = MvPolynomial.map (IsLocalRing.residue O) := ⟨_, rfl⟩
  have hsp : ∀ V : Ideal (MRing ι O), specialIdeal V = V.map π := fun V => by rw [hπ]; rfl
  have hsurj : Function.Surjective π := hπ ▸ MvPolynomial.map_surjective _ IsLocalRing.residue_surjective
  have hker : RingHom.ker π = Ideal.span {C ϖ} := hπ ▸ ker_map_residue_eq_span hϖ
  have hle : ∀ {V : Ideal (MRing ι O)}, (C ϖ : MRing ι O) ∈ V → RingHom.ker π ≤ V := fun h => by
    rw [hker, Ideal.span_le, Set.singleton_subset_iff]; exact h
  have hcm : ∀ {V : Ideal (MRing ι O)}, (C ϖ : MRing ι O) ∈ V → (V.map π).comap π = V := fun h => by
    rw [Ideal.comap_map_of_surjective' π hsurj, sup_eq_left.mpr (hle h)]
  simp only [hsp]
  refine ⟨Ideal.map_isPrime_of_surjective hsurj (hle hϖW), ?_, ?_, ?_⟩
  · have hJ : P ⊔ Ideal.span {C ϖ} = (P.map π).comap π := by
      rw [Ideal.comap_map_of_surjective' π hsurj, hker]
    rw [hJ, Ideal.comap_minimalPrimes_eq_of_surjective hsurj]
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      rwa [Ideal.map_comap_of_surjective π hsurj]
    · intro h
      exact ⟨_, h, hcm hϖW⟩
  · have hX : ∀ v, (X v : MRing ι O) ∈ W ↔ (X v : MRing ι (IsLocalRing.ResidueField O)) ∈ W.map π :=
      fun v => by
        conv_lhs => rw [← hcm hϖW]
        rw [Ideal.mem_comap, hπ, MvPolynomial.map_X]
    simp only [IsRelevant, hX]
  · intro W' _ hϖW' h
    rw [← hcm hϖW', ← hcm hϖW, h]

end GroundTheory.Heights₂.Heights.NumbersDVR
