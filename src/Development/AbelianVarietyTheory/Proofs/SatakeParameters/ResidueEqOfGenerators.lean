module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.ClassResidueGenerators

theorem residue_eq_of_generators {O A : Type} [CommRing O] [IsLocalRing O] [Ring A] [Algebra O A]
    (S : Set A) (ψ ψ' : ↥(Algebra.adjoin O S) →ₐ[O] O)
    (h : ∀ (a : A) (ha : a ∈ S),
      IsLocalRing.residue O (ψ ⟨a, Algebra.subset_adjoin ha⟩) =
        IsLocalRing.residue O (ψ' ⟨a, Algebra.subset_adjoin ha⟩))
    (x : A) (hx : x ∈ Algebra.adjoin O S) :
    IsLocalRing.residue O (ψ ⟨x, hx⟩) = IsLocalRing.residue O (ψ' ⟨x, hx⟩) := by
  induction hx using Algebra.adjoin_induction with
  | mem a ha => exact h a ha
  | algebraMap r =>
    have e : (⟨algebraMap O A r, Subalgebra.algebraMap_mem _ r⟩ : ↥(Algebra.adjoin O S)) =
        algebraMap O _ r := rfl
    rw [e, ψ.commutes, ψ'.commutes]
  | add a b ha hb iha ihb =>
    have e : (⟨a + b, add_mem ha hb⟩ : ↥(Algebra.adjoin O S)) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
    rw [e, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), iha, ihb]
  | mul a b ha hb iha ihb =>
    have e : (⟨a * b, mul_mem ha hb⟩ : ↥(Algebra.adjoin O S)) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [e, map_mul, map_mul, map_mul, map_mul, iha, ihb]

theorem cls_eq_of_generators : ∀ {O K V : Type} [inst : CommRing O] [inst_1 : Field K] [inst_2 : Algebra O K] [inst_3 : AddCommGroup V] [inst_4 : Module K V] [inst_5 : Module O V] [inst_6 : IsScalarTower O K V] [inst_7 : IsLocalRing O] (S : Set (Module.End K V)) (ψ ψ' : ↥(Algebra.adjoin O S) →ₐ[O] O), (∀ (a : Module.End K V) (h : a ∈ S), (IsLocalRing.residue O : O → IsLocalRing.ResidueField O) ((ψ : ↥(Algebra.adjoin O S) → O) (⟨a, Algebra.subset_adjoin h⟩ : ↥(Algebra.adjoin O S))) = (IsLocalRing.residue O : O → IsLocalRing.ResidueField O) ((ψ' : ↥(Algebra.adjoin O S) → O) (⟨a, Algebra.subset_adjoin h⟩ : ↥(Algebra.adjoin O S)))) → Formalism.L2.NCov.cls ψ = Formalism.L2.NCov.cls ψ' := by
  intro O K V _ _ _ _ _ _ _ _ S ψ ψ' h
  unfold Formalism.L2.NCov.cls
  congr 1
  ext ⟨x, hx⟩
  exact residue_eq_of_generators S ψ ψ' h x hx

end GlobalTheory.ClassResidueGenerators
