module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PointDegreePosSt
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PHilbertPositive
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section

variable {k : Type u} [Field k] {N : ℕ}

theorem oneBlock_homogeneousComponent (f : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k) (n : ℕ) :
    oneBlock (S := k) (N := N) (homogeneousComponent n f) =
      homogeneousComponent n (oneBlock (S := k) (N := N) f) := by
  classical
  have ho : ∀ g, oneBlock (S := k) (N := N) g = rename (HilbertPositive.blockEquiv N) g := fun _ => rfl
  ext d
  set d' := Finsupp.mapDomain (HilbertPositive.blockEquiv N).symm d with hd'
  have hd : d = Finsupp.mapDomain (HilbertPositive.blockEquiv N) d' := by
    rw [hd', ← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  have hdeg : d.degree = d'.degree := by
    rw [hd, Finsupp.degree_mapDomain]
  rw [ho, ho, coeff_homogeneousComponent, hd,
    coeff_rename_mapDomain _ (HilbertPositive.blockEquiv N).injective,
    coeff_rename_mapDomain _ (HilbertPositive.blockEquiv N).injective, coeff_homogeneousComponent, ← hd, hdeg]

theorem isMultiProjPrime_comap_oneBlock {Ω : Type w} [Field Ω] [Algebra k Ω] {x : Fin (N + 1) → Ω}
    {pp : Ideal (Poly k N)} (h : IsSubvar x pp 0) :
    NumbersDVR.IsMultiProjPrime (pp.comap (oneBlock (S := k) (N := N)).toRingHom) ∧
      FieldNumbers.relDim (pp.comap (oneBlock (S := k) (N := N)).toRingHom) =
        ((0 : ℕ) : WithBot (WithTop ℤ)) := by
  have := h.isPrime
  let e : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ≃+* Poly k N :=
    (renameEquiv k (HilbertPositive.blockEquiv N)).toRingEquiv
  have hc : pp.comap (oneBlock (S := k) (N := N)).toRingHom = pp.comap e.toRingHom :=
    Ideal.ext fun _ => Iff.rfl
  refine ⟨⟨Ideal.comap_isPrime _ _, ?_, ?_⟩, ?_⟩
  · intro f hf b
    have heq : weightedHomogeneousComponent (NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1))) b f =
        homogeneousComponent (b ()) f := by
      ext d
      rw [coeff_weightedHomogeneousComponent, coeff_homogeneousComponent,
        HilbertPositive.weight_blockWeight_one d]
      congr 1
      apply propext
      constructor
      · intro h; rw [← h]
      · intro h; funext u; exact h
    rw [heq]
    change oneBlock (S := k) (N := N) _ ∈ pp
    change oneBlock (S := k) (N := N) f ∈ pp at hf
    rw [oneBlock_homogeneousComponent]
    exact h.homog _ hf _
  · intro u
    obtain ⟨i, hi⟩ := h.relevant
    refine ⟨i, ?_⟩
    change oneBlock (S := k) (N := N) (X _) ∉ pp
    rw [oneBlock, rename_X]
    exact hi
  · rw [FieldNumbers.CutRegular.relDim_eq_natCast_iff, Fintype.card_unit, hc]
    have hm : pp = (pp.comap e.toRingHom).map e.toRingHom := by
      rw [Ideal.map_comap_of_surjective e.toRingHom e.surjective]
    rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ e hm), h.dim]

end

theorem PointDegreePos.proof : PointDegreePos.Statement.{u, w} := by
  intro k _ Ω _ _ N x pp h
  obtain ⟨hP, hrel⟩ := isMultiProjPrime_comap_oneBlock h
  have := hP.isPrime
  obtain ⟨hfd, -⟩ := FieldNumbers.IntNumBase.full k Unit (fun _ => Fin (N + 1)) _ hP hrel
  unfold FieldNumbers.resDeg
  rw [dite_eq_left hP.isPrime]
  exact Module.finrank_pos

end

end GroundTheory.Heights₂.Heights.Kleiman
