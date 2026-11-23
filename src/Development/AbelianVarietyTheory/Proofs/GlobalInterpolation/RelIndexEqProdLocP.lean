module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove

theorem relIndex_eq_prod_locP (E : Type) [Field E] [NumberField E] (W : Type) [AddCommGroup W] [Module (𝓞 E) W]
    (S : Finset (HeightOneSpectrum (𝓞 E))) (M₁ M₂ : Submodule (𝓞 E) W) (h₁ : Full M₁) (h₂ : Full M₂) (hD : Dom S M₁ M₂) :
    M₂.toAddSubgroup.relIndex M₁.toAddSubgroup =
      ∏ P ∈ S, (localization₂ P.asIdeal M₂).toAddSubgroup.relIndex (localization₂ P.asIdeal M₁).toAddSubgroup := by
  classical
  let Q : S → Type := fun P => (localization₂ P.1.asIdeal M₁).toAddSubgroup ⧸
    (localization₂ P.1.asIdeal M₂).toAddSubgroup.addSubgroupOf (localization₂ P.1.asIdeal M₁).toAddSubgroup
  let g : ∀ P : S, M₁.toAddSubgroup →+ Q P := fun P =>
    (QuotientAddGroup.mk' _).comp (AddSubgroup.inclusion (H := M₁.toAddSubgroup) (K := (localization₂ P.1.asIdeal M₁).toAddSubgroup)
      fun x hx => mem_localization_of_mem P.1 hx)
  have hg : ∀ (P : S) (x : M₁.toAddSubgroup) (y : (localization₂ P.1.asIdeal M₁).toAddSubgroup),
      g P x = (QuotientAddGroup.mk y : Q P) ↔ (x : W) - y ∈ localization₂ P.1.asIdeal M₂ := by
    intro P x y
    exact QuotientAddGroup.eq_iff_sub_mem
  let f : M₁.toAddSubgroup →+ ∀ P : S, Q P := AddMonoidHom.pi g
  have hker : f.ker = M₂.toAddSubgroup.addSubgroupOf M₁.toAddSubgroup := by
    ext x
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, funext_iff]
    constructor
    · intro h
      refine mem_of_locP fun P => ?_
      by_cases hP : P ∈ S
      · simpa using (hg ⟨P, hP⟩ x 0).1 (h ⟨P, hP⟩)
      · exact hD.2 P hP (mem_localization_of_mem P x.2)
    · intro h P
      exact (hg P x 0).2 (by simpa using mem_localization_of_mem P.1 h)
  have hsurj : Function.Surjective f := by
    intro y
    choose x hx using fun P : S => QuotientAddGroup.mk_surjective (y P)
    choose t ht ht' using fun P : S => (h₁.inf h₂).approx {P.1} (x P : W)
    have htM : ∀ P : S, t P ∈ M₁ := fun P => mem_of_locP fun R => by
      by_cases hR : R = P.1
      · subst hR
        have := (localization₂ P.1.asIdeal M₁).add_mem
          (localization_mono P.1 inf_le_left (ht P P.1 (Finset.mem_singleton_self _))) (x P).2
        simpa using this
      · exact localization_mono R inf_le_left (ht' P R (by simpa using hR))
    refine ⟨∑ P : S, ⟨t P, htM P⟩, funext fun P => ?_⟩
    rw [← hx P]
    refine (hg P _ _).2 ?_
    change M₁.toAddSubgroup.subtype (∑ P : S, ⟨t P, htM P⟩) - (x P : W) ∈ _
    rw [map_sum M₁.toAddSubgroup.subtype, ← Finset.add_sum_erase _ _ (Finset.mem_univ P), add_sub_right_comm]
    refine Submodule.add_mem _ (localization_mono P.1 inf_le_right (ht P P.1 (Finset.mem_singleton_self _)))
      (Submodule.sum_mem _ fun R hR => localization_mono P.1 inf_le_right (ht' R P.1 ?_))
    rw [Finset.mem_singleton]
    exact fun e => (Finset.ne_of_mem_erase hR) (Subtype.ext e.symm)
  rw [AddSubgroup.relIndex, ← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj, AddSubgroup.card_top,
    Nat.card_pi, ← Finset.prod_coe_sort S]
  rfl

end GlobalTheory.ThetaMove
