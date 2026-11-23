module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.SchemeImage
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent
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
import Mathlib.SetTheory.ZFC.PSet
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits

universe u

noncomputable section

lemma isIso_opens_ι_restrict {Z : Scheme.{u}} (O : Z.Opens) : IsIso (O.ι ∣_ O) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply le_antisymm le_top
  intro x _
  refine ⟨⟨x, ?_⟩, ?_⟩
  · change O.ι x ∈ O
    exact x.2
  · apply Subtype.ext
    exact morphismRestrict_base_coe O.ι O ⟨x, _⟩

theorem exists_irreducible_isIso_restrict (Z : Scheme.{u}) [IsNoetherian Z] [Nonempty Z] :
    ∃ (Z₁ : Scheme.{u}) (c : Z₁ ⟶ Z) (O : Z.Opens), IsClosedImmersion c ∧ IrreducibleSpace Z₁ ∧
      (O : Set Z).Nonempty ∧ IsIso (c ∣_ O) := by
  obtain ⟨z⟩ := ‹Nonempty Z›
  have hC := irreducibleComponent_mem_irreducibleComponents z
  set C := irreducibleComponent z
  set O := Z.irreducibleComponentOpen C
  refine ⟨Z.irreducibleComponent C hC, Z.irreducibleComponentι C hC, O, inferInstance,
    inferInstance, ?_, ?_⟩
  · obtain ⟨o, ho, hne, hoC⟩ :=
      NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC

    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hcl := closure_sUnion_irreducibleComponents_sdiff_singleton
      NoetherianSpace.finite_irreducibleComponents C hC
    have : (O : Set Z) = (⋃₀ (irreducibleComponents Z \ {C}))ᶜ := rfl
    rw [this, Set.compl_empty_iff] at h
    rw [h, Set.compl_univ, closure_empty] at hcl
    exact hC.1.nonempty.ne_empty hcl.symm
  · have hI := Z.irreducibleComponentIdeal_def C hC
    have : IsIso (O.ι ∣_ O) := isIso_opens_ι_restrict O
    have key := SchemeImage.imageRestrictLift_fac O.ι O
    change IsIso ((Z.irreducibleComponentIdeal C hC).subschemeι ∣_ O)
    rw [hI]
    change IsIso (O.ι.imageι ∣_ O)
    rw [← key]
    infer_instance

end

end GroundTheory.Arith.SchemeCoh
