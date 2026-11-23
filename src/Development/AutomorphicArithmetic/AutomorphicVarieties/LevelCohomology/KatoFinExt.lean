module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
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
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.QuotRepMk
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

private theorem fd_adjoin_range (l : ℕ) [Fact l.Prime] {ι : Type} [Finite ι] (f : ι → PadicAlgCl l) :
    FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] (Set.range f)) := by
  haveI : Finite (Set.range f) := (Set.finite_range _).to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic z).isIntegral

private theorem coc_finext (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] (K₀ : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K₀] (n : ℕ)
    (θ : Γ → (Fin n → PadicAlgCl l) → (Fin n → PadicAlgCl l)) (c : Γ → Fin n → PadicAlgCl l)
    (hθ : ∀ (L : IntermediateField ℚ_[l] (PadicAlgCl l)), K₀ ≤ L → ∀ g v, (∀ j, v j ∈ L) → ∀ j, θ g v j ∈ L)
    (hc1 : c 1 = 0) (hc : Continuous c)
    (hcoc : ∀ g h, c (g * h) = c g + θ g (c h)) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧ K₀ ≤ E ∧ ∀ g j, c g j ∈ E := by
  obtain ⟨ι, _, K, hK, hcov⟩ := GlobalTheory.CompactRepField.exists_countable_family l
  let H : ι → Subgroup Γ := fun i =>
    { carrier := {g | ∀ j, c g j ∈ K₀ ⊔ K i}
      one_mem' := by
        intro j
        rw [hc1]; exact zero_mem _
      mul_mem' := fun {g h} hg hh j => by
        rw [hcoc]
        exact add_mem (hg j) (hθ _ le_sup_left g _ hh j)
      inv_mem' := fun {g} hg j => by
        have h1 := hcoc g⁻¹ g
        rw [inv_mul_cancel, hc1] at h1
        rw [eq_neg_of_add_eq_zero_left h1.symm]
        exact neg_mem (hθ _ le_sup_left _ _ hg j) }
  have hcl : ∀ i, IsClosed (H i : Set Γ) := fun i => by
    haveI := hK i
    haveI : FiniteDimensional ℚ_[l] (K₀ ⊔ K i).toSubalgebra.toSubmodule :=
      (inferInstance : FiniteDimensional ℚ_[l] (K₀ ⊔ K i : IntermediateField ℚ_[l] (PadicAlgCl l)))
    have : (H i : Set Γ) = ⋂ j, (fun g => c g j) ⁻¹' ((K₀ ⊔ K i).toSubalgebra.toSubmodule : Set (PadicAlgCl l)) := by
      ext g
      rw [Set.mem_iInter]
      exact Iff.rfl
    rw [this]
    exact isClosed_iInter fun j =>
      (Submodule.closed_of_finiteDimensional (K₀ ⊔ K i).toSubalgebra.toSubmodule).preimage
        ((continuous_apply j).comp hc)
  have hun : ⋃ i, (H i : Set Γ) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    obtain ⟨i, hi⟩ := hcov (Set.range (c g)) (Set.finite_range _)
    exact Set.mem_iUnion.2 ⟨i, fun j => (le_sup_right : K i ≤ K₀ ⊔ K i) (hi ⟨j, rfl⟩)⟩
  obtain ⟨i, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hcl hun
  have hop : IsOpen (H i : Set Γ) := Subgroup.isOpen_of_mem_nhds _ (mem_interior_iff_mem_nhds.1 hx)
  haveI : Finite (Γ ⧸ H i) := Subgroup.quotient_finite_of_isOpen _ hop
  haveI := fd_adjoin_range l (fun q : (Γ ⧸ H i) × Fin n => c q.1.out q.2)
  haveI := hK i
  refine ⟨IntermediateField.adjoin ℚ_[l] (Set.range fun q : (Γ ⧸ H i) × Fin n => c q.1.out q.2) ⊔ (K₀ ⊔ K i),
    inferInstance, le_sup_left.trans le_sup_right, fun g j => ?_⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (H i) g
  have hg : g = (g : Γ ⧸ H i).out * (h : Γ)⁻¹ := by
    rw [hh, mul_inv_cancel_right]
  rw [hg, hcoc]
  refine add_mem ?_ (hθ _ (le_sup_left.trans le_sup_right) _ _ (fun k => ?_) j)
  · exact (le_sup_left :
        IntermediateField.adjoin ℚ_[l] (Set.range fun q : (Γ ⧸ H i) × Fin n => c q.1.out q.2) ≤ _)
      (IntermediateField.subset_adjoin _ _ ⟨((g : Γ ⧸ H i), j), rfl⟩)
  · exact (le_sup_right : K₀ ⊔ K i ≤ _) ((H i).inv_mem h.2 k)
