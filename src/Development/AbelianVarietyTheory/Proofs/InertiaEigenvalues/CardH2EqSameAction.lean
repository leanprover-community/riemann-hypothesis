module

public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract
import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs

@[expose] public section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.H2CardScalars

theorem card_H2_eq_of_same_action {R S : Type} [CommRing R] [CommRing S] {G : Type} [Group G]
    [TopologicalSpace G] {M : Type} [AddCommGroup M] [Module R M] [Module S M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [ContinuousConstSMul S M]
    (rho : Representation R G M) (rho' : Representation S G M)
    (h : ∀ g m, rho g m = rho' g m) : Nat.card (H2 rho) = Nat.card (H2 rho') := by
  have hZ : ∀ f : G × G → M, f ∈ Z2 rho ↔ f ∈ Z2 rho' := by
    intro f; rw [mem_cocycles2, mem_cocycles2]; simp only [h]
  have hd : ∀ c : G → M, d1 rho c = d1 rho' c := fun c => funext fun p => by
    simp only [d1, LinearMap.coe_mk, AddHom.coe_mk, h]
  have hB : ∀ f : G × G → M, f ∈ B2 rho ↔ f ∈ B2 rho' := by
    intro f; rw [separated_dvr_second_cohomology_mem, separated_dvr_second_cohomology_mem]; simp only [hd]
  let e : Z2 rho ≃ Z2 rho' := Equiv.subtypeEquiv (Equiv.refl _) hZ
  apply Nat.card_congr
  refine Quotient.congr e ?_
  intro a b
  rw [Submodule.quotientRel_def, Submodule.quotientRel_def]
  simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_sub]
  exact hB _

end GlobalTheory.H2CardScalars
