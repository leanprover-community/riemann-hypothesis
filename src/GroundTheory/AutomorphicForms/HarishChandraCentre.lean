module

public import GroundTheory.AutomorphicForms.HarishChandraCentre.Projection
public import GroundTheory.AutomorphicForms.HarishChandraCentre.Injective
public import GroundTheory.AutomorphicForms.HarishChandraCentre.VermaCoordEqZeroOfMemNPlusU
public import GroundTheory.AutomorphicForms.HarishChandraCentre.LeadingTerm
public import GroundTheory.AutomorphicForms.HarishChandraCentre.Symmetric
public import GroundTheory.AutomorphicForms.HarishChandraCentre.Capelli
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

namespace GroundTheory.Automorphic.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

open MvPolynomial

variable {n : ℕ}

theorem harishChandraHom_mem_symmetricSubalgebra (z : Subalgebra.center ℂ (U n)) :
    harishChandraHom z ∈ symmetricSubalgebra (Fin n) ℂ :=
  harishChandraHom_isSymmetric z

noncomputable def capelliCenter (k : ℕ) : Subalgebra.center ℂ (U n) :=
  ⟨capelli (k + 1), capelli_mem_center _⟩

theorem adjoin_harishChandraHom_capelli :
    Algebra.adjoin ℂ (Set.range fun k : Fin n => harishChandraHom (capelliCenter (n := n) k)) =
      symmetricSubalgebra (Fin n) ℂ :=
  adjoin_eq_symmetricSubalgebra _ (fun _ => harishChandraHom_isSymmetric _)
    (fun k => totalDegree_harishChandraHom_capelli_sub k)

theorem range_harishChandraHom :
    (harishChandraHom (n := n)).range = symmetricSubalgebra (Fin n) ℂ := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    exact harishChandraHom_isSymmetric z
  · rw [← adjoin_harishChandraHom_capelli, Algebra.adjoin_le_iff]
    rintro _ ⟨k, rfl⟩
    exact ⟨_, rfl⟩

noncomputable def harishChandraEquiv :
    Subalgebra.center ℂ (U n) ≃ₐ[ℂ] symmetricSubalgebra (Fin n) ℂ :=
  (AlgEquiv.ofInjective harishChandraHom harishChandraHom_injective).trans
    (Subalgebra.equivOfEq _ _ range_harishChandraHom)

@[simp] theorem harishChandraEquiv_apply (z : Subalgebra.center ℂ (U n)) :
    (harishChandraEquiv z : MvPolynomial (Fin n) ℂ) = harishChandraHom z := rfl

end GroundTheory.Automorphic.HarishChandra
