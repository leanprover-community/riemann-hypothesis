module

public import Formalism.ConjugateSelfDual.Statement
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong

namespace GlobalTheory

theorem orbit_finite_mem_finite_ext : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (J : Type) (z : J → ℂ),
    (Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (z j)).Finite →
      ∃ L : IntermediateField ℚ_[l] (Qbar l), FiniteDimensional ℚ_[l] L ∧ ∀ j, ι.symm (z j) ∈ L := by
  intro l _ ι J z hfin
  classical
  set O := Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (z j) with hO
  haveI : Finite O := hfin.to_subtype
  set w : J → Qbar l := fun j => ι.symm (z j) with hw
  let K : Finset J → IntermediateField ℚ_[l] (Qbar l) := fun s =>
    IntermediateField.adjoin ℚ_[l] (w '' (s : Set J))
  have hKfin : ∀ s, FiniteDimensional ℚ_[l] (K s) := fun s => by
    haveI : Finite (w '' (s : Set J)) := (s.finite_toSet.image w).to_subtype
    exact IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  have hbound : ∀ s, Module.finrank ℚ_[l] (K s) ≤ Nat.card O := by
    intro s
    haveI := hKfin s
    rw [← AlgHom.card ℚ_[l] (K s) (Qbar l), ← Nat.card_eq_fintype_card]
    let g : (K s →ₐ[ℚ_[l]] Qbar l) → O := fun φ =>
      ⟨fun j => ι (φ.liftNormal (Qbar l) (w j)),
        ι.symm.trans ((AlgEquiv.ofBijective (φ.liftNormal (Qbar l))
          (Algebra.IsAlgebraic.algHom_bijective _)).toRingEquiv.trans ι), rfl⟩
    apply Nat.card_le_card_of_injective g
    intro φ ψ h
    apply IntermediateField.adjoin_algHom_ext
    rintro x ⟨j, hj, rfl⟩
    have h1 := ι.injective (congrFun (congrArg Subtype.val h) j)
    have e1 := AlgHom.liftNormal_commutes φ (Qbar l) ⟨w j, IntermediateField.subset_adjoin _ _ ⟨j, hj, rfl⟩⟩
    have e2 := AlgHom.liftNormal_commutes ψ (Qbar l) ⟨w j, IntermediateField.subset_adjoin _ _ ⟨j, hj, rfl⟩⟩
    simp only [Algebra.algebraMap_self, RingHom.id_apply] at e1 e2
    exact e1.symm.trans (h1.trans e2)
  set R := Set.range fun s : Finset J => Module.finrank ℚ_[l] (K s) with hR
  have hne : R.Nonempty := ⟨_, ∅, rfl⟩
  have hbdd : BddAbove R := ⟨Nat.card O, by rintro _ ⟨s, rfl⟩; exact hbound s⟩
  obtain ⟨s0, hs0⟩ := Nat.sSup_mem hne hbdd
  haveI := hKfin s0
  refine ⟨K s0, inferInstance, fun j => ?_⟩
  have hle : K s0 ≤ K (insert j s0) :=
    IntermediateField.adjoin.mono _ _ _ (Set.image_mono (by simp))
  haveI := hKfin (insert j s0)
  have heq : K s0 = K (insert j s0) := by
    apply IntermediateField.eq_of_le_of_finrank_le hle
    rw [show Module.finrank ℚ_[l] (K s0) = sSup R from hs0]
    exact le_csSup hbdd ⟨insert j s0, rfl⟩
  rw [heq]
  exact IntermediateField.subset_adjoin _ _ ⟨j, by simp, rfl⟩

end GlobalTheory
