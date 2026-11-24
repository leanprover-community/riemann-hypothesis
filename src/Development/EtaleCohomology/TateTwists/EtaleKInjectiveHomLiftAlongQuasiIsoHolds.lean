module

public import Development.EtaleCohomology.TateTwists.EtaleKInjectiveHomLiftAlongQuasiIsoUpToHomotopy
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

@[expose] public section

open CategoryTheory Limits GlobalTheory.EtC

theorem LateralTheory.EtaleFoundations.etale_kInjective_hom_lift_along_quasiIso_holds : LateralTheory.EtaleFoundations.EtaleKInjectiveHomLiftAlongQuasiIsoUpToHomotopy := by
  intro R _ K L I _ f _
  have hI := CochainComplex.IsKInjective.rightOrthogonal I
  rw [← ObjectProperty.isLocal_trW] at hI
  have hf : (HomotopyCategory.subcategoryAcyclic (Shv R)).trW
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map f) := by
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
      HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact (HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance
  have hb := hI _ hf
  refine ⟨fun a => ?_, fun m m' h => ?_⟩
  · obtain ⟨m', hm'⟩ := hb.2 ((HomotopyCategory.quotient _ _).map a)
    obtain ⟨m, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective m'
    refine ⟨m, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
    rw [Functor.map_comp]; exact hm'
  · obtain ⟨h⟩ := h
    have e := HomotopyCategory.eq_of_homotopy _ _ h
    rw [Functor.map_comp, Functor.map_comp] at e
    exact ⟨HomotopyCategory.homotopyOfEq _ _ (hb.1 e)⟩
