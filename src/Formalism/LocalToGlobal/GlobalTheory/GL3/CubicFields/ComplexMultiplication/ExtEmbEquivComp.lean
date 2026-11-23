module

public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.UniqInvOfLat
public import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical Cardinal
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive)
open Formalism.MainNotions.TaylorLogMetric (lamOf)

theorem extEmb_equiv_comp {R K L : Type} [Field R] [Field K] [Field L] [IsAlgClosed K]
    [IsAlgClosed L] (f : R →+* K) (g : R →+* L) (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ σ : K ≃+* L, ∀ r : R, σ (f r) = g r := by
  letI : Algebra R K := f.toAlgebra
  letI : Algebra R L := g.toAlgebra
  haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).2 f.injective
  haveI : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).2 g.injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R L
  have h1 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs hR hK
  have h2 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hR (hKL ▸ hK)
  have e : s ≃ t := (Cardinal.eq.1 (h1.symm.trans (hKL.trans h2))).some
  refine ⟨IsAlgClosed.equivOfTranscendenceBasis _ _ e hs ht, fun r => ?_⟩
  simp only [IsAlgClosed.equivOfTranscendenceBasis]
  rw [show f r = algebraMap R K r from rfl,
    IsScalarTower.algebraMap_apply R (Algebra.adjoin R (Set.range ((↑) : s → K))) K,
    IsAlgClosure.equivOfEquiv_algebraMap]
  simp [AlgEquiv.commutes]
  rfl

theorem extendEmb_holds : ExtendEmb := by
  intro M hM ρ
  haveI := hM
  have hR : Cardinal.mk M ≤ Cardinal.aleph0 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max ℚ M).trans (max_le Cardinal.mk_le_aleph0 le_rfl)
  obtain ⟨σ, hσ⟩ := extEmb_equiv_comp (M.val.toRingHom : M →+* ℂ) (ρ.toRingHom : M →+* ℂ) hR
    (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum) rfl
  exact ⟨σ, fun x => hσ x⟩

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
