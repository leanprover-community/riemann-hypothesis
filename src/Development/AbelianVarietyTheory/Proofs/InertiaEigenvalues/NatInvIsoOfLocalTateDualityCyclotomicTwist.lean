module

public import Formalism.GaloisCohomology.LocalTateDualityK
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EveryGeneratorH2TwistStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivDvrFgModuleStructureStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGeneratorH2TwistStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearMapContinuousOfCompactSpaceOfFiniteStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract

@[expose] public section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory

theorem natInvIso_of_localTateDuality (hT : Formalism.GaloisCohomology.LocalTateDualityK) : NatInvIso := by
  intro p _ K O _ _ _ _ G _ _ hK hO i ε hε
  haveI := hO.ring; haveI := hO.compact; haveI := hO.t2
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_generator_H2_twist hT hK hO i hε
  have hq := GlobalTheory.T.every_generator_H2_twist hT hK hO i hε z hz
  have hbij : ∀ (M : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
      [ContinuousConstSMul O M] [ContinuousSMul O M] [T2Space M] [Module.Finite O M],
      Function.Bijective (phi ε z M) := by
    intro M _ _ _ _ _ _ _ _
    obtain ⟨n, m, e, ⟨E⟩⟩ := GlobalTheory.T.exists_equiv_dvr_fg_module_structure (O := O) M
    refine bijective_of_retract ε z M (fun _ : Fin n => O) (fun i : Fin m => O ⧸ IsLocalRing.maximalIdeal O ^ e i)
      (fun j => LinearMap.proj j ∘ₗ LinearMap.fst O _ _ ∘ₗ E.toLinearMap)
      (fun j => E.symm.toLinearMap ∘ₗ LinearMap.inl O _ _ ∘ₗ LinearMap.single O (fun _ : Fin n => O) j)
      (fun i => LinearMap.proj i ∘ₗ LinearMap.snd O _ _ ∘ₗ E.toLinearMap)
      (fun i => E.symm.toLinearMap ∘ₗ LinearMap.inr O _ _ ∘ₗ
        LinearMap.single O (fun i : Fin m => O ⧸ IsLocalRing.maximalIdeal O ^ e i) i)
      (fun j => GlobalTheory.T.continuous_linearMap_of_finite _) (fun j => GlobalTheory.T.continuous_linearMap_of_finite _) (fun i => GlobalTheory.T.continuous_linearMap_of_finite _) (fun i => ?_) ?_
      (fun j => ?_) (fun i => hq (e i))
    · have := GlobalTheory.T.continuous_linearMap_of_finite (M := O) (M' := M) ((E.symm.toLinearMap ∘ₗ LinearMap.inr O _ _ ∘ₗ
        LinearMap.single O (fun i : Fin m => O ⧸ IsLocalRing.maximalIdeal O ^ e i) i) ∘ₗ
          (IsLocalRing.maximalIdeal O ^ e i).mkQ)
      exact (Submodule.isOpenQuotientMap_mkQ _).isQuotientMap.continuous_iff.2 this
    · intro x
      conv_rhs => rw [← E.symm_apply_apply x]

      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, ← map_sum, ← map_add (f := _)]
      congr 1
      ext <;> simp [Finset.univ_sum_single]
    · show Function.Bijective (phi ε z O)
      rw [show ⇑(phi ε z O) = fun a : O => a • z from funext (phi_self ε z)]
      exact hz
  refine ⟨⟨fun M _ _ _ _ _ h => by
      haveI := h.csmul; haveI := h.t2; haveI := h.fg
      exact (LinearEquiv.ofBijective (phi ε z M) (hbij M)).symm, ?_⟩⟩
  intro M M' _ _ _ _ _ _ _ _ _ _ h h' f hf w
  haveI := h.csmul; haveI := h.t2; haveI := h.fg
  haveI := h'.csmul; haveI := h'.t2; haveI := h'.fg
  obtain ⟨m, rfl⟩ := (hbij M).2 w
  show (LinearEquiv.ofBijective (phi ε z M') (hbij M')).symm _ =
    f ((LinearEquiv.ofBijective (phi ε z M) (hbij M)).symm _)
  rw [phi_natural ε z M M' f hf (twist_map ε f) m]
  rw [LinearEquiv.ofBijective_symm_apply_apply, LinearEquiv.ofBijective_symm_apply_apply]

end GlobalTheory
