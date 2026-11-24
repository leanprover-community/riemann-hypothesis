module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsPres
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v

theorem GradedULift.proof : GradedULift.Statement.{u, v} := by
  intro S _ N M _ _ _ _ 𝓜
  let e : M ≃ₗ[S] ULift.{u} M := (ULift.moduleEquiv (R := S)).symm
  let eP : M ≃ₗ[Poly S N] ULift.{u} M := (ULift.moduleEquiv (R := Poly S N)).symm
  let pc : ℤ → Submodule S (ULift.{u} M) := fun c => (𝓜.piece c).map (e : M →ₗ[S] ULift.{u} M)
  have hpc : ∀ c, pc c = Submodule.orderIsoMapComap e (𝓜.piece c) := fun _ => rfl
  have hint : DirectSum.IsInternal pc := by
    have h0 := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).1 𝓜.isInternal
    refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2 ⟨?_, ?_⟩
    · have : pc = (Submodule.orderIsoMapComap e) ∘ 𝓜.piece := funext hpc
      rw [this]
      exact h0.1.map_orderIso _
    · have h1 : (⨆ c, pc c) = Submodule.orderIsoMapComap e (⨆ c, 𝓜.piece c) := by
        rw [OrderIso.map_iSup]
        rfl
      rw [h1, h0.2]
      exact (Submodule.orderIsoMapComap e).map_top
  let 𝓜' : GradedPMod S N (ULift.{u} M) :=
    { piece := pc
      isInternal := hint
      smul_mem := by
        intro d c p m hp hm
        obtain ⟨x, hx, rfl⟩ := hm
        refine ⟨p • x, 𝓜.smul_mem d c p x hp hx, ?_⟩
        rfl }
  refine ⟨ULift.{u} M, inferInstance, inferInstance, inferInstance, inferInstance, 𝓜',
    ⟨eP.toLinearMap, fun c m hm => ⟨m, hm, rfl⟩⟩,
    ⟨eP.symm.toLinearMap, fun c m hm => ?_⟩, fun m => rfl, fun m => rfl⟩
  obtain ⟨x, hx, rfl⟩ := hm
  exact hx

end

end GroundTheory.Heights₂.Heights.Kleiman
