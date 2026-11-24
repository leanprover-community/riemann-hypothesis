module

public import Mathlib.NumberTheory.Padics.PadicIntegers
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Formalism.WeaklyAdmissibleFiltrations.Statement

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology



namespace GlobalTheory

theorem linearMap_pi_continuous_coord : ∀ {l : ℕ} [Fact l.Prime] {O M ι : Type}
    [CommRing O] [Algebra ℤ_[l] O] [Fintype ι] [AddCommGroup M] [Module O M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] {e : ℕ} (bO : Module.Basis (Fin e) ℤ_[l] O),
    (∀ m : M, Continuous fun c : ℤ_[l] => algebraMap ℤ_[l] O c • m) →
    ∀ f : (ι → O) →ₗ[O] M,
      @Continuous (ι → O) M
        (Pi.topologicalSpace (t₂ := fun _ => TopologicalSpace.induced bO.equivFun inferInstance))
        inferInstance f := by
  intro l _ O M ι _ _ _ _ _ _ _ e bO hcont f
  classical
  letI : TopologicalSpace O := TopologicalSpace.induced bO.equivFun inferInstance
  have key : ∀ c : ι → O, f c = ∑ i, ∑ α, algebraMap ℤ_[l] O (bO.equivFun (c i) α) • (bO α • f (Pi.single i 1)) := by
    intro c
    rw [LinearMap.pi_apply_eq_sum_univ f c]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hc : (fun j => if i = j then (1:O) else 0) = Pi.single i 1 := by
      funext j; by_cases h : i = j <;> simp [Pi.single_apply, h, eq_comm]
    rw [hc]
    conv_lhs => rw [← bO.sum_equivFun (c i)]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Algebra.smul_def, mul_smul]
  have hf : (f : (ι → O) → M) = fun c => ∑ i, ∑ α, algebraMap ℤ_[l] O (bO.equivFun (c i) α) • (bO α • f (Pi.single i 1)) := funext key
  rw [hf]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun α _ => ?_
  exact (hcont _).comp ((continuous_apply α).comp (continuous_induced_dom.comp (continuous_apply i)))

end GlobalTheory
