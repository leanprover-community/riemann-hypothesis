module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.SurjOfCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtArith
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_subfamily_unique_repr_of_spanning_localRing
    (R : Type) [CommRing R] [IsLocalRing R] (M : Type) [AddCommGroup M] [Module R M] (d g : ℕ) :
    Nonempty (Module.Basis (Fin d) R M) → ∀ w : Fin g → M,
      (∀ u : M, ∃ cf : Fin g → R, u = ∑ a, cf a • w a) →
      ∃ e : Fin d → Fin g, ∀ u : M, ∃! cf : Fin d → R, u = ∑ a, cf a • w (e a) := by
  rintro ⟨b⟩ w hw
  haveI : Module.Finite R M := Module.Finite.of_basis b
  let V := IsLocalRing.ResidueField R ⊗[R] M
  let v : Fin g → V := fun a => (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] w a
  have hsp : Submodule.span (IsLocalRing.ResidueField R) (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul c m =>
      obtain ⟨cf, rfl⟩ := hw m
      have : c ⊗ₜ[R] (∑ a, cf a • w a) = c • ∑ a, cf a • v a := by
        simp only [v, TensorProduct.tmul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
          TensorProduct.smul_tmul', smul_comm c (cf a) (1 : IsLocalRing.ResidueField R),
          smul_eq_mul, _root_.mul_one]
      rw [this]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => ?_)
      exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  obtain ⟨κ, a, ha, hspa, hli⟩ := exists_linearIndependent' (IsLocalRing.ResidueField R) v
  let bk : Module.Basis κ (IsLocalRing.ResidueField R) V :=
    Module.Basis.mk hli (by rw [hspa, hsp])
  let bV : Module.Basis (Fin d) (IsLocalRing.ResidueField R) V :=
    Algebra.TensorProduct.basis (IsLocalRing.ResidueField R) b
  let eq : Fin d ≃ κ := bV.indexEquiv bk
  refine ⟨a ∘ eq, ?_⟩
  have hspR : Submodule.span R (Set.range (w ∘ a ∘ eq)) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis (w ∘ a ∘ eq) (bk.reindex eq.symm) (fun i => by
      simp [bk, v])
  let f : (Fin d → R) →ₗ[R] M := Fintype.linearCombination R (w ∘ a ∘ eq)
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact hspR
  have hfi : Function.Injective f :=
    OrzechProperty.injective_of_surjective_of_injective b.equivFun.symm.toLinearMap f
      b.equivFun.symm.injective hf
  intro u
  obtain ⟨cf, hcf⟩ := hf u
  refine ⟨cf, ?_, ?_⟩
  · rw [← hcf]; simp [f, Fintype.linearCombination_apply]
  · intro cf' hcf'
    apply hfi
    rw [hcf]; simp [f, Fintype.linearCombination_apply, hcf']

end GlobalTheory
