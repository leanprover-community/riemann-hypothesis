module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

@[expose] public section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

open ProfiniteGrp ProfiniteGrp.ProfiniteCompletion CategoryTheory in
theorem UpperTheory.V.AlgebraTools.exists_free_profinite :
    ∀ r : ℕ, ∃ (P : Type) (_ : Group P) (_ : TopologicalSpace P) (_ : IsTopologicalGroup P) (_ : CompactSpace P)
      (_ : TotallyDisconnectedSpace P) (x : Fin r → P), TopGen (Set.range x) ∧
        ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (y : Fin r → G), ∃ f : P →* G, Continuous f ∧ ∀ i, f (x i) = y i := by
  intro r
  let F : GrpCat.{0} := GrpCat.of (FreeGroup (Fin r))
  let P : ProfiniteGrp.{0} := completion F
  let η : FreeGroup (Fin r) →* P := (eta F).hom
  refine ⟨P, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    fun i => η (FreeGroup.of i), ?_, ?_⟩
  · unfold TopGen
    have hr : Set.range (fun i => η (FreeGroup.of i)) = η '' Set.range FreeGroup.of := by
      rw [← Set.range_comp]
      rfl
    rw [hr, ← MonoidHom.map_closure, FreeGroup.closure_range_of, ← MonoidHom.range_eq_map,
      MonoidHom.coe_range]
    exact denseRange (G := F)
  · intro G _ _ _ _ _ y
    let Q : ProfiniteGrp.{0} := ProfiniteGrp.of G
    let f0 : F ⟶ GrpCat.of Q := GrpCat.ofHom (FreeGroup.lift y)
    let L : P ⟶ Q := lift f0
    refine ⟨L.hom.toMonoidHom, L.hom.continuous, ?_⟩
    intro i
    have h : ((eta F) ≫ (forget₂ ProfiniteGrp GrpCat).map L).hom (FreeGroup.of i) =
        f0.hom (FreeGroup.of i) := by
      rw [lift_eta]
    exact h.trans FreeGroup.lift_apply_of
