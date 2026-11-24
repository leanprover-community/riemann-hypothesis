module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.FractionRing
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

@[expose] public section

namespace Formalism.L2.G

open Module

theorem finrank_span_le {O Kf W : Type} [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [IsFractionRing O Kf]
    [AddCommGroup W] [Module Kf W] [Module O W] [IsScalarTower O Kf W] (M : Submodule O W) [Module.Finite O M] :
    Module.rank Kf (Submodule.span Kf (M : Set W)) ≤ (Module.finrank O M : Cardinal) := by
  obtain ⟨b, hbM, hspan, hli⟩ := exists_linearIndependent Kf (M : Set W)
  rw [← hspan, rank_span_set hli]

  have hinj : Function.Injective fun r : O => r • (1 : Kf) := by
    simpa [Algebra.smul_def] using IsFractionRing.injective O Kf
  have hliO : LinearIndependent O (fun x : b => (x : W)) := hli.restrict_scalars hinj
  let w : b → M := fun x => ⟨x, hbM x.2⟩
  have hliw : LinearIndependent O w := LinearIndependent.of_comp M.subtype hliO
  have h1 := hliw.cardinal_le_rank
  have h2 : Module.rank O M < Cardinal.aleph0 := Module.rank_lt_aleph0 O M
  rw [Module.finrank, Cardinal.cast_toNat_of_lt_aleph0 h2]
  exact h1

theorem mem_span_of_card {O Kf W ι : Type} [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [IsFractionRing O Kf]
    [AddCommGroup W] [Module Kf W] [Module O W] [IsScalarTower O Kf W] (M : Submodule O W) [Module.Finite O M]
    [Fintype ι] (c : ι → W) (hli : LinearIndependent Kf c) (hc : ∀ i, c i ∈ Submodule.span Kf (M : Set W))
    (hcard : Fintype.card ι = Module.finrank O M) (F : W) (hF : F ∈ M) : F ∈ Submodule.span Kf (Set.range c) := by
  by_contra hF'
  have hli2 : LinearIndependent Kf (fun o : Option ι => Option.casesOn' o F c) :=
    linearIndependent_option'.mpr ⟨hli, hF'⟩
  let S := Submodule.span Kf (M : Set W)
  have hmem : ∀ o : Option ι, Option.casesOn' o F c ∈ S := by
    intro o
    cases o with
    | none => exact Submodule.subset_span hF
    | some i => exact hc i
  let w : Option ι → S := fun o => ⟨_, hmem o⟩
  have hliw : LinearIndependent Kf w := LinearIndependent.of_comp S.subtype hli2

  have h1 := hliw.cardinal_le_rank.trans (finrank_span_le (Kf := Kf) M)
  rw [Cardinal.mk_fintype, Fintype.card_option] at h1
  norm_cast at h1
  omega

end Formalism.L2.G
