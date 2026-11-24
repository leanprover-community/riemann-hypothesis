module

public import Development.DiscreteGroups.GlobalIrreducibility.DzTypeCut
public import Development.DiscreteGroups.GlobalIrreducibility.ExistsOfMemKOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem lDepth : LDepth := by
  intro E _ _ w g _ i hi n τ σ hs
  obtain ⟨φ, hφ, hφe⟩ := hs
  obtain ⟨u, hu⟩ : ∃ u, φ u ≠ 0 := by
    by_contra h
    exact hφ (LinearMap.ext fun u => not_not.1 fun hne => h ⟨u, hne⟩)
  let e := equivRep σ
  have hfix : ∀ m ∈ KOne (w.adicCompletion E) (Fin n), σ.ρ m (φ u) = φ u := by
    intro m hm
    obtain ⟨k, hk, rfl⟩ := DiscreteGroups.sglob.DzIso.exists_of_mem_KOne i hi hm
    have := hφe k u
    rw [hk, map_one, Module.End.one_apply] at this
    exact this.symm
  intro hbot
  have hv : e.toIntertwiningMap (φ u) ∈ fixed (cls σ).rep (KOne (w.adicCompletion E) (Fin (cls σ).1)) := by
    intro m
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    rw [← e.toIntertwiningMap.isIntertwining, hfix m m.2]
  rw [hbot, Submodule.mem_bot] at hv
  have h2 : e.toLinearEquiv (φ u) = 0 := hv
  exact hu (e.toLinearEquiv.injective (h2.trans (map_zero _).symm))

end DiscreteGroups.sglob.DzType
