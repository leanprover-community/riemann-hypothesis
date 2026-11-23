module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.MemPowEqv
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

theorem UpperTheory.V.ZK.Cl.cGtNe :
    UpperTheory.V.ZK.Cl.CGtNe := by
  intro hS L F _ _ _ _ _ J _ q _ ζ χ η 𝔡 h
  classical
  have hsum : ∀ x : ZMod q, ∑ i : {j // χ j = x}, η i.1 = 0 := by
    intro x
    have h1 : η.mapDomain χ x = 0 := by rw [h]; rfl
    rw [Finsupp.mapDomain, Finsupp.sum_fintype _ _ (by simp), Finsupp.finsetSum_apply] at h1
    rw [← h1, ← Finset.sum_subtype (Finset.univ.filter fun j => χ j = x) (by simp) (fun j => η j), Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finsupp.single_apply]
  have hex : ∀ x : ZMod q, ∃ g : ({j // χ j = x} → F) ≃ₗ[F] ({j // χ j = x} → F), LinearEquiv.det g = 1 ∧
      ∀ w, InLat 0 w ↔ InLat (fun i : {j // χ j = x} => η i.1 • 𝔡) (g w) := by
    intro x
    refine hS F {j // χ j = x} 0 (fun i => η i.1 • 𝔡) 1 (Or.inr rfl) fun P => ?_
    simp only [Pi.zero_apply, Finsupp.coe_zero, sub_zero, Finsupp.smul_apply, smul_eq_mul]
    rw [← Finset.sum_mul, hsum, zero_mul]
    simp [ordP]
  choose g' hdet hlat using hex
  obtain ⟨⟨g, hg⟩, hall⟩ := cBlock L F J (ZMod q) (fun _ => 1) χ g'
  refine ⟨g, (hall g hg).2.2 _ (fun j => η j • 𝔡) (fun j P => ?_) hlat, fun _ => 1, χ, g', hg, fun j => ?_, hdet⟩
  · rw [(cAct L F).2.2.1]
  · congr 1
