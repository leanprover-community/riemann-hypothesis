module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Formalism.LocalRingCardinality.DataTheta
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem chain_length_le_finrank_add_one : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (G U C : Submodule ℂ V), FiniteDimensional ℂ U → G ≤ U ⊔ C → ∀ (m : ℕ) (N : Fin m → Submodule ℂ V), StrictMono N → (∀ k, C ≤ N k) → (∀ k l, k < l → ∃ v ∈ N l, v ∈ G ∧ v ∉ N k) → m ≤ Module.finrank ℂ U + 1 := by
  intro V _ _ G U C hU hGUC m N hN hC hsep
  let g : Fin m → Submodule ℂ U := fun k => (N k).comap U.subtype
  have hg : StrictMono g := by
    intro k l hkl
    refine lt_of_le_of_ne (fun x hx => hN.monotone hkl.le hx) ?_
    intro heq
    obtain ⟨v, hvl, hvG, hvk⟩ := hsep k l hkl
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.mp (hGUC hvG)
    have hcl : c ∈ N l := hC l hc
    have hul : u ∈ N l := by simpa using (N l).sub_mem hvl hcl
    have hmem : (⟨u, hu⟩ : U) ∈ g l := hul
    rw [← heq] at hmem
    exact hvk ((N k).add_mem hmem (hC k hc))
  let f : Fin m → Fin (Module.finrank ℂ U + 1) := fun k =>
    ⟨Module.finrank ℂ (g k), Nat.lt_succ_of_le (Submodule.finrank_le _)⟩
  have hf : Function.Injective f := by
    intro k l h
    have h' : Module.finrank ℂ (g k) = Module.finrank ℂ (g l) := congrArg Fin.val h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (ne_of_lt (Submodule.finrank_lt_finrank_of_lt (hg hlt))) h'
    · exact (ne_of_lt (Submodule.finrank_lt_finrank_of_lt (hg hlt))) h'.symm
  simpa using Fintype.card_le_of_injective f hf

end GlobalTheory.HoweR
