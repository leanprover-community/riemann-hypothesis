module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsStandardUnipotentRadicalBijOnNilradicalStatement
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem IsPrimitive.finsum_unipotentRadical_eq_zero (F : Type) [Field F] [Finite F] (d : ℕ)
    (φ : Module.End F (Fin d → F) → ℂ) (hφ : IsPrimitive φ) (a : ℕ) (ha : 0 < a) (had : a < d) :
    ∑ᶠ u ∈ {u : GL (Fin d) F | ∀ i j : Fin d,
      (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)},
      φ (Matrix.toLin' (u : Matrix (Fin d) (Fin d) F)) = 0 := by
  obtain ⟨A, H, hA, hH, hbij⟩ := GlobalTheory.T.exists_standardUnipotentRadical_bijOn_nilradical F d a had.le
  have hbot : A ≠ ⊥ := by
    rintro rfl
    rw [finrank_bot] at hA
    omega
  have htop : A ≠ ⊤ := by
    rintro rfl
    rw [finrank_top, Module.finrank_fin_fun] at hA
    omega
  rw [← hH, ← hφ A hbot htop 1 (fun x hx => hx)]
  refine finsum_mem_eq_of_bijOn _ hbij fun u _ => ?_
  simp only [add_sub_cancel]

end GlobalTheory.CuspGL
