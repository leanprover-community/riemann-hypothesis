module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.LocGL

theorem isLSeg_single (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ρ : IrrGL (k := k)) (hρ : ρ.IsCusp) : IsLSeg (Segment.single ρ hρ) ρ.rep := by
  have hterm : ((Segment.single ρ hρ).term : Fin 1 → IrrGL (k := k)) = fun _ => ρ := by
    funext a
    have ha : (a : ℕ) = 0 := by
      have h1 : (a : ℕ) < 1 := a.isLt
      omega
    show (Segment.single ρ hρ).first.nu ((a : ℕ) : ℂ) = ρ
    rw [ha, Nat.cast_zero, show (Segment.single ρ hρ).first = ρ from Segment.first_ofFirst ρ hρ 1 one_pos,
      IrrGL.nu_zero]
  have key : ∀ x : Fin 1 → IrrGL (k := k), x = (fun _ => ρ) → ∀ hd : ∑ a, (x a).1 = ρ.1,
      IsCosocle ρ.rep (prodIrr x hd) := by
    intro x hx hd
    subst hx
    obtain ⟨φ⟩ := nonempty_equiv_prodIrr_one ρ hd
    exact (isCosocle_self ρ.2.rep.irr).of_equiv (Representation.Equiv.refl _) φ
  have hd : ∑ a : Fin 1, ((Segment.single ρ hρ).term a).1 = ρ.1 := by
    rw [hterm]
    simp
  exact ⟨hd, key _ hterm hd⟩

end GlobalTheory.CompanionTheory.LocGL
