module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerEqCentralizer
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.Set.Finite.Lattice

@[expose] public section

open GlobalTheory.OrbitUnfold GlobalTheory.OrbitUnfold.ConjSelf

namespace GlobalTheory.OrbitUnfold

theorem finite_support_pairTerm :
    ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ),
      (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) →
      (∀ y : Y, (Function.support (F y)).Finite) →
      {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite →
      (Function.support (fun o : MulAction.orbitRel.Quotient Γ (Y × ConjSelf Γ) =>
        pairTerm F (Quotient.out o))).Finite := by
  intro Γ Y _ _ F hF hfin hS
  refine (hS.biUnion (t := fun o' =>
      (fun γ : Γ => (Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) (Quotient.out o', of γ))) ''
        Function.support (F (Quotient.out o'))) (fun o' _ => (hfin _).image _)).subset ?_
  intro o ho
  have hne : F (Quotient.out o).1 (val (Quotient.out o).2) ≠ 0 := by
    intro h
    apply ho
    simp [pairTerm, h]
  set p := Quotient.out o with hp
  set o' : MulAction.orbitRel.Quotient Γ Y := Quotient.mk (MulAction.orbitRel Γ Y) p.1 with ho'
  obtain ⟨η, hη⟩ := Quotient.exact (Quotient.out_eq o')
  change η • p.1 = Quotient.out o' at hη
  have hval : F (Quotient.out o') (η * val p.2 * η⁻¹) ≠ 0 := by
    rw [← hη, hF]; exact hne
  refine Set.mem_biUnion (x := o') ⟨_, hval⟩ ⟨η * val p.2 * η⁻¹, hval, ?_⟩
  have hsm : (η • p : Y × ConjSelf Γ) = (Quotient.out o', of (η * val p.2 * η⁻¹)) := by
    rw [Prod.smul_def, hη]; rfl
  show Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) (Quotient.out o', of (η * val p.2 * η⁻¹)) = o
  rw [← hsm]
  calc Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) (η • p)
      = Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) p :=
        Quotient.sound ⟨η, rfl⟩
    _ = o := by rw [hp]; exact Quotient.out_eq o

end GlobalTheory.OrbitUnfold
