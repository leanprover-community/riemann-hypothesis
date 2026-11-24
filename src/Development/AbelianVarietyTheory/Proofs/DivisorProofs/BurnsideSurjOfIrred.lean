module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfIrreducible
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.CompanionTheory.Burnside

theorem mem_of_irred {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : Subalgebra K (Module.End K V))
    (hirr : ∀ N : Submodule K V, (∀ f ∈ S, ∀ v ∈ N, f v ∈ N) → N = ⊥ ∨ N = ⊤)
    (f : Module.End K V) : f ∈ S := by
  first
  | exact @_root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible
  | exact _root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible
  | (apply _root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible <;> assumption)
  | (intros; apply _root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible ..)

theorem burnside_surj_of_irred {A V : Type} [Ring A] [Algebra ℂ A] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : A →ₐ[ℂ] Module.End ℂ V) (hirr : ∀ W : Submodule ℂ V, (∀ h, ∀ w ∈ W, ρ h w ∈ W) → W = ⊥ ∨ W = ⊤) :
    Function.Surjective ρ := by
  intro f
  have h := mem_of_irred ρ.range (fun N hN => hirr N fun a w hw => hN (ρ a) ⟨a, rfl⟩ w hw) f
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha⟩

end GlobalTheory.CompanionTheory.Burnside
