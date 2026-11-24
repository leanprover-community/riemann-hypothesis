module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.ZModInj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Group.AddChar

@[expose] public section

namespace KStar.Selmer

open Matrix Module

variable {N : ℕ} [NeZero N] {M M' : Type*} [AddCommGroup M] [Module (ZMod N) M] [AddCommGroup M']
  [Module (ZMod N) M']

private theorem finite_dual [Finite M] : Finite (Module.Dual (ZMod N) M) :=
  Finite.of_injective (fun f : Module.Dual (ZMod N) M => (f : M → ZMod N)) DFunLike.coe_injective

private theorem card_dual_le [Finite M] : Nat.card (Module.Dual (ZMod N) M) ≤ Nat.card M := by
  haveI := finite_dual (N := N) (M := M)
  haveI := Fintype.ofFinite M
  let Φ : Module.Dual (ZMod N) M → AddChar M ℂ := fun f =>
    ZMod.stdAddChar.compAddMonoidHom f.toAddMonoidHom
  have hΦ : Function.Injective Φ := by
    intro f g h
    ext m
    have := DFunLike.congr_fun h m
    simp only [Φ, AddChar.compAddMonoidHom_apply] at this
    exact ZMod.injective_stdAddChar this
  calc Nat.card (Module.Dual (ZMod N) M) ≤ Nat.card (AddChar M ℂ) :=
        Nat.card_le_card_of_injective Φ hΦ
    _ = Nat.card M := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]

private theorem eval_inj : Function.Injective (Module.Dual.eval (ZMod N) M) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro m hm
  by_contra hne
  obtain ⟨f, -, hf⟩ := exists_form_ne_zero (⊥ : Submodule (ZMod N) M) (z := m)
    (by simpa using hne)
  exact hf (by simpa using DFunLike.congr_fun (LinearMap.mem_ker.1 hm) f)

theorem card_dual [Finite M] : Nat.card (Module.Dual (ZMod N) M) = Nat.card M := by
  refine le_antisymm card_dual_le ?_
  have h1 : Finite (Module.Dual (ZMod N) M) := finite_dual
  have h2 : Finite (Module.Dual (ZMod N) (Module.Dual (ZMod N) M)) := finite_dual
  exact (Nat.card_le_card_of_injective _ (eval_inj (N := N) (M := M))).trans card_dual_le

end KStar.Selmer
