module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum
open Pointwise

private theorem hom_one {Γ M : Type} [Group Γ] [AddCommGroup M] {f : Γ → M} (hf : ∀ a b, f (a * b) = f a + f b) :
    f 1 = 0 := by
  have := hf 1 1
  rw [one_mul] at this
  exact left_eq_add.1 this

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

private theorem zm_triv (D : LData F Ω l) (r : ℕ) (g) (m : ZMod (l ^ r)) : zmTw D r 0 g m = m := by simp [zmTw]

private theorem mem_iff (D : LData F Ω l) (r : ℕ) (z : Z1 (zmTw D r 0)) :
    (Submodule.Quotient.mk z : H1 (zmTw D r 0)) ∈ ShaZm D r 0 ↔
      ∀ v : D.S, ∀ g ∈ Dec (F := F) (D.A v), z.1 (toGS Ω _ g) = 0 := by
  refine (Submodule.mem_iInf _).trans (forall_congr' fun v => ?_)
  refine ((Submodule.Quotient.mk_eq_zero _).trans (mem_coboundaries1 _ _)).trans ⟨fun ⟨m, hm⟩ g hg => ?_, fun h => ⟨0, fun g => ?_⟩⟩
  · exact (hm ⟨g, hg⟩).trans (sub_eq_zero.2 (zm_triv D r _ m))
  · exact (h g.1 g.2).trans (sub_eq_zero.2 (zm_triv D r _ 0)).symm

end
