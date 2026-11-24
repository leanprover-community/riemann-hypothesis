module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TrueColumnTupleTrivialEqOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Cls

theorem coeffField_rootsOfUnity_typePrimes_hermitianStages : ∀ X : Stages, GlobalTheory.Core.Cls.RootsG X.toD7 := by
  intro X i
  have hp : Nat.Prime (X.B.host.g i) := X.B.host.g_prime i
  obtain ⟨z, -, hz⟩ := X.B.roots_Ks (X.B.host.g i * (X.B.host.g i - 1)) (by fin_cases i <;> simp)
  have hne : X.B.host.g i * (X.B.host.g i - 1) ≠ 0 :=
    mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)
  have hprim : IsPrimitiveRoot z (X.B.host.g i * (X.B.host.g i - 1)) := by
    refine IsPrimitiveRoot.of_map_of_injective (f := X.B.embLL) ?_ X.B.embLL.injective
    rw [hz]
    exact_mod_cast Complex.isPrimitiveRoot_exp _ hne
  have hpos : 0 < X.B.host.g i * (X.B.host.g i - 1) := Nat.pos_of_ne_zero hne
  exact ⟨⟨z ^ (X.B.host.g i - 1), hprim.pow hpos (mul_comm _ _)⟩, ⟨z ^ X.B.host.g i, hprim.pow hpos rfl⟩⟩

end GlobalTheory.Core.Cls
