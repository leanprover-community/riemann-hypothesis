module

public import Development.AutomorphicArithmetic.IntegralCasts.TransposeInverse.TransposeInv
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsOpenStabilizer
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open Matrix

namespace GlobalTheory.CuspRep

abbrev BlockIx (a r : ℕ) := {p : Fin a × Fin a // p.1.val < r ∧ r ≤ p.2.val}

section
variable {a : ℕ} {R : Type} [CommRing R]

def nilM {r : ℕ} (x : BlockIx a r → R) : Matrix (Fin a) (Fin a) R :=
  Matrix.of fun i j => if h : i.val < r ∧ r ≤ j.val then x ⟨(i, j), h⟩ else 0

theorem nilM_mul_self {r : ℕ} (x : BlockIx a r → R) : nilM x * nilM x = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases h : l.val < r
  · simp [nilM, not_le.2 h]
  · simp [nilM, h]

theorem nilM_mul {r : ℕ} (x y : BlockIx a r → R) : nilM x * nilM y = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases h : l.val < r
  · simp [nilM, not_le.2 h]
  · simp [nilM, h]

def unip {r : ℕ} (x : BlockIx a r → R) : GL (Fin a) R where
  val := 1 + nilM x
  inv := 1 - nilM x
  val_inv := by simp [add_mul, mul_sub, nilM_mul_self]
  inv_val := by simp [sub_mul, mul_add, nilM_mul_self]

end

def invT (a : ℕ) (R : Type) [CommRing R] : GL (Fin a) R →* GL (Fin a) R :=
  (Reformulated.TransposeInverseTheory.transposeInv : GL (Fin a) R ≃* GL (Fin a) R).toMonoidHom

def twRep {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (χ : G →* ℂˣ) : Representation ℂ G V where
  toFun g := (χ g : ℂ) • ρ g
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul, Units.val_mul, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [mul_comm (χ h : ℂ)]

theorem isOpen_stab_of_mem_nhds {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : G →* Module.End ℂ V) (v : V)
    (h : {g : G | ρ g v = v} ∈ nhds (1 : G)) : IsOpen {g : G | ρ g v = v} :=
  UpperTheory.Reformulated.B.IsOpenStabilizer.isOpen_stab_of_mem_nhds ρ v h

end GlobalTheory.CuspRep
