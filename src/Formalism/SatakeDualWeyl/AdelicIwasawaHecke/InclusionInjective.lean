module

public import Formalism.SatakeDualWeyl.Statement
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

noncomputable section

open Matrix TensorProduct

namespace Formalism.UG.P

open Formalism.UG

theorem bc_coe {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]
    (φ : A →+* B) (g : GL n A) : ((bc φ g : GL n B) : Matrix n n B) = (g : Matrix n n A).map φ :=
  by simp [bc]

theorem incl_cT_map {A B : Type} [CommRing A] [CommRing B] {m p : Type}
    (σ : A →+* A) (σ' : B →+* B) (φ : A →+* B) (h : φ.comp σ = σ'.comp φ) (M : Matrix m p A) :
    cT σ' (M.map φ) = (cT σ M).map φ := by
  ext i j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  exact (RingHom.congr_fun h (M j i)).symm

theorem bc_mem {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]
    (σ : A →+* A) (σ' : B →+* B) (φ : A →+* B) (h : φ.comp σ = σ'.comp φ)
    (J : Matrix n n A) (g : GL n A) (hg : g ∈ UJ σ J) : bc φ g ∈ UJ σ' (J.map φ) := by
  have hg' : cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  show cT σ' ((bc φ g : GL n B) : Matrix n n B) * J.map φ * ((bc φ g : GL n B) : Matrix n n B) = J.map φ
  rw [bc_coe, incl_cT_map σ σ' φ h, ← Matrix.map_mul, ← Matrix.map_mul, hg']

theorem inclE_injective (F E : Type) [Field F] [CommRing E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] [Nontrivial R] :
    Function.Injective (inclE (F := F) (E := E) R) := by
  intro x y hxy
  apply Algebra.TensorProduct.includeLeft_injective (S := F) (A := E) (B := R)
    (algebraMap F R).injective
  exact hxy

theorem UG_inclusion_injective : Formalism.UG.InclInj := by
  intro F E _ _ _ n _ _ R _ _ hR
  haveI := hR
  intro g g' hgg
  apply Units.ext
  have h1 := congrArg Units.val hgg
  rw [bc_coe, bc_coe] at h1
  ext i j
  exact inclE_injective F E R (congrFun (congrFun h1 i) j)

end Formalism.UG.P
