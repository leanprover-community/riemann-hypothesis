module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SrcGl

variable {D : D7}

def CA (A : HSp D) : Submodule ℂ (GA D A → ℂ) where
  carrier := {φ | GlobalTheory.Unf.IsContAut A φ}
  add_mem' {φ ψ} hφ hψ := ⟨fun γ hγ g => by simp [hφ.1 γ hγ g, hψ.1 γ hγ g], hφ.2.add hψ.2⟩
  zero_mem' := ⟨fun _ _ _ => rfl, continuous_const⟩
  smul_mem' c φ hφ := ⟨fun γ hγ g => by simp [hφ.1 γ hγ g], continuous_const.mul hφ.2⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {n : Type} [Fintype n] [DecidableEq n]

theorem rep_mem_CA {A : HSp D} (α : Frame p A n) (g : GL n k) {φ : GA D A → ℂ} (h : φ ∈ CA A) : α.rep g φ ∈ CA A :=
  ⟨fun γ hγ x => by
    change φ (γ * x * α.gl g) = φ (x * α.gl g)
    rw [mul_assoc, h.1 γ hγ], h.2.comp (continuous_mul_const _)⟩

def caRep {A : HSp D} (α : Frame p A n) : Representation ℂ (GL n k) (CA A) where
  toFun g := (α.rep g).restrict fun _ h => rep_mem_CA α g h
  map_one' := by ext φ x; simp
  map_mul' g h := by ext φ x; simp

@[simp] theorem caRep_apply {A : HSp D} (α : Frame p A n) (g : GL n k) (φ : CA A) :
    ((caRep α g φ : CA A) : GA D A → ℂ) = α.rep g φ := rfl

def blkHom : Matrix n n k →* Matrix (n ⊕ Fin 1) (n ⊕ Fin 1) k where
  toFun x := fromBlocks x 0 0 1
  map_one' := by simp
  map_mul' x y := by simp [fromBlocks_multiply]

def blk : GL n k →* GL (n ⊕ Fin 1) k := Units.map blkHom

@[simp] theorem blk_val (g : GL n k) : (blk g).val = fromBlocks g.val (0 : Matrix n (Fin 1) k) 0 1 := rfl

end GlobalTheory.FinPl.SrcGl
