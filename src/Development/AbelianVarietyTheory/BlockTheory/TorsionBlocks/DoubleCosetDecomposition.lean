module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
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

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelSubgroupStabilizers

open NumberField Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct

section Level

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem finMat_one : finMat σ J (1 : HA (AF F) σ J) = 1 := by
  show (((1 : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))).map _ = 1
  rw [Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem finMat_mul (g h : HA (AF F) σ J) : finMat σ J (g * h) = finMat σ J g * finMat σ J h := by
  show (((HA.mat (AF F) σ J g * HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (AF F ⊗[F] E))).map _ = _
  rw [Units.val_mul]
  exact Matrix.map_mul (f := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom)

def levelK (L : Set (Fin M → E)) : Subgroup (HA (AF F) σ J) where
  carrier := {h | ∀ y, y ∈ latHat F E L ↔ (finMat σ J h).mulVec y ∈ latHat F E L}
  one_mem' := by
    intro y
    rw [finMat_one, Matrix.one_mulVec]
  mul_mem' := by
    intro a b ha hb y
    rw [finMat_mul, ← Matrix.mulVec_mulVec]
    exact (hb y).trans (ha _)
  inv_mem' := by
    intro a ha y
    have := ha ((finMat σ J a⁻¹).mulVec y)
    rw [Matrix.mulVec_mulVec, ← finMat_mul, mul_inv_cancel, finMat_one, Matrix.one_mulVec] at this
    exact this.symm

end Level

section Space

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def latCoord (W : HSpace E) : Set (Fin W.rank → E) := {x | ∑ i, x i • W.frame i ∈ W.L0}

def levelW (hc : CMData F E) (W : HSpace E) : Subgroup (HA (AF F) hc.sig W.gram) :=
  levelK hc.sig W.gram (latCoord W)


end Space

end GlobalTheory.IndefiniteRowSideFullHecke.LevelSubgroupStabilizers
