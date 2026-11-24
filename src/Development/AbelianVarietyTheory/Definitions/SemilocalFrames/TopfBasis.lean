module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.RowLev

open Formalism.MainNotions.S Formalism.BasicNotions NumberField Matrix
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def coordLat (W : HSpace E) : Submodule (𝓞 E) (Fin W.rank → E) :=
  W.L0.map (W.frame.equivFun.toLinearMap.restrictScalars (𝓞 E))

def congSet (cm : CMData F E) (W : HSpace E) (g : ℕ) : Set (Formalism.UG.UPts cm.sig W.gram (Af F)) :=
  {x | (x : GL (Fin W.rank) (E ⊗[F] Af F)) ∈ Formalism.UG.stabGL (lamAf (F := F) (coordLat W)) ∧
    ∀ y ∈ lamAf (F := F) (coordLat W), ∃ z ∈ lamAf (F := F) (coordLat W),
      ((x : GL (Fin W.rank) (E ⊗[F] Af F)) - 1 : Matrix (Fin W.rank) (Fin W.rank) (E ⊗[F] Af F)) *ᵥ y =
        (g : E ⊗[F] Af F) • z}

structure InstData (cm : CMData F E) (W : HSpace E) (ε : InfinitePlace F → Fin W.rank → Bool)
    (φ : InfinitePlace F → (E →+* ℂ)) where
  J_herm : Formalism.UG.IsHerm (starRingEnd E) W.gram
  J_det : W.gram.det ≠ 0
  L_span : Submodule.span E (coordLat W : Set (Fin W.rank → E)) = ⊤
  L_fg : (coordLat W).FG
  L_dual : ∀ x : Fin W.rank → E, x ∈ coordLat W ↔
    ∀ y ∈ coordLat W, Formalism.UG.hform (starRingEnd E) W.gram y x ∈ (algebraMap (𝓞 E) E).range
  φ_over : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a
  P : InfinitePlace F → Matrix (Fin W.rank) (Fin W.rank) ℂ
  P_unit : ∀ v, IsUnit (P v)
  P_spec : ∀ v, (P v)ᴴ * W.gram.map (φ v) * P v = Formalism.REAL.Jm (ε v)
  topf : TopologicalSpace (Formalism.UG.UPts cm.sig W.gram (Af F))
  topf_group : @IsTopologicalGroup _ topf _
  topf_open : ∀ g : ℕ, 1 ≤ g → @IsOpen _ topf (congSet cm W g)
  topf_basis : ∀ U ∈ @nhds _ topf 1, ∃ g : ℕ, 1 ≤ g ∧ congSet cm W g ⊆ U

end GlobalTheory.RowLev
