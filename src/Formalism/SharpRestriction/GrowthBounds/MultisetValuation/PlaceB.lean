module

public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X)

def EntB (j : ℕ) (i0 : X.Pl → ℕ) (g : ℝ) : Prop :=
  ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (φ : Y.Frm j La La') (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
      Y.geC (AddMonoidAlgebra.coeff (applyD (X.PI j I i0) (X.ThZA Y.Kc j (Y.ThA j La La' φ))) n) g

def TtL (j : ℕ) (i0 : X.Pl → ℕ) (vs : List X.Pl) (F : X.Fm j) : X.Fm j :=
  vs.foldr (fun v F' => X.Tt v (i0 v) j F') F

def FormB : Prop :=
  ∀ j < X.mm, ∀ (i0 : X.Pl → ℕ) (vs : List X.Pl) (g : ℝ), vs.Nodup → (∀ v, i0 v ≤ X.G.P.r) →
    (∀ v, v ∉ vs → i0 v = 0) → EntB X Y j i0 g →
    ∀ G ∈ X.Int j, X.vGe (j + 1) (TtL X (j + 1) i0 vs (X.Kz j G)) (g - X.dG j)

def PlaceB (j : ℕ) (v : X.Pl) (i : ℕ) (g : ℝ) : Prop :=
  (i = 0 ∧ (Y.LowAt j v g ∨ g ≤ X.gv v (j + 1) - X.alEven v)) ∨ (1 ≤ i ∧ i ≤ X.G.P.r ∧ g ≤ X.gv v (j + 1))

end Formalism.MainNotions.FormalGroupSystem.Pf
