module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.Finiteness.Defs
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
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

noncomputable section

open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace UpperTheory.KN

variable {G O : Type} (LL : Type) [Group G] [CommRing O] [Field LL] [Algebra O LL]

def actN {ι : Type} {n : ℕ} (N : ι → (G →* Matrix (Fin n) (Fin n) O)) (g : G) (v : ι → Fin n → LL) :
    ι → Fin n → LL := fun j => ((N j g).map (algebraMap O LL)).mulVec (v j)

def HasPres {X : Type} {n : ℕ} (N : X → (G →* Matrix (Fin n) (Fin n) O)) {Q : Type} [AddCommGroup Q] [Module O Q]
    (actQ : G → Q → Q) (f : G → Q) : Prop :=
  ∃ (a : ℕ) (x : Fin a → X) (E : Fin a → Fin n → LL) (Y : Submodule O (Fin a → Fin n → LL)) (_ : Y.FG)
    (hst : ∀ g, ∀ y ∈ Y, actN LL (fun j => N (x j)) g y ∈ Y)
    (hE : ∀ g, actN LL (fun j => N (x j)) g E - E ∈ Y) (φ : ↥Y →ₗ[O] Q),
    (∀ (g : G) (y : ↥Y), φ ⟨_, hst g y.1 y.2⟩ = actQ g (φ y)) ∧ ∀ g, f g = φ ⟨_, hE g⟩

end UpperTheory.KN

end
