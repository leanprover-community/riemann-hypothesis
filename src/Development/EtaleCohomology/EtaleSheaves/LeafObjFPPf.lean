module

public import Development.EtaleCohomology.EtaleSheaves.LeafDescendFPPf
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf

namespace LateralTheory.E.LeafObjFPPf

def Desc (k : Type) [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (f : X ⟶ Sp Ω) : Prop :=
  ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D : Scheme.{0}) (q : D ⟶ Sp R) (v : X ⟶ D),
    FP q ∧ IsPullback v f q (toR R)

def LeafObjAff : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), IsAffine X → FP f → Desc k f

def LeafObjGlue : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), FP f → ∀ (U V : X.Opens), U ⊔ V = ⊤ →
    Desc k (U.ι ≫ f) → Desc k (V.ι ≫ f) → Desc k ((U ⊓ V).ι ≫ f) → Desc k f

def LeafQCQSInduct : Prop := ∀ (S : Scheme.{0}) [IsAffine S] (P : ∀ {X : Scheme.{0}}, (X ⟶ S) → Prop),
    (∀ {X : Scheme.{0}} (f : X ⟶ S), IsAffine X → FP f → P f) →
    (∀ {X : Scheme.{0}} (f : X ⟶ S), FP f → ∀ (U V : X.Opens), U ⊔ V = ⊤ →
      P (U.ι ≫ f) → P (V.ι ≫ f) → P ((U ⊓ V).ι ≫ f) → P f) →
    ∀ {X : Scheme.{0}} (f : X ⟶ S), FP f → P f

theorem objectDescent_of_affineDescent (hA : LeafObjAff) (hG : LeafObjGlue) (hI : LeafQCQSInduct) : LeafObjFP := by
  intro k _ Ω _ _ X f hf
  exact hI (Sp Ω) (fun g => Desc k g) (fun g hX hg => hA k Ω g hX hg)
    (fun g hg U V hUV h1 h2 h3 => hG k Ω g hg U V hUV h1 h2 h3) f hf

end LateralTheory.E.LeafObjFPPf

end
