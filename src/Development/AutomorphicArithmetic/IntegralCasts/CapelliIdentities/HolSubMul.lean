module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

namespace UpperTheory.Reformulated.B.Qe28

@[reducible] noncomputable def FDSec : {E : Type} →
  [inst : Field E] →
    [inst_1 : NumberField E] →
      [inst_2 : NumberField.IsCMField E] →
        {r : ℕ} → {Comp : Type} → (Comp → ReciprocityTheory.ChartRestriction.G.FD.Data E r) → Type :=
  fun {E} [Field E] [NumberField E] [NumberField.IsCMField E] {r} {Comp} X =>
    (c : Comp) → ReciprocityTheory.ChartRestriction.G.FD.Frame (X c).Ψ r → ℂ

noncomputable def IsHolCusp : {E : Type} →
  [inst : Field E] →
    [inst_1 : NumberField E] →
      [inst_2 : NumberField.IsCMField E] →
        {r : ℕ} →
          {Comp : Type} →
            (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data E r) →
              ((c : Comp) → ReciprocityTheory.ChartRestriction.G.FD.Wt (X c).Ψ r) →
                FDSec X → Prop :=
  fun {E} [Field E] [NumberField E] [NumberField.IsCMField E] {r} {Comp} X la P => ∀ (c : Comp), P c ∈ (X c).SS (la c)

noncomputable def holSub : {E : Type} →
  [inst : Field E] →
    [inst_1 : NumberField E] →
      [inst_2 : NumberField.IsCMField E] →
        {r : ℕ} →
          {Comp : Type} →
            (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data E r) →
              ((c : Comp) → ReciprocityTheory.ChartRestriction.G.FD.Wt (X c).Ψ r) →
                Submodule ℂ (FDSec X) :=
  fun {E} [Field E] [NumberField E] [NumberField.IsCMField E] {r} {Comp} X la =>
    Submodule.span ℂ {P | IsHolCusp X la P}

theorem holSub_mul : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
  [inst_2 : NumberField.IsCMField E] {r : ℕ},
  ReciprocityTheory.ChartRestriction.G.FD.SiegelSpaceAlgebra (E := E) →
    ∀ {Comp : Type} {X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data E r}
      {la la' : (k : Comp) → ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r}
      {P Q : FDSec X},
      P ∈ holSub X la →
        Q ∈ holSub X la' →
          P * Q ∈ holSub X (la + la') := by
  intro E _ _ _ r h5 Comp X la la' P Q hP hQ
  have key : ∀ (l : (k : Comp) → ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (R : FDSec X),
      R ∈ holSub X l → IsHolCusp X l R := by
    intro l R hR
    induction hR using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact fun c => (h5 r (X c) (l c) (l c) 0).1.1
    | add x y _ _ hx hy => exact fun c => (h5 r (X c) (l c) (l c) 0).1.2.1 _ (hx c) _ (hy c)
    | smul a x _ hx => exact fun c => (h5 r (X c) (l c) (l c) 0).1.2.2 a _ (hx c)
  exact Submodule.subset_span fun c =>
    (h5 r (X c) (la c) (la' c) 0).2.1 _ (key la P hP c) _ (key la' Q hQ c).1

end UpperTheory.Reformulated.B.Qe28
