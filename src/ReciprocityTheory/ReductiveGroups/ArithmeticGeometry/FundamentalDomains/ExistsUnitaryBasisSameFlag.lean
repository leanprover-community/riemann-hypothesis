module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UbasisAt

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Matrix
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

def Jt (x : Frame X.Ψ r) (τ : X.Ψ) (v : Fin r → ℂ) : Fin r → ℂ :=
  I • ((2 : ℂ) • X.ppos x τ v - v)

def UBasis (z0 : Frame X.Ψ r) (ξ : Fin r → E) (f : X.Ψ → Fin (r - 2) → Fin r → ℂ) : Prop :=
  ∀ τ : X.Ψ,
    (∀ k, hermC τ.1 X.Gm (f τ k) (emb τ.1 ξ) = 0 ∧ hermC τ.1 X.Gm (X.Jt z0 τ (f τ k)) (emb τ.1 ξ) = 0) ∧
    (∀ k, X.Jt z0 τ (f τ k) = (if (k : ℕ) < X.p0 - 1 then I else -I) • f τ k) ∧
    (∀ k l, hermC τ.1 X.Gm (f τ k) (f τ l) =
      if k = l then (if (k : ℕ) < X.p0 - 1 then 1 else -1) else 0) ∧
    (∀ c : Fin (r - 2) → ℂ, X.maj z0 τ (∑ k, c k • f τ k) = ∑ k, ‖c k‖ ^ 2) ∧
    (∀ v : Fin r → ℂ, hermC τ.1 X.Gm v (emb τ.1 ξ) = 0 → hermC τ.1 X.Gm (X.Jt z0 τ v) (emb τ.1 ξ) = 0 →
      v ∈ Submodule.span ℂ (Set.range (f τ)))

end Data

theorem exists_unitary_basis_same_flag (r : ℕ) (X : DataX E r) (ξ : Fin r → E) (z0 x0 : Frame X.Ψ r) (hξ : X.IsIso ξ)
    (hz : z0 ∈ X.dom) (hx0 : x0 ∈ X.dom) (hortho : X.IsOrtho x0) (hflag : X.SameFlag z0 x0) :
    ∃ f : X.Ψ → Fin (r - 2) → Fin r → ℂ, X.UBasis z0 ξ f := by

  choose f hf using fun τ : X.Ψ =>
    OrthonormalPerpBasis.ubasis_at (X := X.toData) ξ z0 x0 hξ.2.2 hξ.2.1 hz hx0 hortho hflag τ
  exact ⟨f, fun τ => hf τ⟩

end

end ReciprocityTheory.ChartRestriction.G.FD
