module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Formalism.LocalToGlobal.ProjectiveLattices.IsThRule
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs
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

@[expose] public section

noncomputable section

namespace UpperTheory.Depth

open NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def SplitAt (d p : ℕ) : Prop := p = 2 ∨ jacobiSym (-(d : ℤ)) p = 1

def SplitPlaces (p : ℕ) [Fact p.Prime] (H : Host E) (f : ℕ) (vd : ℝ) : Prop :=
  letI := H.starRing
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C],
    v.Integers O → ∀ [Fact (¬ IsUnit (p : O))] [Algebra ℤ_[p] O] (τO : (E →+* ℂ) → (𝓞 E →+* O)),
    Function.Injective τO → (∀ τ τ', τ (H.rt : E) = τ' (H.rt : E) ↔ τO τ H.rt = τO τ' H.rt) →
    ∃ (s : ℕ) (w : Fin s → Place p (𝓞 E)) (vdi : Fin s → ℝ),
      ∑ i, (w i).n = f ∧ ∑ i, ((w i).n : ℝ) * vdi i = (f : ℝ) * vd ∧
      (∀ i σ, σ ∈ Emb (O := O) (w i).e → ∃ τ, InPsi H τ ∧ σ = τO τ) ∧
      (∀ τ, InPsi H τ → ∃! i, τO τ ∈ Emb (O := O) (w i).e) ∧
      (∀ i σ, σ ∈ Emb (O := O) (w i).bar → ∃ τ, ¬ InPsi H τ ∧ σ = τO τ) ∧
      ∀ i, ∃ t : Fin (w i).n ≃ Emb (O := O) (w i).e, HasVd p v (w i) t (vdi i)

end UpperTheory.Depth

end
