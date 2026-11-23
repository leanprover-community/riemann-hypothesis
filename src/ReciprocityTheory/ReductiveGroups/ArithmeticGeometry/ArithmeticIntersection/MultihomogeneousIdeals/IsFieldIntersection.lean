module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AI.I1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

section Algebra

variable {F : Type*} [Field F]

def IsProjVarF (V : Ideal (MRingOver F ι)) (d : ℕ) : Prop :=
  IsMultiProjPrime V ∧ ringKrullDim (MRingOver F ι ⧸ V) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)

def ratDiv (V : Ideal (MRingOver F ι)) (f g : MRingOver F ι) : Ideal (MRingOver F ι) →₀ ℤ :=
  Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (divCycle V f) -
    Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (divCycle V g)

def IsRatSection (V : Ideal (MRingOver F ι)) (a : K → ℤ) (f g : MRingOver F ι) : Prop :=
  ∃ α β : K → ℕ, IsMultiHomog f α ∧ IsMultiHomog g β ∧ f ∉ V ∧ g ∉ V ∧
    ∀ k, (α k : ℤ) - β k = a k

def IsChart (V : Ideal (MRingOver F ι)) (i : ∀ k, ι k) : Prop :=
  ∀ k, (X ⟨k, i k⟩ : MRingOver F ι) ∉ V

def chartIdeal (V : Ideal (MRingOver F ι)) (i : ∀ k, ι k) : Ideal (MRingOver F ι) :=
  V ⊔ Ideal.span (Set.range fun k => (X ⟨k, i k⟩ : MRingOver F ι) - 1)

def ptDeg (V : Ideal (MRingOver F ι)) (i : ∀ k, ι k) : ℕ :=
  Module.finrank F (MRingOver F ι ⧸ chartIdeal V i)

abbrev IFamily (F : Type*) [Field F] (κ : K → Type*) := Ideal (MRingOver F κ) → (n : ℕ) → (Fin n → K → ℤ) → ℤ

def cycEval (J : Ideal (MRingOver F ι) → ℤ) (D : Ideal (MRingOver F ι) →₀ ℤ) : ℤ :=
  D.sum fun W m => m * J W

def IsFieldIntersection (I : IFamily F ι) : Prop :=
  (∀ (V : Ideal (MRingOver F ι)) (L : Fin 0 → K → ℤ) (i : ∀ k, ι k),
      IsProjVarF V 0 → IsChart V i → I V 0 L = ptDeg V i) ∧
  (∀ (V : Ideal (MRingOver F ι)) (n : ℕ) (L : Fin n → K → ℤ) (A : K → ℤ) (f g : MRingOver F ι),
      IsProjVarF V (n + 1) → IsRatSection V A f g →
      I V (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L A) = cycEval (fun W => I W n L) (ratDiv V f g))

end Algebra

section Morphisms

variable {F : Type*} [Field F] {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]

def IsBlockMap (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) : Prop :=
  Function.Injective κ ∧ Function.Injective v ∧ (∀ p, (v p).1 = κ p.1) ∧
    ∀ q : Σ k', ι' k', q.1 ∈ Set.range κ → q ∈ Set.range v


variable (F) in
def imageVar (v : (Σ k, ι k) → (Σ k', ι' k')) (V' : Ideal (MRingOver F ι')) : Ideal (MRingOver F ι) :=
  V'.comap (rename v : MRingOver F ι →ₐ[F] MRingOver F ι').toRingHom

def pullDeg (κ : K → K') (a : K → ℤ) : K' → ℤ :=
  Function.extend κ a 0

def chartMap (v : (Σ k, ι k) → (Σ k', ι' k')) (V' : Ideal (MRingOver F ι')) (i' : ∀ k', ι' k') :
    MRingOver F ι ⧸ (chartIdeal V' i').comap (rename v : MRingOver F ι →ₐ[F] MRingOver F ι').toRingHom →+*
      MRingOver F ι' ⧸ chartIdeal V' i' :=
  Ideal.quotientMap _ (rename v : MRingOver F ι →ₐ[F] MRingOver F ι').toRingHom le_rfl

def fnDeg (v : (Σ k, ι k) → (Σ k', ι' k')) (V' : Ideal (MRingOver F ι')) (i' : ∀ k', ι' k') : ℕ :=
  letI := (chartMap v V' i').toAlgebra
  Module.finrank (MRingOver F ι ⧸ (chartIdeal V' i').comap
    (rename v : MRingOver F ι →ₐ[F] MRingOver F ι').toRingHom) (MRingOver F ι' ⧸ chartIdeal V' i')

end Morphisms

end ReciprocityTheory.ChartRestriction.G.AI.I1
