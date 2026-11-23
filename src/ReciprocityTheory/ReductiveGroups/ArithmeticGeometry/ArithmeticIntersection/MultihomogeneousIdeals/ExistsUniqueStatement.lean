module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
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

section Family

variable {K : Type*} [Fintype K] (F : Type*) [Field F] (ι : K → Type*) [∀ k, Fintype (ι k)]

def ExistsUniqueStatement : Prop :=
  ∃ I : IFamily F ι, IsFieldIntersection I ∧
    ∀ J : IFamily F ι, IsFieldIntersection J →
      ∀ (V : Ideal (MRingOver F ι)) (n : ℕ) (L : Fin n → K → ℤ), IsProjVarF V n → J V n L = I V n L

def SymmStatement : Prop :=
  ∀ I : IFamily F ι, IsFieldIntersection I →
    ∀ (V : Ideal (MRingOver F ι)) (n : ℕ) (L : Fin n → K → ℤ) (σ : Equiv.Perm (Fin n)),
      IsProjVarF V n → I V n (L ∘ σ) = I V n L

def MultilinStatement : Prop :=
  ∀ I : IFamily F ι, IsFieldIntersection I →
    ∀ (V : Ideal (MRingOver F ι)) (n : ℕ) (L : Fin n → K → ℤ) (j : Fin n) (a b : K → ℤ),
      IsProjVarF V n →
      I V n (Function.update L j (a + b)) = I V n (Function.update L j a) + I V n (Function.update L j b)

end Family

section Projection

variable {K : Type*} [Fintype K] {K' : Type*} [Fintype K'] (F : Type*) [Field F]
  (ι : K → Type*) [∀ k, Fintype (ι k)] (ι' : K' → Type*) [∀ k, Fintype (ι' k)]

def ProjContractStatement : Prop :=
  ∀ I' : IFamily F ι', IsFieldIntersection I' →
    ∀ (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (V' : Ideal (MRingOver F ι')) (e d : ℕ)
      (L : Fin e → K → ℤ), IsBlockMap κ v → IsProjVarF V' e → IsProjVarF (imageVar F v V') d →
      d < e → I' V' e (fun j => pullDeg κ (L j)) = 0

def ProjDegStatement : Prop :=
  ∀ (I : IFamily F ι) (I' : IFamily F ι'), IsFieldIntersection I → IsFieldIntersection I' →
    ∀ (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (V' : Ideal (MRingOver F ι')) (e : ℕ)
      (L : Fin e → K → ℤ) (i' : ∀ k', ι' k'), IsBlockMap κ v → IsProjVarF V' e →
      IsProjVarF (imageVar F v V') e → IsChart V' i' →
      I' V' e (fun j => pullDeg κ (L j)) = (fnDeg v V' i' : ℤ) * I (imageVar F v V') e L

end Projection

section Fibre

variable {K : Type*} [Fintype K] (ι : K → Type*) [∀ k, Fintype (ι k)]

def GeoNumStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (I : IFamily (ZMod p) ι), IsFieldIntersection I →
    ∀ (V : Ideal (MRing ι)) (n : ℕ) (a : Fin n → K → ℤ), IsMultiProjPrime V → (p : MRing ι) ∈ V →
      IsProjVarF (V.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) n →
      geoNum n V a = I (V.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) n a

end Fibre

section BaseField

variable {K : Type*} [Fintype K] (F F' : Type*) [Field F] [Field F'] [Algebra F F'] (ι : K → Type*)
  [∀ k, Fintype (ι k)]

end BaseField

section Positivity

variable {K : Type*} [Fintype K] (F : Type*) [Field F] (ι : K → Type*) [∀ k, Fintype (ι k)]

def PositivityStatement : Prop :=
  ∀ I : IFamily F ι, IsFieldIntersection I →
    ∀ (V : Ideal (MRingOver F ι)) (n : ℕ), IsProjVarF V n →
      (∀ L : Fin n → K → ℤ, (∀ j k, 0 ≤ L j k) → 0 ≤ I V n L) ∧ 0 < I V n (fun _ _ => 1)

end Positivity

section Inhabit

variable (F : Type*) [Field F]

end Inhabit

end ReciprocityTheory.ChartRestriction.G.AI.I1
