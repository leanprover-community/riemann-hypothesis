module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
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

@[expose] public section

noncomputable section

open IsLocalRing Polynomial UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.Ws.Pp

def SpTri {ι A C : Type} [CommRing A] [CommRing C] (M : ι → M4 A) (P : ι → Fin 4 → A[X]) (φ : A →+* C) (u : M4 C) : Prop :=
  IsGSp 1 u ∧ ∀ g, IsUp (adj u * (M g).map φ * u) ∧ ∀ i, (P g i).eval₂ φ ((adj u * (M g).map φ * u) i i) = 0

def Dist {A : Type} [CommRing A] (I : Ideal A) (p : A[X]) : Prop := p.Monic ∧ ∀ n < p.natDegree, p.coeff n ∈ I

theorem SpTri.map {ι A C C' : Type} [CommRing A] [CommRing C] [CommRing C'] {M : ι → M4 A} {P : ι → Fin 4 → A[X]}
    {φ : A →+* C} {u : M4 C} (h : SpTri M P φ u) (ψ : C →+* C') : SpTri M P (ψ.comp φ) (u.map ψ) := by
  have a : ∀ Y : M4 C, adj (Y.map ψ) = (adj Y).map ψ := fun Y => by
    ext i j
    simp only [adj_apply, Matrix.map_apply, map_zsmul]
  have e : ∀ g, adj (u.map ψ) * (M g).map (ψ.comp φ) * u.map ψ = (adj u * (M g).map φ * u).map ψ := fun g => by
    rw [a, Matrix.map_mul, Matrix.map_mul]
    rfl
  refine ⟨?_, fun g => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
  · have := h.1
    unfold IsGSp at this ⊢
    rw [a, ← Matrix.map_mul, this, one_smul, one_smul, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
  · rw [e, Matrix.map_apply, (h.2 g).1 i j hij, map_zero]
  · rw [e, Matrix.map_apply, ← hom_eval₂, (h.2 g).2 i, map_zero]

theorem SpTri.of_map {ι A C C' : Type} [CommRing A] [CommRing C] [CommRing C'] {M : ι → M4 A} {P : ι → Fin 4 → A[X]}
    {φ : A →+* C} {u : M4 C} (ψ : C →+* C') (hψ : Function.Injective ψ) (h : SpTri M P (ψ.comp φ) (u.map ψ)) :
    SpTri M P φ u := by
  have a : ∀ Y : M4 C, adj (Y.map ψ) = (adj Y).map ψ := fun Y => by
    ext i j
    simp only [adj_apply, Matrix.map_apply, map_zsmul]
  have e : ∀ g, adj (u.map ψ) * (M g).map (ψ.comp φ) * u.map ψ = (adj u * (M g).map φ * u).map ψ := fun g => by
    rw [a, Matrix.map_mul, Matrix.map_mul]
    rfl
  refine ⟨?_, fun g => ⟨fun i j hij => hψ ?_, fun i => hψ ?_⟩⟩
  · have := h.1
    unfold IsGSp at this ⊢
    rw [a, ← Matrix.map_mul, one_smul, ← Matrix.map_one ψ (map_zero ψ) (map_one ψ)] at this
    rw [one_smul]
    exact Matrix.map_injective hψ this
  · have := (h.2 g).1 i j hij
    rwa [e, Matrix.map_apply, ← map_zero ψ] at this
  · have := (h.2 g).2 i
    rwa [e, Matrix.map_apply, ← hom_eval₂, ← map_zero ψ] at this

end UpperTheory.V.Ws.Pp

end
