module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace UpperTheory.V.Af

def coef (f : ℍ → ℂ) (n : ℕ) : ℂ := (qExpansion 1 f).coeff n

def HasChar (k : ℕ) {M : ℕ} (χ : DirichletCharacter ℂ M) (f : ℍ → ℂ) : Prop :=
  ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M → f ∣[(k : ℤ)] γ = χ ((γ 1 1 : ℤ) : ZMod M) • f

def IsEigAt (k : ℕ) {M : ℕ} (χ : DirichletCharacter ℂ M) (f : ℍ → ℂ) (p : ℕ) (lam : ℂ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    coef f (p * n) + χ (p : ZMod M) * (p : ℂ) ^ (k - 1) * (if p ∣ n then coef f (n / p) else 0) = lam * coef f n

structure Newform (k : ℕ) where

  M : ℕ
  pos : 0 < M

  f : CuspForm (Gamma1 M) (k : ℤ)

  χ : DirichletCharacter ℂ M
  char : HasChar k χ f
  one : coef f 1 = 1
  eig : ∀ p : ℕ, p.Prime → ¬ p ∣ M → IsEigAt k χ f p (coef f p)
  new : ∀ M' : ℕ, M' ∣ M → M' ≠ M → ∀ (g : CuspForm (Gamma1 M') (k : ℤ)) (χ' : DirichletCharacter ℂ M'),
    HasChar k χ' g → (∀ᶠ p : ℕ in Filter.cofinite, p.Prime → IsEigAt k χ' g p (coef f p)) → g = 0

namespace Newform

variable {k : ℕ} (g : Newform k)

def a (n : ℕ) : ℂ := coef g.f n

def heckePoly (p : ℕ) : ℂ[X] := X ^ 2 - C (g.a p) * X + C (g.χ (p : ZMod g.M) * (p : ℂ) ^ (k - 1))

def Att {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (V : G ℚ Ω →* GL (Fin 2) (Qbar l)) : Prop :=
  IsSSRep V ∧ ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∀ A : ValuationSubring Ω, IsPlaceOver A w →
    (∀ s ∈ Ine (F := ℚ) A, V s = 1) ∧ ∀ σ : G ℚ Ω, IsFrob A (normV w) σ →
      (V σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.map ι.toRingHom = g.heckePoly (normV w)

end Newform

end UpperTheory.V.Af
