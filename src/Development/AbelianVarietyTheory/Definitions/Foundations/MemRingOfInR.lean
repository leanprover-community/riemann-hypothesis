module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.QFam GlobalTheory.KZ
open ReciprocityTheory.ChartRestriction.L1 (DD jT)

namespace GlobalTheory.FN

def Lv (E : Subring ℂ) (N w : ℕ) (f : ℍ → ℂ) : Prop :=
  (∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, f (γ • τ) = f τ) ∧
    ∀ γ : SL(2, ℤ), QAll (· ∈ E) N fun τ => DD τ ^ w * f (γ • τ)

def InR (E : Subring ℂ) (f : ℍ → ℂ) : Prop := ∃ N w : ℕ, 0 < N ∧ Lv E N w f

def ring (E : Subring ℂ) : Subring (ℍ → ℂ) := Subring.closure {f | InR E f}

def up (f : ℍ → ℂ) : ℂ → ℂ := fun z => f (UpperHalfPlane.ofComplex z)

def germ (f : ℍ → ℂ) : Mero := ((up f : ℂ → ℂ) : Mero)

def cmp (g : GQ) (f : ℍ → ℂ) : ℍ → ℂ := fun τ => up f (mob g τ)

def HS {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) (C : ℝ) (φ : ℂ → ℂ) (h : HahnSeries ℚ Ω) : Prop :=
  ∀ z : ℂ, C < z.im →
    HasSum (fun r : ℚ => ε (h.coeff r) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (φ z)

def Den {Ω : Type} [Field Ω] (h : HahnSeries ℚ Ω) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∀ r : ℚ, h.coeff r ≠ 0 → ∃ n : ℤ, r = (n : ℚ) / N

def IsExp {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) (f : ℍ → ℂ) (h : HahnSeries ℚ Ω) : Prop :=
  Den h ∧ ∃ C : ℝ, HS ε C (up f) h

def Cong (M : ℕ) (d : ℤ) (γ γ' : SL(2, ℤ)) : Prop :=
  (en γ' 0 0 : ZMod M) = en γ 0 0 ∧ (en γ' 0 1 : ZMod M) = d * en γ 0 1 ∧
    (d : ZMod M) * en γ' 1 0 = en γ 1 0 ∧ (en γ' 1 1 : ZMod M) = en γ 1 1

def IsStd {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Tower Ω ε) : Prop := T.an T.jK = germ jT

structure Frac (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) where

  K : Type
  [fld : Field K]
  [alg : Algebra Ω K]

  io : ring ε.range →+* K
  io_inj : Function.Injective io
  io_surj : ∀ f : K, ∃ a b : ring ε.range, b ≠ 0 ∧ f * io b = io a
  io_c : ∀ (c : Ω) (a : ring ε.range), (a : ℍ → ℂ) = (fun _ => ε c) → io a = algebraMap Ω K c

  exp : K →ₐ[Ω] HahnSeries ℚ Ω
  exp_io : ∀ a : ring ε.range, IsExp ε a (exp (io a))

  sl : GQ → (K ≃ₐ[Ω] K)
  sl_io : ∀ (g : GQ) (a a' : ring ε.range), (a' : ℍ → ℂ) = cmp g a → sl g (io a) = io a'

  gal : (Ω ≃ₐ[ℚ] Ω) → (K ≃+* K)
  gal_exp : ∀ s f r, (exp (gal s f)).coeff r = s ((exp f).coeff r)

  an : K →+* Mero
  an_io : ∀ a : ring ε.range, an (io a) = germ a

attribute [instance] Frac.fld Frac.alg

theorem mem_ring_of_inR {E : Subring ℂ} {f : ℍ → ℂ} (h : InR E f) : f ∈ ring E := Subring.subset_closure h

end GlobalTheory.FN
