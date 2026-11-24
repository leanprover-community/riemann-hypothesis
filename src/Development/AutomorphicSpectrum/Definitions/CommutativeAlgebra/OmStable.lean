module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Mathlib.Algebra.Module.Lattice.Full
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

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

structure HTPoint (C O : Type) [Field C] [CommRing O] [Algebra O C] {E : Type} [Field E] [NumberField E]
    (c : E ≃+* E) (κ : O) (N : ℕ)
    (V Ω : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
    [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω] where

  T : Submodule O V

  ρ : 𝓞 E →+* Module.End C V

  t : Fin N → V
  free : IsFreeOn ρ T t

  e : V →ₗ[C] V →ₗ[C] C
  alt : ∀ x, e x x = 0
  nondeg : ∀ y, (∀ x, e x y = 0) → y = 0
  perfect : dualLat e T = T
  adj : ∀ (a : 𝓞 E) (x y : V), e (ρ a x) y = e x (ρ (RingOfIntegers.mapRingEquiv c a) y)

  om : Submodule O Ω
  om_lat : om.IsFullLattice C

  ρΩ : 𝓞 E →+* Module.End C Ω
  om_stable : ∀ (a : 𝓞 E), ∀ x ∈ om, ρΩ a x ∈ om

  ht : V →ₗ[C] Ω
  ht_lin : ∀ (a : 𝓞 E) (x : V), ht (ρ a x) = ρΩ a (ht x)
  ht_mem : ∀ x ∈ T, ht x ∈ om
  κ_ne : algebraMap O C κ ≠ 0
  κ_mem : ∀ y ∈ om, ∃ x ∈ T, ht x = κ • y
  lagr : ∀ x, ht x = 0 ↔ ∀ y, ht y = 0 → e x y = 0

namespace HTPoint

variable {C O : Type} [Field C] [CommRing O] [Algebra O C] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {κ : O} {N : ℕ}
  {V Ω : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω]
  (P : HTPoint C O c κ N V Ω)

def W : Submodule C V := LinearMap.ker P.ht

def om' : Submodule O Ω := P.T.map (P.ht.restrictScalars O)

def Wsp (σ : E →+* C) : Submodule C V := P.W ⊓ eigSp P.ρ σ

def Ωsp (σ : E →+* C) : Submodule C Ω := eigSp P.ρΩ σ

def W' (σ : E →+* C) : Submodule O V := P.W.restrictScalars O ⊓ eigSub P.ρ σ P.T

def omHT (σ : E →+* C) : Submodule O Ω := eigQuot P.ρΩ σ P.om'

def omRec (σ : E →+* C) : Submodule O Ω := eigQuot P.ρΩ σ P.om

def tate (x : Fin N → 𝓞 E) : V := ∑ i, P.ρ (x i) (P.t i)

end HTPoint

end GlobalTheory.CompanionTheory.Ar.HT
