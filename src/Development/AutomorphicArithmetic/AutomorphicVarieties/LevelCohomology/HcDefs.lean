module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
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

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace UpperTheory.V.X

section Frame

variable {k Γ M : Type} [CommRing k] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module k M] [TopologicalSpace M]
  [DiscreteTopology M] (F : Alg.Frame Γ) (ρ : Representation k Γ M)

def selF : Submodule k (H1 ρ) :=
  (⨅ v, LinearMap.ker (resH1 ρ (F.φ v) (F.hφ v))) ⊓
    ⨅ q, (H1ur (ρ.comp (F.ψ q)) (F.N q)).comap (resH1 ρ (F.ψ q) (F.hψ q))

def shaF : Submodule k (H2 ρ) :=
  (⨅ v, LinearMap.ker (resH2 ρ (F.φ v) (F.hφ v))) ⊓ ⨅ q, LinearMap.ker (resH2 ρ (F.ψ q) (F.hψ q))

end Frame

structure HcPublished : Prop where
  lf : LocalFiniteness
  lt : LocalTateDuality
  le : LocalEulerChar
  gf : GlobalFiniteness
  ge : GlobalEulerChar
  pt : GlobalTheory.Published.PoitouTateNormalised

section Gal

variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

def cycK (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] : G ℚ Ω →* kˣ :=
  (Units.map (ZMod.castHom (dvd_pow_self l one_ne_zero) k).toMonoidHom).comp (cycMod ℚ Ω l 1)

variable {Ω}

def galFrame (SP : Set (HeightOneSpectrum (𝓞 ℚ))) (T Q : Finset ℕ) (v0 : T) (pl : ℕ → ValuationSubring Ω)
    (K : Subgroup (G ℚ Ω)) : Alg.Frame (GS Ω SP) where
  T := T
  v0 := v0
  Gv v := Dec (F := ℚ) (pl v)
  φ v := locHom SP (pl v)
  hφ v := continuous_locHom SP (pl v)
  Q := Q
  Gq q := Dec (F := ℚ) (pl q)
  ψ q := locHom SP (pl q)
  hψ q := continuous_locHom SP (pl q)
  N q := (Ine (F := ℚ) (pl q) ⊓ K).subgroupOf (Dec (F := ℚ) (pl q))

structure GalData (l : ℕ) (SP : Set (HeightOneSpectrum (𝓞 ℚ))) (T Q : Finset ℕ) (pl : ℕ → ValuationSubring Ω)
    (K : Subgroup (G ℚ Ω)) : Prop where
  l_odd : l ≠ 2
  prime : ∀ p, p ∈ T ∨ p ∈ Q → p.Prime
  disj : Disjoint T Q
  l_mem : l ∈ T
  mem : ∀ v, v ∈ SP ↔ ∃ p, (p ∈ T ∨ p ∈ Q) ∧ ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal
  isOver : ∀ p, p ∈ T ∨ p ∈ Q → (pl p).valuation (p : Ω) < 1
  idx : ∀ q ∈ Q, ¬ l ∣ K.relIndex (Ine (F := ℚ) (pl q))

def Van {k : Type} [Field k] (T : Finset ℕ) (pl : ℕ → ValuationSubring Ω) (K : Subgroup (G ℚ Ω)) (γ : G ℚ Ω →* kˣ) : Prop :=
  ∀ z : G ℚ Ω → k, IsLocallyConstant z → (∀ g h, z (g * h) = z g + (γ g : k) * z h) →
    (∀ A : ValuationSubring Ω, (∀ p ∈ T, ¬ A.valuation (p : Ω) < 1) → ∀ g ∈ Ine (F := ℚ) A, g ∈ K → z g = 0) →
    (∀ v ∈ T, ∃ m, ∀ g ∈ Dec (F := ℚ) (pl v), z g = (γ g : k) * m - m) → ∃ m, ∀ g, z g = (γ g : k) * m - m

end Gal

end UpperTheory.V.X

end
