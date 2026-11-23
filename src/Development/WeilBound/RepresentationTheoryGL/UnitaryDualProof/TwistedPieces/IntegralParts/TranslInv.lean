module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.TraceForm
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseP
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.IsClosedGzS
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.TP.Nil

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def hom (t : kˣ) (p : Sp k n) : Sp k n := ((t : k) • p.1, p.2)

def pullH (t : kˣ) : ((Sp k n → ℂ) →ₗ[ℂ] ℂ) →ₗ[ℂ] ((Sp k n → ℂ) →ₗ[ℂ] ℂ) where
  toFun ξ := ξ ∘ₗ LinearMap.funLeft ℂ ℂ (hom t)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def polyH (t : kˣ) (a : List ℝ) : Module.End ℂ ((Sp k n → ℂ) →ₗ[ℂ] ℂ) :=
  (a.map fun x => pullH t - ((((nabs k t)⁻¹ : ℝ) ^ x : ℝ) : ℂ) • LinearMap.id).prod

def SuppU (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ) (C : Set (Sp k n)) : Prop :=
  ∀ f ∈ supportedIn (UU : Set (Sp k n)), (∀ p ∈ C, f p = 0) → ξ f = 0

def InvU (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ g ∈ Gz Z, ∀ f ∈ supportedIn (UU : Set (Sp k n)), ξ (fun p => f (act g p)) = ξ f

def TranslInv (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ z ∈ Z, ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), ξ (fun p => f (p.1 + z, p.2)) = ξ f

def dB (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : ℕ :=
  Module.finrank k (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)))

variable (k)

def FourQ : Prop :=
  TraceForm k → ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z →
    ∃ 𝓕 : ((Sp k n → ℂ) →ₗ[ℂ] ℂ) →ₗ[ℂ] ((Sp k n → ℂ) →ₗ[ℂ] ℂ),
      (∀ ξ, Supp ξ (Bz Z ×ˢ Set.univ) → Supp (𝓕 ξ) (Bz Z ×ˢ Set.univ)) ∧
      (∀ ξ, Supp ξ (Bz Z ×ˢ Set.univ) → Inv Z ξ → Inv Z (𝓕 ξ)) ∧
      (∀ ξ, Supp ξ (Bz Z ×ˢ Set.univ) → (Kills ξ UU ↔ Kills (𝓕 ξ) UU)) ∧
      (∀ ξ, (∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), ξ f = 0) →
        ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), 𝓕 ξ f = 0) ∧
      (∀ (t : kˣ) ξ, Supp ξ (Bz Z ×ˢ Set.univ) → ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)),
        𝓕 (pullH t ξ) f = ((((nabs k t)⁻¹ ^ dB Z : ℝ)) : ℂ) * pullH t⁻¹ (𝓕 ξ) f) ∧
      ∀ ξ, Supp ξ (NB Z ×ˢ Set.univ) → TranslInv Z (𝓕 ξ)

def OrbQ : Prop :=
  TraceForm k → PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k) → ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z →
    0 < dB0 Z → ∀ t : kˣ, nabs k t < 1 → ∃ a : List ℝ, (∀ x ∈ a, 2 * x < dB0 Z) ∧
      ∀ ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ, SuppU ξ (NB Z ×ˢ Set.univ) → InvU Z ξ → Kills (polyH t a ξ) UU

def FibQ : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → ∀ η : (Sp k n → ℂ) →ₗ[ℂ] ℂ,
    Supp η (Bz Z ×ˢ Set.univ) → Inv Z η → TranslInv Z η → SuppU η ((ZN Z ∩ Bz Z) ×ˢ Set.univ) →
    ∃ η' : (Sp k n → ℂ) →ₗ[ℂ] ℂ, SuppU η' (NB Z ×ˢ Set.univ) ∧ InvU Z η' ∧
      ∀ t : kˣ, nabs k t < 1 → ∀ a : List ℝ, Kills (polyH t a η') UU →
        Kills (polyH t (a.map (· + (Module.finrank k Z : ℝ))) η) UU

def BaseQ : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → dB0 Z = 0 → FibVan Z (NB Z)

end PositivityTheory.RgUd.TP.Nil

end
