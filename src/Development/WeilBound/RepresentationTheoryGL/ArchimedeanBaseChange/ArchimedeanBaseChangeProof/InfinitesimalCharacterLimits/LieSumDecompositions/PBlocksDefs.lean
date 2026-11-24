module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def yp {a : ℕ} (k : Kinf E a) (g : GL (Fin a) (Af E)) : GA E a := infGL E a (Unitary.toUnits k) * finGL E a g

def lsF (r s : ℕ) (F : Sm E (r + s)) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) : Set (Sm E r) :=
  {ℓ | ∃ m₂ : GA E s, ∀ m₁, ℓ.1 m₁ = F.1 (lev (Ad E) r s (m₁, m₂) * yp k g)}

def rsF (r s : ℕ) (F : Sm E (r + s)) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) : Set (Sm E s) :=
  {ℓ | ∃ m₁ : GA E r, ∀ m₂, ℓ.1 m₂ = F.1 (lev (Ad E) r s (m₁, m₂) * yp k g)}

def LS {r s : ℕ} (U : Submodule ℂ (Sm E (r + s))) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)) : Submodule ℂ (Sm E r) :=
  Submodule.span ℂ {ℓ | ∃ ψ ∈ U, ∃ k g, ℓ ∈ lsF r s (T ψ) k g}

def RS {r s : ℕ} (U : Submodule ℂ (Sm E (r + s))) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)) : Submodule ℂ (Sm E s) :=
  Submodule.span ℂ {ℓ | ∃ ψ ∈ U, ∃ k g, ℓ ∈ rsF r s (T ψ) k g}

theorem lsF_sub_LS {r s : ℕ} {U : Submodule ℂ (Sm E (r + s))} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} {ψ : Sm E (r + s)}
    (hψ : ψ ∈ U) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) : lsF r s (T ψ) k g ⊆ LS U T :=
  fun _ h => Submodule.subset_span ⟨ψ, hψ, k, g, h⟩

theorem rsF_sub_RS {r s : ℕ} {U : Submodule ℂ (Sm E (r + s))} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} {ψ : Sm E (r + s)}
    (hψ : ψ ∈ U) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) : rsF r s (T ψ) k g ⊆ RS U T :=
  fun _ h => Submodule.subset_span ⟨ψ, hψ, k, g, h⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives

end
