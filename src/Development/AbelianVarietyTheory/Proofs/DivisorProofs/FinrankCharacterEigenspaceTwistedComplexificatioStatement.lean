module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCharacterEigenspaceTwistedComplexificatio
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open GlobalTheory.BadCount

theorem _root_.GlobalTheory.T.finrank_characterEigenspace_twistedComplexification : ∀ (K W G : Type) [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Group G] [Fintype G]
    (σ : K →+* ℂ) (ρ0 : G →* (W →ₗ[K] W)) (χ : G →* Kˣ) (J : Subgroup G) (μ : J →* Kˣ) (c : G → K),
    Module.finrank K (⨅ p : J, LinearMap.ker (ρ0 p - ((χ p * μ p : Kˣ) : K) • LinearMap.id) : Submodule K W) =
      Module.finrank ℂ (eig (GlobalTheory.DefRead.twBC σ ρ0 χ) J ((Units.map σ.toMonoidHom).comp μ)) ∧
    Module.finrank K ((⨅ p : J, LinearMap.ker (ρ0 p - ((χ p * μ p : Kˣ) : K) • LinearMap.id)) ⊓
        LinearMap.ker (∑ g, (c g * ((χ g)⁻¹ : Kˣ)) • ρ0 g) : Submodule K W) =
      Module.finrank ℂ (eig (GlobalTheory.DefRead.twBC σ ρ0 χ) J ((Units.map σ.toMonoidHom).comp μ) ⊓
        LinearMap.ker (Representation.asAlgebraHom (GlobalTheory.DefRead.twBC σ ρ0 χ) (∑ g, MonoidAlgebra.single g (σ (c g)))) :
          Submodule ℂ (GlobalTheory.DefRead.VC σ W)) := by
  first | exact @GlobalTheory.DefRead.finrank_eig_twBC | exact GlobalTheory.DefRead.finrank_eig_twBC | (intros; apply GlobalTheory.DefRead.finrank_eig_twBC <;> assumption)
