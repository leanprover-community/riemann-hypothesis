module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOppositeSubmoduleImprovedModPrimeOfOrthogo
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt


theorem _root_.GlobalTheory.T.exists_oppositeSubmodule_improved_mod_prime_of_orthogonal : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal) (hn𝔭 : (n : 𝓞 E) ∈ 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (m : D.La) (hm : m ∈ perp D Z ⊓ perp D Z') (hym : y m ∉ img D y Z' 𝔭)
    (hA : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ 𝔭 ∨ Z.map y ≤ img D y Z' 𝔭),
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' := by
  first | exact @GlobalTheory.LowFilt.exists_improves_of_perp | exact GlobalTheory.LowFilt.exists_improves_of_perp | (intros; apply GlobalTheory.LowFilt.exists_improves_of_perp <;> assumption)
