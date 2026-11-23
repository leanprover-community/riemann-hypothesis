module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelConstantsExtension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AddJFintype

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

theorem _root_.GlobalTheory.T.lie_model_constants_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Tor.Level H) (c : Coeff l)
    (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀]
    [CharZero Ω] [Algebra Ω₀ Ω] (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X')
    (cst : c.F →+* Ω₀) (V V' : Type) [AddCommGroup V] [Module Ω₀ V] [AddCommGroup V'] [Module Ω V']
    (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V') (ρ : 𝓞 E →+* Module.End Ω₀ V) (ρ' : 𝓞 E →+* Module.End Ω V')
    (L : CMType H ⊕ CMType H → Lat ξ V) (j : V →+ V') (r : CMType H ⊕ CMType H → ℕ)
    (b : ∀ s, Fin (r s) → V'),
    IsCptGen ξ → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω₀ Ω) →
    M.IsActOf t.act.act ρ → M'.IsActOf t'.act.act ρ' →
    (∀ q : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → IsIntegrallyClosed (regAt ξ q)) →
    (∀ q : Cpt ξ', (∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q) → IsIntegrallyClosed (regAt ξ' q)) →
    (∀ s (q : Cpt ξ), (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → L s q = M.eigLat ρ (cst.comp (labelEmb c s)) q) →
    M'.lat = M.lat.pull ξ' f j →
    (∀ s, ∀ e ∈ eigSp ρ (cst.comp (labelEmb c s)),
      j e ∈ eigSp ρ' (((algebraMap Ω₀ Ω).comp cst).comp (labelEmb c s))) →
    (∀ s, ((L s).pull ξ' f j).IsFlagVBOn Set.univ (b s)) →
    ∀ s, (M'.eigLat ρ' (((algebraMap Ω₀ Ω).comp cst).comp (labelEmb c s))).IsFlagVBOn
      {q | ∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q} (b s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagStep.eigLat_isFlagVBOn_of_pull_char0 | exact GlobalTheory.CompanionTheory.Ar.FlagStep.eigLat_isFlagVBOn_of_pull_char0 | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagStep.eigLat_isFlagVBOn_of_pull_char0 <;> assumption)
