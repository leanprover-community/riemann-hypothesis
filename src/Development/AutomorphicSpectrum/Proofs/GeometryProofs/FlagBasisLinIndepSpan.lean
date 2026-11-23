module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualRevDualRev
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.FlagBasis

theorem flagStep_full {E : Type} [AddCommGroup E] (Ω : Type) [Field Ω] [Module Ω E] {r : ℕ} (b : Fin r → E) :
    GlobalTheory.CompanionTheory.Ar.flagStep Ω b r = Submodule.span Ω (Set.range b) := by
  unfold GlobalTheory.CompanionTheory.Ar.flagStep
  have : {k : Fin r | (k : ℕ) < r} = Set.univ := by ext k; simp [k.2]
  rw [this, Set.image_univ]

theorem flag_b_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ)
    (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y)
    (Fl : 𝔐.Flag) (t : CMType H ⊕ CMType H),
    LinearIndependent Ω (Fl.b t) ∧ Submodule.span Ω (Set.range (Fl.b t)) = 𝔐.Vgen t := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ J y 𝔐 Fl t
  letI := 𝔐.fn.toAlgebra
  obtain ⟨cc, u, hc, _hj, _hjc, hb, _hu1, _hu0, hflag, _⟩ := Fl.generic
  refine ⟨hb t, ?_⟩
  have hle : Submodule.span Ω (Set.range (Fl.b t)) ≤ 𝔐.Vgen t := by
    rw [← flagStep_full, hflag t (labelRk D t), flagStep_full, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ ?_
    exact (Fl.V₀_mem t (cc t l)).1 ((hc t).2 ▸ Submodule.subset_span ⟨l, rfl⟩)
  obtain ⟨U, hpU, b', hspan, hfr⟩ := 𝔐.vb t ⟨GlobalTheory.CompanionTheory.Ar.genPt 𝔐.ξ, 𝔐.all _⟩ trivial
  have hli' : LinearIndependent Ω b' := (hfr _ trivial hpU).1
  have hV : Submodule.span Ω (Set.range b') = 𝔐.Vgen t := hspan
  haveI : FiniteDimensional Ω (𝔐.Vgen t) := by
    rw [← hV]; exact FiniteDimensional.span_of_finite Ω (Set.finite_range b')
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [← hV, finrank_span_eq_card (hb t), finrank_span_eq_card hli']

end GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.FlagBasis
