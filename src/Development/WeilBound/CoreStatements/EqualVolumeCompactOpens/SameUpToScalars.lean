module

public import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.IsIsotropicHermitianSetting
public import Mathlib.NumberTheory.NumberField.CMField
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

@[expose] public section

noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField MeasureTheory GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
  ReciprocityTheory.L2DbarEstimates

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

abbrev ccH (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E := (IsCMField.complexConj E).toRingHom

end defs

def LevelFacts : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (c : E ≃ₐ[F] E)
    (J : Matrix (Fin N) (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E)) (𝔞 : Ideal (𝓞 E)), IsLat Λ → IsUnit J.det →
    (Neat c 𝔞 → ∀ γ ∈ levelGrp c.toRingHom J Λ 𝔞,
      (∃ s : E, (γ : Matrix (Fin N) (Fin N) E) = s • (1 : Matrix (Fin N) (Fin N) E)) → γ = 1) ∧
    ∀ (J₀ : Matrix (Fin N) (Fin N) E) (a : GL (Fin N) E) (Λ₀ : Submodule (𝓞 E) (Fin N → E)),
      (a : Matrix (Fin N) (Fin N) E)ᵀ * J₀ * (a : Matrix (Fin N) (Fin N) E).map c.toRingHom = J →
      (∀ x, x ∈ Λ ↔ (a : Matrix (Fin N) (Fin N) E) *ᵥ x ∈ Λ₀) →
      conjBy a (levelGrp c.toRingHom J Λ 𝔞) = levelGrp c.toRingHom J₀ Λ₀ 𝔞

end PositivityTheory.EqVol
