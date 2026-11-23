module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyBasisBijectiveStatement
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem preRes_bijective : ∀ (R' : Type) [CommRing R'] (X X' : Scheme.{0}) (φ : X' ⟶ X) [IsClosedImmersion φ] (s' : X' ⟶ Sp R'), Function.Bijective (preRes φ s').pull1 ∧ Function.Bijective (preRes φ s').pull2 ∧ (CohomZeroIsConstants (OAff s') → CohomZeroIsConstants (OPre φ s')) := by
  intro R' _ X X' φ _ s'
  have hB : ∀ {U : TopologicalSpace.Opens X} {x : X}, x ∈ U → ∃ U' ∈ X.affineOpens, x ∈ U' ∧ U' ≤ U :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
  refine GlobalTheory.T.structureSheafCohomology_basis_bijective R' X' s' X.affineOpens (preU φ) (preU_mono φ) ?_ ?_
  · intro U x hx
    obtain ⟨W, hW, hWU⟩ := (φ.isClosedEmbedding).isInducing.isOpen_iff.mp U.1.2
    have hxW : φ.base x ∈ W := by
      have : x ∈ φ.base ⁻¹' W := by rw [hWU]; exact hx
      exact this
    obtain ⟨V, hV, hxV, hVW⟩ := hB (U := ⟨W, hW⟩) hxW
    refine ⟨⟨V, hV⟩, hxV, ?_⟩
    intro y hy
    have : y ∈ φ.base ⁻¹' W := hVW hy
    rw [hWU] at this
    exact this
  · intro a b x ha hb
    obtain ⟨V, hV, hxV, hVW⟩ := hB (U := a.1 ⊓ b.1) ⟨ha, hb⟩
    exact ⟨⟨V, hV⟩, fun y hy ↦ (hVW hy).1, fun y hy ↦ (hVW hy).2, hxV⟩

end GlobalTheory.AbCoh
