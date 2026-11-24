module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

theorem UpperTheory.Cb.exists_finite_etale_restrict_clopen :
    ∀ (Y Z : Scheme.{0}) (c : Y ⟶ Z) (V : Z.Opens) (W : Y.Opens), IsClosed (W : Set Y) → W ≤ c ⁻¹ᵁ V → IsFinite c → Etale c → ∃ c' : W.toScheme ⟶ V.toScheme, c' ≫ V.ι = W.ι ≫ c ∧ IsFinite c' ∧ Etale c' := by
  intro Y Z c V W hWc hWV hfin het
  haveI := het
  haveI := hfin
  refine ⟨c.resLE V W hWV, c.resLE_comp_ι hWV, ?_, inferInstance⟩
  haveI hWι : IsClosedImmersion W.ι := .of_isPreimmersion _ (by simpa using hWc)
  haveI h1 : IsClosedImmersion (Y.homOfLE hWV ≫ (c ⁻¹ᵁ V).ι) := by
    rw [Scheme.homOfLE_ι]
    exact hWι
  haveI h2 : IsClosedImmersion (Y.homOfLE hWV) := .of_comp _ ((c ⁻¹ᵁ V).ι)
  haveI h3 : IsFinite (c ∣_ V) := by infer_instance
  show IsFinite (Y.homOfLE hWV ≫ c ∣_ V)
  infer_instance
