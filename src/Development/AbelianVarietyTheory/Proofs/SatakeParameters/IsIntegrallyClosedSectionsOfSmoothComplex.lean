module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.CupPair
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KaehlerOneFormsToExtensionDeRhamMulSelf

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

theorem isIntegrallyClosed_sections_of_smooth_complex :
    ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℂ) [Smooth s] (U : Z.Opens), IsAffineOpen U → genericPoint Z ∈ U → IsIntegrallyClosed Γ(Z, U) := by
  intro Z _ s hsm U hU hg
  have hs : (s.appLE ⊤ U le_top).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth s hsm ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  letI : Algebra Γ(Sp ℂ, ⊤) Γ(Z, U) := (s.appLE ⊤ U le_top).hom.toAlgebra
  have : Algebra.Smooth Γ(Sp ℂ, ⊤) Γ(Z, U) := hs
  let e : Γ(Sp ℂ, ⊤) ≃+* ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
  letI : Field Γ(Sp ℂ, ⊤) := (e.toMulEquiv.isField (Field.toIsField ℂ)).toField
  have : Nonempty U := ⟨⟨_, hg⟩⟩
  have : IsDomain Γ(Z, U) := inferInstance
  exact GlobalTheory.isIntegrallyClosed_of_smooth Γ(Sp ℂ, ⊤) Γ(Z, U)

end GlobalTheory
