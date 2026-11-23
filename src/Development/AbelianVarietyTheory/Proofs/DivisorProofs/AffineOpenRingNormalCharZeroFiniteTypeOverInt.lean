module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyVals

theorem ring_of_isAffineOpen : ∀ (S : Scheme.{0}) [IsIntegral S] (s : S ⟶ Sp ℤ) (W : S.Opens), IsAffineOpen W → (W : Set S).Nonempty →
    Geo.Tor.IsNormalScheme S → LocallyOfFiniteType s → CharZero Γ(S, ⊤) →
    IsIntegrallyClosed Γ(S, W) ∧ CharZero Γ(S, W) ∧ Algebra.FiniteType ℤ Γ(S, W) := by
  intro S _ s W hW hne hN hs hc
  haveI : Nonempty W := hne.to_subtype
  haveI : GlobalTheory.IsNormalScheme S := (GlobalTheory.isNormalScheme_iff_pred S).2 hN
  refine ⟨GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hW, ?_, ?_⟩
  · exact charZero_of_injective_ringHom (map_injective_of_isIntegral S (homOfLE (le_top : W ≤ ⊤)))
  · have h₁ : (s.appLE ⊤ W le_top).hom.FiniteType :=
      HasRingHomProperty.appLE (P := @LocallyOfFiniteType) s hs ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
    have h₂ : ((Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom).FiniteType :=
      RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of ℤ)).symm.commRingCatIsoToRingEquiv.surjective
    have h₃ := h₁.comp h₂
    rw [← RingHom.finiteType_algebraMap, RingHom.ext_int (algebraMap ℤ Γ(S, W))
      ((s.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom)]
    exact h₃

end GlobalTheory.KeyVals
