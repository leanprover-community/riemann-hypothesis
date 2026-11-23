module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftPointAffineHomSectionsRingHom
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

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM

theorem _root_.GlobalTheory.T.exists_lift_point_affineHom_sections_ringHom : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsAffineHom π], ∀ (U : Z.affineOpens) (V V' : Type) [CommRing V]
    [IsLocalRing V] [CommRing V'] [IsLocalRing V'] (ξ : Sp V ⟶ Z) (hξ : ⊤ ≤ ξ ⁻¹ᵁ U.1) (f : V →+* V')
    (ρ : Γ(Y, π ⁻¹ᵁ U.1) →+* V'),
    ρ.comp (π.app U.1).hom = f.comp (ξ.appLE U.1 ⊤ hξ ≫ (Scheme.ΓSpecIso (.of V)).hom).hom →
    ∃ ψ : Sp V' ⟶ Y, ψ ≫ π = spMap f ≫ ξ ∧
      ∀ I : Y.IdealSheafData, idlAlong I ψ = (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩).map ρ := by
  first | exact @GlobalTheory.AffinePointLift.exists_lift | exact GlobalTheory.AffinePointLift.exists_lift | (intros; apply GlobalTheory.AffinePointLift.exists_lift <;> assumption)
