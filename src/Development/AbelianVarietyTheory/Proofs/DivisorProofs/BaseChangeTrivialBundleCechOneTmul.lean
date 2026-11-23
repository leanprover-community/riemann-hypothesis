module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false

namespace GlobalTheory.CechPoset

theorem Φ_one_tmul : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)), Φ w D hD' 0 ((1 : R') ⊗ₜ[R] one s D) = fun _ => 1 := by
  intro R R' _ _ _ X X' s s' φ w κ _ D hD'
  funext t
  have key : GlobalTheory.AbLaw.SecOnR.coord (f := s') (M := (LB.triv X).pull φ) (GlobalTheory.AbLaw.secTermBaseChange (LB.triv X) D w 1 ((1 : R') ⊗ₜ[R] one s D) t) (i0 φ) = 1 := by
    erw [GlobalTheory.AbLaw.secTermBaseChange_tmul, one_smul]
    refine (GlobalTheory.AbLaw.SecOn.coord_pullLE (M := LB.triv X) φ (GlobalTheory.AbLaw.preimage_biInf D φ t.1).ge ((GlobalTheory.AbLaw.secOnTrivEquiv _).symm 1) (i0 φ)).trans ?_
    have hc : GlobalTheory.LB.coord ((GlobalTheory.AbLaw.secOnTrivEquiv (X := X) (⨅ i ∈ t.1, D i)).symm 1) PUnit.unit = 1 := by
      refine (GlobalTheory.AbLaw.SecOn.coord_chart_symm (M := Out.Inh.trivLB X) (Out.Inh.trivLB_isLB X) PUnit.unit PUnit.unit le_top (1 : Γ(X, ⨅ i ∈ t.1, D i))).trans ?_
      rw [map_one]
      exact (_root_.one_mul _).trans (map_one _)
    exact (congrArg _ hc).trans (map_one _)
  change Sec.res s' _ (GlobalTheory.AbLaw.SecOnR.coord (f := s') (M := (LB.triv X).pull φ) (GlobalTheory.AbLaw.secTermBaseChange (LB.triv X) D w 1 ((1 : R') ⊗ₜ[R] one s D) t) (i0 φ)) = 1
  rw [key]
  exact (Sec.res s' _).map_one

end GlobalTheory.CechPoset
