module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GermSecRestrictGlobalAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericGermDifferentialFormPullbackDominant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.genericGerm_differentialForm_pullback_dominant : ∀ (Z Z' : Scheme.{0}) [IsIntegral Z] [IsIntegral Z'] (p : Z ⟶ Sp ℂ) (p' : Z' ⟶ Sp ℂ),
    letI := algΓ p; letI := algΓ p'
    ∀ [inst : Algebra ℂ Z.functionField] [inst' : Algebra ℂ Z'.functionField] (hinst : inst = ffAlg p)
      (hinst' : inst' = ffAlg p') (f : Z' ⟶ Z) (hf : f ≫ p = p') (ψ : Z.functionField →ₐ[ℂ] Z'.functionField)
      (φ : DR ℂ Z.functionField →ₗ[ℂ] DR ℂ Z'.functionField), IsDRMap ℂ ψ φ →
      (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Z' ∈ f ⁻¹ᵁ V) (g : Γ(Z, V)),
        ψ ((Z.presheaf.germ V (genericPoint Z) hV).hom g) =
          (Z'.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Z') hV').hom (f.app V g)) →
      ∀ (j : ℕ) (V : Z.Opens) (V' : Z'.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
        (hη : genericPoint Z ∈ V) (hη' : genericPoint Z' ∈ V') (h : V' ≤ f ⁻¹ᵁ V)
        (y : sectionsOn (Omega p j) V),
        formGermI p' j hV' hη' hinst' (sectionsOn.res ℂ (Omega p' j) h
          (sectionsOn.mapOver (appTop_algebraMap hf) (omegaPull hf j) V y)) =
          φ (formGermI p j hV hη hinst y) := by
  first | (exact @GlobalTheory.HodgeCoh.formGermI_res_mapOver) | (exact GlobalTheory.HodgeCoh.formGermI_res_mapOver) | (intros; apply GlobalTheory.HodgeCoh.formGermI_res_mapOver  <;> assumption)
