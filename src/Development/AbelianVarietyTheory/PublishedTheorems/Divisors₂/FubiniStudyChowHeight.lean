module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap
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

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChowHt

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.Published

def FubiniStudyChowHeight : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (N e δ : ℕ) (Y : Scheme.{0}) [IsIntegral Y]
    (i : Y ⟶ PSpace (𝓞 K) N) [IsClosedImmersion i], GlobalTheory.IsArithVar (i ≫ PSpace.str (𝓞 K) N) e →
    ∀ (A : (𝓞 K →+* ℂ) → Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (hA : ∀ σ, (A σ).det ≠ 0)
      (hc : ∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin (N + 1)) ℂ,
        A ((starRingEnd ℂ).comp σ) = (A σ).map (starRingEnd ℂ) * U)
      (f : MvPolynomial (Fin (e + 1) × Fin (N + 1)) K),
      IsChowFormInt (((i (genericPoint Y) : ProjectiveSpectrum
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (𝓞 K))).asHomogeneousIdeal.toIdeal).map
          (MvPolynomial.map (algebraMap (𝓞 K) K))) e δ f →
      ((GlobalTheory.HermLB.fs (PSpace.str (𝓞 K) N) (GlobalTheory.ProjSpace.O1_isLB (𝓞 K) N) (GlobalTheory.ProjSpace.coord (𝓞 K) N)
          (GlobalTheory.ProjSpace.iSup_nonzeroLocus_coord (𝓞 K) N) A hA hc).pull i rfl).IsSelfInter
        ((Module.finrank ℚ K : ℝ) * formHeight δ (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) K)
          (fun σ => A (σ.comp (algebraMap (𝓞 K) K))) f)

end GlobalTheory.Published

end
