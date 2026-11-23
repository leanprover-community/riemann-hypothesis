module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportOfPrincipalSeriesSubquotient
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsIrreducibleIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.CoreOrdAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord

namespace UpperTheory.V.Z.Ord.AtLOrdinary

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem plainTor_of_ps [CharZero k] {n : ℕ} (σ : SmIrr (GL (Fin n) k)) (ω : Fin n → kˣ →* ℂˣ) (hs : ∀ i, IsSmoothChar (ω i))
    (hd : ∀ i j, i ≠ j → ∃ y : Uo k, ω i y ≠ ω j y) (e : σ.ρ.Equiv (PS ω)) :
    GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) := by
  have hμ : ∀ i, IsSmoothChar (ω i * absPow k (((n : ℂ) - 1) / 2)) := fun i => (hs i).mul (isSmoothChar_absPow _)
  have hsup := hasSupport_of_isSubquotient_prinSeries k n _ hμ ⟨_, σ.ρ, σ.smooth, σ.irred⟩
    (.of_injective e.toIntertwiningMap e.toLinearEquiv.injective)
  refine ⟨_, hsup.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred), fun y hy => ?_, fun y hy z hz e' => ?_⟩
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    rfl
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hz
    rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at e'
    by_cases hij : i = j
    · subst hij
      have h1 : absPow k ((1 : ℝ) : ℂ) = 1 := by
        have := mul_left_cancel (a := ω i * absPow k (((n : ℂ) - 1) / 2)) (b := 1) (c := absPow k 1) (by simpa using e')
        simpa using this.symm
      exact one_ne_zero (absPow_ofReal_eq_one.1 h1)
    · obtain ⟨y, hy⟩ := hd i j hij
      have h1 := DFunLike.congr_fun e' (y : kˣ)
      simp only [MonoidHom.mul_apply, isUnram_absPow k 1 (y : kˣ) y.2, isUnram_absPow k (((n : ℂ) - 1) / 2) (y : kˣ) y.2, mul_one] at h1
      exact hy h1

end UpperTheory.V.Z.Ord.AtLOrdinary
