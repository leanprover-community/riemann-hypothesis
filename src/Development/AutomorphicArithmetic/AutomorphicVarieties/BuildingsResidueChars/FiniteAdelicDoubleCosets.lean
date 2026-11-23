module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaDecompositionFiniteAdelesGLStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StrongApproximationUpperUnitriangularFiniteAdeleStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
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

open NumberField IsDedekindDomain GlobalTheory.CuspRep

private theorem ohat_of {F : Type} [Field F] [NumberField F] {x : Af F} (hx : x ∈ PIW.ClassFinD.Ohat F) :
    x ∈ UpperTheory.V.Af.Ohat F :=
  UpperTheory.V.Af.mem_Ohat.2 (GroundTheory.Global.mem_integralFiniteAdeles.2 hx)

theorem UpperTheory.finite_adelic_double_cosets :
    UpperTheory.V.Af.CohB.FinDC := by
  intro F _ _ n
  obtain ⟨S, hS⟩ := PIW.ClassFinD.borelKGL_of GlobalTheory.T.iwasawaDecomposition_finiteAdeles_GL GlobalTheory.T.strongApproximation_upperUnitriangular_finiteAdeles PIW.ClassFinD.idele_class_finite F n
  refine ⟨S, fun g => ?_⟩
  obtain ⟨γ, s, hs, k, hk, hx⟩ := hS g
  refine ⟨γ, s, hs, k, UpperTheory.V.Af.mem_KLev.2 ⟨fun a b => ohat_of (hk.1 a b), fun a b => ohat_of (hk.2 a b),
    fun a b => ⟨_, sub_mem (ohat_of (hk.1 a b)) (ohat_of (PIW.ClassFinD.matInt_one F n a b)), ?_⟩⟩, hx⟩
  rw [Nat.cast_one, one_mul]
