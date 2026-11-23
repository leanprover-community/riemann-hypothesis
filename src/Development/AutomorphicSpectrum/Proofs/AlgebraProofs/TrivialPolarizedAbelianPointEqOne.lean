module

import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotGoodClassZeroSucc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
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

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.DimZero

theorem isIso_hom_of_relDim_zero {S : Scheme.{0}} (A : Over S) [GrpObj A] (h : IsAbelianScheme A)
    (hd : SmoothOfRelativeDimension 0 A.hom) : IsIso A.hom := by
  apply GlobalTheory.ZM.Model.isIso_of_dim_zero <;> assumption

theorem over_hom_eq_of_mono {S : Scheme.{0}} {T A : Over S} [Mono A.hom] (x y : T ⟶ A) : x = y := by
  ext1
  rw [← cancel_mono A.hom, Over.w x, Over.w y]

theorem eq_one_of_g_eq_zero (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (P : Out.PolAV (Spec (CommRingCat.of R))) (hg : P.g = 0) (z : sp (R₀ := R) R ⟶ P.A) :
    z = 1 := by
  have hd : SmoothOfRelativeDimension 0 P.A.hom := hg ▸ P.smoothDim
  haveI := isIso_hom_of_relDim_zero P.A P.isAb hd
  exact over_hom_eq_of_mono _ _

end GlobalTheory.CompanionTheory.Ar.DimZero
