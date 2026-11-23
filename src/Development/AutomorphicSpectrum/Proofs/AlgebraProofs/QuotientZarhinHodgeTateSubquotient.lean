module

public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AbelianSchemeTorsionAugmentationStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderRetractRestrictionStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsFiniteStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsHopfOrderStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem subquotientStatement_of_quotient_zarhin_hodgeTate
    (hQ : QuotientByFiniteFlatStatement) (hZ : ZarhinStatement) (hH : HodgeTateDatumStatement) :
    SubquotientStatement := by
  intro p _ C _ _ _ v R _ _ hv hp hc N _ M hM K
  obtain ⟨A, _, L, hA, hL, hamp, T, N', _, pt, hpt, i, π, hiπ, hst, rfl⟩ := hM
  classical
  haveI : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj
  haveI : IsCommMonObj A := hA.comm
  haveI : Finite N' := GlobalTheory.T.torsion_points_finite R p A T N' pt hpt
  letI : Fintype N' := Fintype.ofFinite N'
  have hi : Function.Injective i := Function.LeftInverse.injective (g := π) hiπ
  haveI : Finite N := Finite.of_injective i hi
  letI : Fintype N := Fintype.ofFinite N
  obtain ⟨⟨AA, hAA⟩, -⟩ := GlobalTheory.T.torsion_points_hopf_order p C v R hv hp A T N' pt hpt
  have hgen := GlobalTheory.T.abelian_scheme_torsion_augmentation hQ hZ hH p C v R hv hp hc A L hA hL hamp T N' pt hpt (K.map i)
  have hret := GlobalTheory.T.hopf_order_retract_restriction p C v R hv hp N' AA N i π hiπ (by rw [hAA]; exact hst)
  rw [← hAA]
  exact hret.2.2 K (by rw [hAA]; exact hgen)

end GlobalTheory.CompanionTheory.Ar.GR
