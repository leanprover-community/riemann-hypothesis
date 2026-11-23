module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBiduality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDimUniqueOfIsoGrp
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.H2EqZeroOfIsInitial
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.BaseChangeMapRingAct

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.AbDual GlobalTheory.CechPic
open GlobalTheory.SerreTateDef (IsPairRed polBundle)
open GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin (IsPolarisation)
open GlobalTheory.BadPt (IsWeilHom)
open GlobalTheory.PerfdLat (dualBaseChange)

attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

namespace GlobalTheory.DualTower

theorem dim_eq_of_isDual {K : Type} [Field K] (A D : AV.AbVar K) (P : LB (A.X ⊗ D.X).left)
    (h : IsDual A.X D.X P) : D.dim = A.dim := by
  obtain ⟨B, _, P₀, _, hdim, hdual, _⟩ := GlobalTheory.dualAbelianScheme _ A.X A.ab
  obtain ⟨e⟩ := GlobalTheory.Published.AbelianDualCrystal.Test.dual_unique hdual h
  have hB := hdim A.dim A.smooth
  have hne : Nonempty (Sp K) := ⟨IsLocalRing.closedPoint K⟩
  exact (GlobalTheory.relDim_unique_of_iso_grp _ hne B D.X e.hom inferInstance A.dim D.dim hB D.smooth).symm

end GlobalTheory.DualTower
