module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.HeckeFixedPointCMCycleClass
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.InvMemLatMonoidOfMemAwaySupp
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.fixZ_of :
    UpperTheory.Gal.W2.HeckeFixedPointCMCycleClass → UpperTheory.Gal.W2.LevelChange → UpperTheory.Gal.W2.FixZ := by
  intro hZ hLC p _ D G L ha hm v hv t₀ ht gb hgb N N' h hok X X' c₁ c₂ hreg k α hα hE h₁ h₂
  obtain ⟨hsm, Fx, At, hF, hT, hfin, htriv, hsum⟩ :=
    hZ p D G L ha hm v hv t₀ ht gb hgb N N' h hok X X' c₁ c₂ hreg k α hα hE h₁ h₂
  obtain ⟨hN3, -, hN'3, -, hdvd, hconj⟩ := hok
  have hN : 0 < N := by omega
  have hN' : 0 < N' := by omega
  have hle : L.KN N' ≤ GlobalTheory.HeckeCorr.heckeLevel (L.KN N) h⁻¹ := by
    obtain ⟨k', rfl⟩ := hdvd
    exact fun u hu => GlobalTheory.W2.mem_heckeLevel_inv.2 ⟨GlobalTheory.W2.KN_mul_le L N k' hu, hconj u hu⟩
  refine ⟨hsm, Fx, At, hF, hT, fun t => ?_⟩
  rw [hsum t]
  exact hLC p G v (wtFix L v t₀ α t) (L.KN N) (L.KN N') h hle
    (GlobalTheory.W2.relIndex_KN_ne_zero L hN hN') htriv hfin
