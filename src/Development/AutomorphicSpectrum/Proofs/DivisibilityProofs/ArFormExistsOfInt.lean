module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ToZIsArFunIffStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsArithVarInt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.WZIsCInfStatement
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem arFormExists_of_int :
    (∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℤ) (D : ℕ), IsArithVar p D →
      ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p), ∃ Φ, IsArFun L D Φ) → GlobalTheory.Published.ArFormExists := by
  intro H k _ X _ p D hX ι _ L
  let t : X ⟶ Sp ℤ := specZIsTerminal.from X
  haveI : Module.Finite ℤ k := hX.finite
  have hL : ∀ i τ, (wZ (L i) t τ).IsCInf := fun i τ => GlobalTheory.T.wZ_isCInf' k X p t (L i) τ
  obtain ⟨Φ, hΦ⟩ := H X t D (GlobalTheory.CompanionTheory.Ar.BaseZ.isArithVar_int k X p t D hX) ι
    (fun i => GlobalTheory.CompanionTheory.Ar.BaseZ.toZ (L i) t (hL i))
  exact ⟨Φ, (GlobalTheory.T.toZ_isArFun_iff k X p t D hX ι L hL Φ).1 hΦ⟩

end GlobalTheory.CompanionTheory.Ar.BaseZ
