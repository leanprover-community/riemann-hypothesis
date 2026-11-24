module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ToZIsArithHeightIffStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsArithVarInt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ToZPullIsometricStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.WZIsCInfStatement
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

theorem heightProjection_of_int : (∀ (X Y : Scheme.{0}) [IsIntegral Y] (p : X ⟶ Sp ℤ) (q : Y ⟶ Sp ℤ) (D e : ℕ), IsArithVar p D → IsArithVar q e → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), topologicalKrullDim (closure ({π (genericPoint Y)} : Set X)) = (e + 1 : ℕ) → π.residueDegree (genericPoint Y) ≠ 0 → ∀ (L : HermLB p) (h : X → ℝ), L.IsArithHeight h → (L.pull π hπ).IsSelfInter ((π.residueDegree (genericPoint Y) : ℝ) * h (π (genericPoint Y)))) → GlobalTheory.Published.HeightProjection := by
  intro H k _ X Y _ p q D e hp hq π hπ hdim hdeg L h hL
  haveI : Module.Finite ℤ k := hp.finite
  have hc : ∀ τ : ℤ →+* ℂ, (wZ L (p ≫ spMap (Int.castRingHom k)) τ).IsCInf :=
    GlobalTheory.T.wZ_isCInf' k X p (p ≫ spMap (Int.castRingHom k)) L
  have hc' : ∀ τ : ℤ →+* ℂ,
      (wZ (L.pull π hπ) (π ≫ p ≫ spMap (Int.castRingHom k)) τ).IsCInf :=
    GlobalTheory.T.wZ_isCInf' k Y q (π ≫ p ≫ spMap (Int.castRingHom k)) (L.pull π hπ)
  have htX : GlobalTheory.IsArithVar (p ≫ spMap (Int.castRingHom k)) D :=
    isArithVar_int k X p _ D hp
  have htY : GlobalTheory.IsArithVar (π ≫ p ≫ spMap (Int.castRingHom k)) e :=
    isArithVar_int k Y q _ e hq
  have hLZ : (toZ L (p ≫ spMap (Int.castRingHom k)) hc).IsArithHeight h :=
    (GlobalTheory.T.toZ_isArithHeight_iff k X p _ D hp L hc h).mpr hL
  have key := H X Y (p ≫ spMap (Int.castRingHom k)) (π ≫ p ≫ spMap (Int.castRingHom k)) D e
    htX htY π rfl hdim hdeg (toZ L (p ≫ spMap (Int.castRingHom k)) hc) h hLZ
  have iso := GlobalTheory.T.toZ_pull_isometric k X Y p q (p ≫ spMap (Int.castRingHom k))
    (π ≫ p ≫ spMap (Int.castRingHom k)) π hπ rfl L hc hc'
  obtain ⟨h', hh', hv⟩ := GlobalTheory.HermLB.Isometric.isSelfInter htY iso.symm key
  exact ⟨h', (GlobalTheory.T.toZ_isArithHeight_iff k Y q _ e hq (L.pull π hπ) hc' h').mp hh', hv⟩

end GlobalTheory.CompanionTheory.Ar.BaseZ
