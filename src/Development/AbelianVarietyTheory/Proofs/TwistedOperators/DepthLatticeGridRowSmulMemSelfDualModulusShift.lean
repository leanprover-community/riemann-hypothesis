module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsValuationOneElementAtGridPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedGridArrowLatticeIffIntegralFrameMatr
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
namespace GlobalTheory.DepHalf

open scoped Pointwise

theorem smul_mem_latBig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → OffQ D →
    ∀ (G : GridData L sc) (i : ℕ), i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ u ∈ latRow G i, e • u ∈ latBig G i := by
  intro D T L sc μ₀ hL hQ G i hi e he u hu
  have h1 : e • u ∈ hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) := hu.2 e he
  have hmB : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    refine FractionalIdeal.coeIdeal_ne_zero.2 ?_
    unfold Places.modulBar
    intro h
    apply G.pl.modul_ne_bot sc
    have := congrArg (fun J : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • J) h
    simpa [smul_smul] using this
  have hone : (1 : D.host.E) ∈ ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹ := by
    have hle : (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤
        ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹ := by
      have := FractionalIdeal.inv_anti_mono hmB FractionalIdeal.coeIdeal_le_one
      rwa [inv_one] at this
    exact hle (FractionalIdeal.one_mem_one _)
  have hsub : G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0)) ≤
      homLat (G.Λ (.grid (i + 1) 0)) (idLat (shiftId G) (G.Λ (.grid i 0))) := by
    refine Submodule.smul_le.2 fun r hr x hx y hy => ?_
    rw [smul_mulVec]
    refine Submodule.subset_span ⟨algebraMap (𝓞 D.host.E) D.host.E r, ?_, x *ᵥ y, hx y hy, ?_⟩
    · unfold shiftId
      rw [show algebraMap (𝓞 D.host.E) D.host.E r = algebraMap (𝓞 D.host.E) D.host.E r * 1 by rw [mul_one]]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hr) hone
    · exact (algebraMap_smul D.host.E r (x *ᵥ y)).symm
  have h2 : e • u ∈ hatMx (homLat (G.Λ (.grid (i + 1) 0)) (idLat (shiftId G) (G.Λ (.grid i 0)))) := by
    refine AddSubgroup.closure_mono ?_ h1
    rintro w ⟨α, hα, x, hx, rfl⟩
    exact ⟨α, hα, x, hsub hx, rfl⟩
  have hhalf : IsHalf e (e • u) := fun a b => by
    rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, GlobalTheory.PlaceDatum.idemSum_mul_self he]
  have h0 : ∀ j, (Node.grid (i + 1) 0 : Node) ≠ .grid 0 j := fun j h => by
    injection h with h'
    omega
  have hsd : IsSelfDualC (G.V (.grid (i + 1) 0)) (G.Λ (.grid (i + 1) 0)) := (G.isV (show (Node.grid (i + 1) 0 : Node).InRange D.R.m from ⟨hi, Nat.zero_le _⟩) h0).sd
  exact GlobalTheory.RowLatChi.mem_latO_of_mem_hatMx hsd he (GlobalTheory.AAUnit.exists_valuation_one_element_at_grid_places hQ hL G) hhalf h2

end GlobalTheory.DepHalf
