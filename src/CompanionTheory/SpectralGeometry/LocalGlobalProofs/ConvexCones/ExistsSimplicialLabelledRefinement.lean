module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SimpLabMinValOne
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.BarycentricStageExtensionStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CarrierDimensionLabelBoundedStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsCarrierDimensionLabelStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SimplicialLabellingOfBarycentricStageZeroStatement
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.SimplicialLabelRefinement

theorem exists_simpLab_refinement : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → ∃ φ lab : InvFun O, IsPolyFan bar q φ ∧ IsTwG w0 φ ∧ IsTwG w0 lab ∧ SimpLab bar q φ lab ∧ Subordinate bar q φ ψ := by
  intro O _ _ _ _ bar w0 hb q ψ hD hψ hT
  obtain ⟨lab, hlT, hlab⟩ := GlobalTheory.T.exists_carrier_dimension_label O bar w0 hb q ψ hD hψ hT
  obtain ⟨N, hN⟩ := GlobalTheory.T.carrier_dimension_label_bounded O bar hb q ψ lab hlab
  have key : ∀ d : ℕ, ∃ φ : InvFun O, IsTwG w0 φ ∧ IsBaryStage bar q ψ lab φ (N - d) := by
    intro d
    induction d with
    | zero => exact ⟨ψ, hT, isBaryStage_start hψ hN⟩
    | succ d ih =>
      obtain ⟨φ, hφT, hφ⟩ := ih
      rcases Nat.eq_zero_or_pos (N - d) with h | h
      · exact ⟨φ, hφT, by rw [show N - (d + 1) = N - d by omega]; exact hφ⟩
      · have e : N - d = (N - (d + 1)) + 1 := by omega
        rw [e] at hφ
        exact GlobalTheory.T.barycentric_stage_extension O bar w0 hb q ψ lab φ _ hD hψ hT hlT hlab hφT hφ
  obtain ⟨φ, hφT, hφ⟩ := key N
  rw [Nat.sub_self] at hφ
  exact ⟨φ, lab, hφ.1, hφT, hlT, GlobalTheory.T.simplicialLabelling_of_barycentricStage_zero _ bar q ψ lab φ hlab hφ, hφ.2.1⟩

end GlobalTheory.CompanionTheory.Ar.Fan.SimplicialLabelRefinement
