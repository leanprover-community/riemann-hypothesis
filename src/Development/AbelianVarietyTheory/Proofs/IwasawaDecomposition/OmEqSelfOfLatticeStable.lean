module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NotMemSpanOfCommute
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke

theorem om_eq_self_of_lattice_stable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (e : AE D), IsSplitIdem D e → ∀ (g : GA D S) (h : GA D T), SuppAt e S g → SuppAt e T h → ∀ x y, IsDetAt e S g x → IsDetAt e T h y → splitFacO χS χT x y = 1 → (∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), actO S T g⁻¹ h⁻¹ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True)) → ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), IsHalf e u ∨ IsHalf (cA D e) u → heisO ψ S T u f = f) → om (g, h) f = f := by
  intro D ψ S T χS χT om hW e he g h hg hh x y hx hy h1 hL f hf hfix
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hW.std (GlobalTheory.PlaceModel.isSelfDualC_latFrame S)
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame T)).1
  rw [GlobalTheory.PlaceModel.coe_latFrame, GlobalTheory.PlaceModel.coe_latFrame] at hdual
  have hfin := @GlobalTheory.SplitScalar.latO_fin D S T (L0c D S) (L0c D T)
  have key := om_eq_sum hW he hf hfix hg hh hx hy (R := {0})
    (fun u hu => by
      rw [Finset.mem_singleton.1 hu]
      exact ⟨hL 0 (zero_mem _), GlobalTheory.SplitScalar.isHalf_zero e⟩)
    (fun w hw hwe => by
      refine ⟨0, ⟨Finset.mem_singleton_self _, ?_⟩, fun v hv => Finset.mem_singleton.1 hv.1⟩
      rw [sub_zero, hdual w (GlobalTheory.SplitScalar.half_fin he hwe)]
      intro u hu
      rw [← symplO_actO S T g⁻¹ h⁻¹]
      exact (hdual _ (hfin hw)).1 hw _ (hL u hu))
    (fun w hw _ => hL w hw)
  rw [key, h1, Finset.sum_singleton, Finset.card_singleton, GlobalTheory.SplitScalar.heisO_zero]
  simp

end GlobalTheory.SplitHecke
