module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem etale_isLocalHomeomorph : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → IsLocalHomeomorph (fun y : U => z y) := by
  intro n Y _ _ _ _ _ ι La _ A U z hE
  apply IsLocalHomeomorph.mk
  intro y
  set i := A.pick y
  set e := A.chart i
  set S : Set (V n) := e.target ∩ e.symm ⁻¹' U with hSdef
  have hS : IsOpen S := e.isOpen_inter_preimage_symm hE.isOpen
  have hyU : (y : Y) ∈ U := y.2
  have hys : (y : Y) ∈ e.source := A.mem_pick y
  have hxS : e y ∈ S := ⟨e.map_source hys, by simp [e.left_inv hys, hyU]⟩
  have hd : DifferentiableOn ℂ (z ∘ e.symm) S := hE.holo i
  have hcd : ContDiffOn ℂ ∞ (z ∘ e.symm) S :=
    contDiffOn_piLp' 2 (fun k => contDiffOn_of_differentiableOn n _ S hS
      ((differentiableOn_piLp 2).1 hd k))
  have hca : ContDiffAt ℂ ∞ (z ∘ e.symm) (e y) := hcd.contDiffAt (hS.mem_nhds hxS)
  have hst := hca.hasStrictFDerivAt_fderiv (by simp)
  have hdet : (fderiv ℂ (z ∘ e.symm) (e y)).det ≠ 0 := hE.det_ne i y hyU hys
  let L : V n ≃L[ℂ] V n :=
    (LinearMap.equivOfDetNeZero ((fderiv ℂ (z ∘ e.symm) (e y)) : V n →ₗ[ℂ] V n) hdet).toContinuousLinearEquiv
  have hL : ((L : V n →L[ℂ] V n)) = fderiv ℂ (z ∘ e.symm) (e y) := by
    ext v; rfl
  have hst' : HasStrictFDerivAt (z ∘ e.symm) (L : V n →L[ℂ] V n) (e y) := hL ▸ hst
  let h := hst'.toOpenPartialHomeomorph (z ∘ e.symm)
  let P := e.trans (h.restrOpen S hS)
  have hyP : (y : Y) ∈ P.source := by
    simp only [P, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.restrOpen_source,
      Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨hys, hst'.mem_toOpenPartialHomeomorph_source, hxS⟩
  have hPz : ∀ w ∈ P.source, P w = z w := by
    intro w hw
    have hw1 : w ∈ e.source := by
      simp only [P, OpenPartialHomeomorph.trans_source] at hw; exact hw.1
    have hh : ∀ v, h v = (z ∘ e.symm) v := fun v => by
      simp only [h, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
    change (h.restrOpen S hS) (e w) = z w
    change h (e w) = z w
    rw [hh, Function.comp_apply, e.left_inv hw1]
  have hne : Nonempty (⟨U, hE.isOpen⟩ : TopologicalSpace.Opens Y) := ⟨y⟩
  let Q := P.subtypeRestr hne
  refine ⟨Q, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact hyP
  · intro w hw
    rw [OpenPartialHomeomorph.subtypeRestr_source] at hw
    rw [OpenPartialHomeomorph.subtypeRestr_coe]
    exact (hPz w hw).symm

end GlobalTheory.OTY
