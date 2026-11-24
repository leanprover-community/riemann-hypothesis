module

public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2
public import GroundTheory.AutomorphicForms.L2LocalComponents.Summand
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.formsClosure :
    UpperTheory.ConvolutionTheory.Dp.FormsClosure := by
  intro K _ _ n μ _ U hU hs
  have hsup := sup_orthRel_centralCuspForms μ U hU hs.ρ hs.τ
  have hin : ∀ a b : cuspForms K n, inner ℂ (clsL μ a) (clsL μ b) = inner ℂ (cuspToL2 μ a) (cuspToL2 μ b) :=
    fun _ _ => rfl
  apply le_antisymm
  · rintro φ ⟨hφc, hφV⟩
    have hφc' := hφc
    rw [← hsup] at hφc'
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 hφc'
    have huV : clsL μ u ∈ (U.map (clsL μ)).topologicalClosure :=
      Submodule.le_topologicalClosure _ ⟨u, hu, rfl⟩
    have hcV : clsL μ c ∈ (U.map (clsL μ)).topologicalClosure := by
      have h : clsL μ (u + c) ∈ (U.map (clsL μ)).topologicalClosure := hφV
      rw [map_add (f := _)] at h
      simpa only [add_sub_cancel_left] using Submodule.sub_mem _ h huV
    have hle : U.map (clsL μ) ≤ (ℂ ∙ clsL μ c)ᗮ := by
      rintro _ ⟨v, hv, rfl⟩
      rw [Submodule.mem_orthogonal_singleton_iff_inner_left, hin]
      exact hc.2 v hv
    have h2 := Submodule.topologicalClosure_minimal _ hle (Submodule.isClosed_orthogonal _) hcV
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, hin, inner_self_eq_zero] at h2
    have h0 : c = 0 :=
      injOn_cuspToL2 μ (hc.1 : _) (fun _ _ => rfl) (h2.trans (map_zero (cuspToL2 μ)).symm)
    rw [h0, add_zero]
    exact hu
  · intro φ hφ
    exact ⟨hU hφ, Submodule.le_topologicalClosure _ ⟨φ, hφ, rfl⟩⟩
