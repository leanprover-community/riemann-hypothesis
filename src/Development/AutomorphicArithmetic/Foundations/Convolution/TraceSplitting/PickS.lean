module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ParEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
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

open NumberField IsDedekindDomain Filter

theorem UpperTheory.ConvolutionTheory.T.pickS :
    UpperTheory.ConvolutionTheory.T.PickS := by
  classical
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ V Λ t hV hAt v
  obtain ⟨hInf, hUnr, hNe, -, -, -⟩ := UpperTheory.ConvolutionTheory.T.places F E hp
  obtain ⟨S₀, hS₀, hA⟩ := hAt
  obtain ⟨-, -, h0⟩ := UpperTheory.ConvolutionTheory.Dp.parEx E n hn μ V hV
  have hU := Filter.eventually_cofinite.1 hUnr
  have hfin := ((hS₀.image (fun w => w.under (𝓞 F))).union hU).union (Set.finite_singleton v)
  obtain ⟨q, hq, hqS⟩ := (hInf.diff hfin).nonempty
  have hsub : ∀ w, w.under (𝓞 F) ∉ hfin.toFinset → w ∉ S₀ := fun w hw hw0 =>
    hw (hfin.mem_toFinset.2 (Or.inl (Or.inl ⟨w, hw0, rfl⟩)))
  refine ⟨hfin.toFinset, q, (hNe q).some, hfin.mem_toFinset.2 (Or.inr rfl),
    fun h => hqS (hfin.mem_toFinset.1 h), hq, fun u hu => ?_, fun w hw => ?_, fun S' hS' => ?_⟩
  · by_contra h
    exact hu (hfin.mem_toFinset.2 (Or.inl (Or.inr h)))
  · exact (hA.2 w (hsub w hw)).2.1
  · have hS : ∀ w, w ∉ S' → w ∉ S₀ := fun w hw => hsub w fun h => hw ((hS' w).2 (Or.inl h))
    exact ⟨⟨hA.1, fun w hw => hA.2 w (hS w hw)⟩, fun τ => (hA.1 τ).1,
      fun w hw => ⟨(hA.2 w (hS w hw)).1, h0 w _ (hA.2 w (hS w hw))⟩⟩
