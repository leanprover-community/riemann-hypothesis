module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.KillComp
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.Langlands
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.NearDat
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.RhoLe
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField

theorem UpperTheory.ConvolutionTheory.BW.funKill :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.FunKill E := by
  intro E _ _ _ S n ρ C hC
  obtain ⟨B, hB⟩ := far E n C hC
  obtain ⟨D₀, hfin, hD₀⟩ := nearDat E S n ρ B
  refine ⟨{d ∈ D₀ | 2 ≤ d.len}, hfin.subset (Set.sep_subset _ _), fun d hd => hd.2, ?_⟩
  intro φ w F G hφ hSφ hw hK hSw hF hD hG hsum
  refine (langlands E S n ρ w hw hK hSw).2 ?_
  intro k d hd hlen
  refine killComp E S n C φ w F G hC hφ hSφ hw hF hG hsum k d ?_
  by_cases hfar : ∃ τ i, B < ‖d.lam τ i‖
  · exact Or.inr fun ψ hψ hSψ => hB S d ψ hψ hSψ hfar
  · push_neg at hfar
    obtain ⟨d', hd', hl, hk⟩ := hD₀ d hd hfar
    exact Or.inl (hk F hF (hD d' ⟨hd', hl ▸ hlen⟩))
