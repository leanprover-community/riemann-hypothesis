module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.DictKAOfParts
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

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SWDict

open PositivityTheory.PfSWUS GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd

theorem dictKA_of_parts : PositivityTheory.PfSWUS.DictKAOfParts := by
  intro hF hW hI hM D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k hk
  obtain ⟨N, φs, hsum, hmono⟩ := hF D n V ψ χ θ μ ω H l s ν Φ hS hR k hk
  refine ⟨N, φs, fun j => npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) - n) *
    IfrB V ν (fun x => φs j (HMul.hMul x a.1)) β, ?_, ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hW D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k N φs hmono
    exact ⟨t, fun z hz => by rw [hsum]; exact ht z hz⟩
  · rw [hsum, hI D n V ψ χ θ μ ω H l s ν Φ hS hR β hβ a N φs hmono, Finset.mul_sum]
  · exact fun j => hM D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k hk (φs j) (hmono j)

end GlobalTheory.CompanionTheory.SWDict

end
