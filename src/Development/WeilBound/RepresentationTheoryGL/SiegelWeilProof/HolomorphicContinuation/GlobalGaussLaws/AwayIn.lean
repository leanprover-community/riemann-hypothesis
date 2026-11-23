module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpSt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayInA
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayInD
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Matrix ComplexConjugate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem awayIn : AwayIn := by
  intro D n V θ l s τ ε fr hθ hs hfr hl Ψ hΨ
  refine ⟨fun x x' hx hf => AwayPf.dep θ V l s τ hΨ x x' hx hf, fun f hf => ?_⟩
  induction hΨ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨p, g, hg, hp, rfl⟩ := hφ
    exact AwayPf.gen_sch θ V l s τ fr hfr.1 hs hl p hp g hg f hf
  | zero =>
    have : tens θ τ fr f (0 : Mx D V.rank n → ℂ) = 0 := by
      funext x
      simp [tens]
    rw [this]
    exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
    have : tens θ τ fr f (a + b) = tens θ τ fr f a + tens θ τ fr f b := by
      funext x
      simp only [tens, Pi.add_apply, mul_add]
    rw [this]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    have : tens θ τ fr f (c • a) = c • tens θ τ fr f a := by
      funext x
      simp only [tens, Pi.smul_apply, smul_eq_mul]
      ring
    rw [this]
    exact Submodule.smul_mem _ c ha

end PositivityTheory.Rg.Sw.Glob
