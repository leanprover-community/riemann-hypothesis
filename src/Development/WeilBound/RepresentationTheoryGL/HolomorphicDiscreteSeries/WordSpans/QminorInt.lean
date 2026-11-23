module

import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLExistsOfAlg
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.WordSpan
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.RrCompCastSucc
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix Finset

namespace PositivityTheory.RgHe.SM

open Formalism.REAL Formalism.FourierDecayAlt.P.CapelliAbstractCharacter

theorem qminor_int {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {n t : ℕ}
    {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ V'} (f : V →ₗ[ℂ] V')
    (hf : ∀ a b x, f (E a b x) = E' a b (f x)) (a b : Fin t → Fin n) (u : ℂ) (x : V) :
    f (qminor E a b u x) = qminor E' a b u (f x) := by
  apply Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA.qminor_int <;> assumption

theorem thMap : ThMap := by
  intro V V' _ _ _ _ N E E' f hf u X x
  refine ⟨?_, qminor_int f hf _ _ _ _⟩

  simp only [Th, LinearMap.pi_apply, LinearMap.sum_apply, map_sum,
  LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, qminor_int f hf]

theorem keyId : KeyId := by
  intro V V' _ _ _ _ N E E' ι z f hE hι hz hf w cG hdet h0 v
  have h := congrArg f (algId V N E ι z hE hι hz (w + 1) v)
  rw [hdet] at h
  have hw : w + 1 - 1 = w := by ring
  rw [hw] at h
  have hT := thMap V V' N (fun a b => E (ι a) (ι b)) E' f hf w
  have hq : ∀ y, f (qdet (fun a b => E (ι a) (ι b)) w y) = 0 := by
    intro y
    rw [(hT (fun _ => y) 0).2]
    exact h0 _

  rw [← LinearMap.map_smul, h, map_sub, map_sum, hq, zero_sub]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  exact (hT _ c).1

end PositivityTheory.RgHe.SM
