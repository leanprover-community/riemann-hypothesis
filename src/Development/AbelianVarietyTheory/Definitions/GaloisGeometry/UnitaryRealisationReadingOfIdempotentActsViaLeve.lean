module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

noncomputable section

namespace GlobalTheory.NRows.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.RowCopy

variable {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch}
  (X : GlobalTheory.NJoin.RealAt D cf nch tp)


theorem unitaryRealisationReading_of_idempotent_acts_via_levelGroup {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch}
    (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (h : ∀ μ (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (f : D.what₂.Mt μ (j.1 + 1))
      (l : (X.R.cV j).W →ₗ[ℂ] ℂ),
      Formalism.IndefR.Links.gaL (Formalism.IndefR.Links.Vc D j) (X.R.βV j) (X.R.datVt j (X.tupT μ)) X.R.eG
        (Formalism.IndefR.Links.RealDat.eC (A := X.A) (Formalism.IndefR.Links.sg0 D X.A)) (fun g => l (X.fn hμ j f g)) =
        fun g => l (X.fn hμ j (D.ntypes.onMt μ (j.1 + 1) D.ntypes.e0 f) g)) : GoodIdempotentReadsAsGoodTypeProjector X := by
  intro μ hμ j f y hy
  unfold GlobalTheory.DownLift.GoodVt
  rw [hy]
  constructor
  · intro hf l
    rw [h μ hμ j f l, hf]
  · intro hg
    apply (X.IL.jMt μ hμ j).injective
    apply Subtype.ext
    funext g
    have key : ∀ l : (X.R.cV j).W →ₗ[ℂ] ℂ,
        l (X.fn hμ j (D.ntypes.onMt μ (j.1 + 1) D.ntypes.e0 f) g - X.fn hμ j f g) = 0 := fun l => by
      rw [map_sub, sub_eq_zero]
      exact congrFun ((h μ hμ j f l).symm.trans (hg l)) g
    exact sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ (V := (X.R.cV j).W) _).1 key)

end GlobalTheory.NRows.Model

end
