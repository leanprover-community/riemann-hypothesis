module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.PeriodIntegrals.LocFramePrim
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.HidaSetting
open scoped TensorProduct Classical

namespace ChkLocFramePrim

theorem primX_of (hS : PI.LocFramePrim.Statement) {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (w : D.what₂.Word)
    (Lb : Submodule (𝓞 X.B.I.E) (Fin X.B.I.n → X.B.I.E))
    (hFG : X.B.I.L.FG)
    (hsplit : X.B.I.L =
      PI.LocFramePrim.latSpan (fun a : Fin D.R.rS => PI.LocFramePrim.ddE X.B.I.F ^ (-((D.R.rS : ℤ) - (a : ℕ))))
          (frameOf X w).e ⊔ Lb ⊔
        PI.LocFramePrim.latSpan (fun a : Fin D.R.rS => (PI.LocFramePrim.ddE X.B.I.F ^ (-((D.R.rS : ℤ) - (a : ℕ))))⁻¹)
          (frameOf X w).f)
    (hind : LinearIndependent X.B.I.E (Fin.append (frameOf X w).e (frameOf X w).f))
    (hdir : ∀ y ∈ Lb, y ∈ Submodule.span X.B.I.E (Set.range (frameOf X w).e ∪ Set.range (frameOf X w).f) → y = 0)
    (hz : (frameOf X w).z ∈ Lb)
    (hzp : ∀ c : X.B.I.E, c • (frameOf X w).z ∈ Lb → ∃ o : 𝓞 X.B.I.E, (o : X.B.I.E) = c) :
    PrimX X w := fun v =>
  hS X.B.I.F X.B.I.E v X.B.I.n D.R.rS X.B.I.L Lb (frameOf X w).e (frameOf X w).f (frameOf X w).z
    hFG hsplit hind hdir hz hzp

end ChkLocFramePrim
