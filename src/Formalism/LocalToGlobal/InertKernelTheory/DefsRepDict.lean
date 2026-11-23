module

public import Formalism.LocalToGlobal.InertKernelTheory.DefsRep
public import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
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

namespace Formalism.L2.KerInert.Rep

open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def CurveDict : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ) (l : ℕ) [Fact l.Prime]
    (g : Formalism.MainNotions.GL3Theta.G1 l) (hLT : Formalism.L2.G.Pend.LTIso g),
    Formalism.MainNotions.GL3Theta.At D cc δ g → 5 ≤ l → Formalism.MainNotions.GL3Theta.InertK D l → Formalism.MainNotions.GL3Theta.ModelOverW g.lam g.abelian₂ g.C →
    ∃ g2 g3 ε s2 : MaximalUnramifiedExtension l, (g2 : ℂ_[l]) = Formalism.L2.Th1.A.g₂ g.W ∧ (g3 : ℂ_[l]) = Formalism.L2.Th1.A.g₃ g.W ∧
      (ε : ℂ_[l]) = (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹ ∧
      PowerSeries.rescale ((g.C.u⁻¹ : ℂ_[l]ˣ) : ℂ_[l]) (Formalism.MainNotions.TaylorLogMetric.sgSer g.lam g.abelian₂) =
        PowerSeries.C ((g.C.u⁻¹ : ℂ_[l]ˣ) : ℂ_[l]) * Formalism.L2.Th1.B.sgW g.W (s2 : ℂ_[l]) ∧
      ‖((g.C.u⁻¹ : ℂ_[l]ˣ) : ℂ_[l]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹‖ = 1 ∧
      CurveAt l (Formalism.L2.G.Pend.beLT hLT) g2 g3 ε s2 ∧
      ∀ D' : Formalism.BasicNotions.D7, DictInt D' g.lam g.abelian₂
        (((g.C.u⁻¹ : ℂ_[l]ˣ) : ℂ_[l]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹) g2 g3 s2 ε

end Formalism.L2.KerInert.Rep
