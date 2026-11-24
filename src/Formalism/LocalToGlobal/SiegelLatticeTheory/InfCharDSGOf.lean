module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.GgExistsAddCharNeOne
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.DiagonalEntryIdentity

@[expose] public section

noncomputable section

open MeasureTheory Matrix Filter Topology Finset
open scoped InnerProductSpace ContDiff Convolution ComplexOrder

namespace Formalism.MainNotions.GapDS

open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.S.UnitaryLevelOperators Formalism.QuantumDeterminants

def InfCharDSG : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → Formalism.MainNotions.S.IsDS ε lam σ →
    ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h → thrX ε < h →
    ∀ v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) σ, ∀ Y : ℂ,
      Formalism.L2.SG.LitS.actU ε σ (Formalism.REAL.qdet (Formalism.L2.SG.LitS.Egl n) (Y + ((n : ℂ) - 1) / 2)) v =
        Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • v

end Formalism.MainNotions.GapDS
