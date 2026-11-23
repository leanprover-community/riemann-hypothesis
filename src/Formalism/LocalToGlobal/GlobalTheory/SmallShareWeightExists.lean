module

public import Formalism.SharpRestriction.GlobalSchurBounds.LossesSmallShares
public import Formalism.LocalToGlobal.GlobalTheory.SuppSat
public import Formalism.SizeWindowBrackets.PrimeClassLossHypothesesSatisfiable
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Loss7

open Formalism.BasicNotions Formalism.MainNotions Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.PrimeWindowSizeBounds Formalism.LFunctionChainParameters.SmallOrderPrimeLosses Formalism.L2.GlobalTheoryTheory.Loss

def LossSettingFamily : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (X : G.Inst D L) (K : G.Consts) (Cr C bo : ℝ) (P : Par),
    PtH X K Cr → LinkG_at X K C bo → ParTie P L K C bo Cr → 0 ≤ bo → 0 ≤ L.LaG → L.sc.p0 D.R.k ≤ L.sc.X' →
    D.host.TT.Nonempty → ChBadp_at X → ChW_at X K →
    PrimeClassLossHypotheses P (PsAt L) (sAt L K) (largeOrderResiduePrimes L) (SizeData₂.lifts D) (TTv D) (badAt X)
      (fun p => G.Sig X K (G.aL L) (G.bL L) p) (fun (_ : Unit) p => G.ioP X K (G.aL L) (G.bL L) p)
      (fun _ => ldAt X K C bo)

def ThickDensitySizeWindowsForAllFamilies : Prop :=
  ∀ (eps : ℝ) (Fm : FamP eps), ChosenTT Fm → ChosenBadp Fm → LinkG Fm → Lnk.LossesSmallShares Fm

end Formalism.L2.GlobalTheoryTheory.Loss7

end
