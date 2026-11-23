module

public import Formalism.LocalToGlobal.HermitianColumns.TiedQC
public import Formalism.LocalToGlobal.HermitianColumns.HermCols
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

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure TwChJoint {D : D7} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop} (T : TwChTied D inQ)
    (H : HermCols D) : Prop where
  Uloc_off : ∀ u μ i (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : T.Ch u μ i) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∉ T.Q μ →
    (T.lev u μ i h1 hm β).Uloc v = (H.lev u i h1 hm).Uloc v
  Lb_off : ∀ u μ i (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : T.Ch u μ i) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∉ T.Q μ →
    locL v (T.lev u μ i h1 hm β).Lb = locL v (H.lev u i h1 hm).Lb
  Q_off : ∀ u μ, ∀ v ∈ T.Q μ, (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal ∧ ∀ a, (D.host.g a : 𝓞 D.host.F) ∉ v.asIdeal

def clsCast (D : D7) (u : D.what₂.Word) (i : ℕ) : (D.mem u).C.cls i ≃ (D.chTw u D.what₂.mu0).cls i :=
  Equiv.cast (congrArg (fun C => C.cls i) (D.memberColumns_twistedChain_base u).symm)

def yCast (D : D7) (u : D.what₂.Word) (i : ℕ) : (D.mem u).C.Y i ≃ (D.chTw u D.what₂.mu0).Y i :=
  Equiv.cast (congrArg (fun C => C.Y i) (D.memberColumns_twistedChain_base u).symm)

structure TwChMu0 {D : D7} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop} (T : TwChTied D inQ) : Prop where
  eY : ∀ u i hi, T.eY u D.what₂.mu0 i hi = yCast D u i
  eCls0 : ∀ u, T.eCls0 u D.what₂.mu0 = clsCast D u 0

end Formalism.L2.Herm

end
