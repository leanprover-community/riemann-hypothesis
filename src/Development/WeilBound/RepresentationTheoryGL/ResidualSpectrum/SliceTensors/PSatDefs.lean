module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace PositivityTheory.Rg.Rs.SatakeVectors

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem absNorm_cpow_ne_zero (w : HeightOneSpectrum (𝓞 E)) (s : ℂ) :
    (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ s) ≠ 0 := by
  have h : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (NumberField.HeightOneSpectrum.one_lt_absNorm w).ne_bot
  exact fun e => h ((Complex.cpow_eq_zero_iff _ _).1 e).1

def qU (w : HeightOneSpectrum (𝓞 E)) (s : ℂ) : ℂˣ :=
  Units.mk0 (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ s) (absNorm_cpow_ne_zero w s)

@[simp] theorem qU_val (w : HeightOneSpectrum (𝓞 E)) (s : ℂ) :
    ((qU w s : ℂˣ) : ℂ) = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ s := rfl

def SatLike {m : ℕ} (U : Submodule ℂ (Sm E m)) (w : HeightOneSpectrum (𝓞 E)) (S : Multiset ℂˣ) : Prop :=
  ∀ ψ ∈ U, (∀ k ∈ GlobalTheory.LFun.KGL w (n := m), finRep E m (locGL E m w k) ψ = ψ) → ψ ≠ 0 →
    GlobalTheory.LFun.IsSatVecGL w ((finRep E m).comp (locGL E m w)) ψ S

theorem satLike_of_satV {m : ℕ} {V : Submodule ℂ (Sm E m)} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}
    (h : SatV V w B) : SatLike V w B := h.2

theorem satTw_eq (w : HeightOneSpectrum (𝓞 E)) (z : ℂ) (B : Multiset ℂˣ) :
    satTw w z B = (B.map (· * qU w (-z))).map fun b : ℂˣ => (b : ℂ) := by
  simp [satTw, Multiset.map_map, Function.comp_def]

end PositivityTheory.Rg.Rs.SatakeVectors

end
