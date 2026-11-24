module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.TranslInv
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseOrbits.MainE
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseOrbits.OneDim
public import GroundTheory.AutomorphicForms.WhittakerDistribution
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

open Matrix GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.TP.Nil.Base

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.BasePf PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem van_of {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (h0 : dB0 Z = 0) : Van Z := by
  intro ξ hS hI
  have : TotallyDisconnectedSpace k := totallyDisconnectedSpace_localField
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) k) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → k))
  have : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  have : T2Space (Matrix (Fin n) (Fin n) k) := inferInstanceAs (T2Space (Fin n → Fin n → k))
  intro f hf
  have hle : supportedIn {p : Sp k n | p.2 ≠ 0} ≤ LinearMap.ker ξ := supportedIn_le_of_local fun p hp => by
    obtain ⟨e, he, hee, hev, hprim⟩ := prim Z hZ.1 hZ.2 p.2 hp
    refine ⟨{q : Sp k n | e *ᵥ q.2 ≠ 0}, ?_, hev, fun g hg =>
      LinearMap.mem_ker.2 (mainE Z hZ h0 e he hee hprim p.2 hev ξ hS hI g hg)⟩
    exact isOpen_ne_fun (continuous_const.matrix_mulVec continuous_snd) continuous_const
  exact LinearMap.mem_ker.1 (hle hf)

theorem baseQ : BaseQ k := by
  intro n Z hZ h0 ξ hS hI
  refine van_of k Z hZ h0 ξ (fun f hf hf0 => hS f hf fun p hp => hf0 p ⟨hp.1.1, hp.2⟩) hI

end PositivityTheory.RgUd.TP.Nil.Base

end
