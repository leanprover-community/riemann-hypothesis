module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantApply
public import Mathlib.FieldTheory.IsSepClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisLocallyConstantTupleRingTensorPowerUnivers
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
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.galoisLocallyConstantTupleRing_tensorPower_universal : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ) (B : Type) [CommRing B] (g : Fin (k + 1) → (Ω →+* B)) (c : K →+* B), (∀ i, (g i).comp (algebraMap K Ω) = c) → ∃! u : GlobalTheory.EtC.GalSec.LCRing K Ω k →+* B, u.comp (GlobalTheory.EtC.GalSec.baseHom K Ω k) = c ∧ ∀ i, u.comp (GlobalTheory.EtC.GalSec.legHom K Ω k i) = g i := by
  first | (exact @GlobalTheory.EtC.GalSec.Tens.lcRing_universal) | (exact GlobalTheory.EtC.GalSec.Tens.lcRing_universal) | (intros; apply GlobalTheory.EtC.GalSec.Tens.lcRing_universal  <;> assumption)
