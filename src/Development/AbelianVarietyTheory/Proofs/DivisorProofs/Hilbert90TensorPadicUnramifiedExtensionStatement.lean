module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Hilbert90TensorPadicUnramifiedExtension
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

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_unit_of_frobenius_norm_one_tensor_Qr : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ), 0 < r → ∀ (B : Type) [CommRing B] [Algebra ℚ_[p] B] [Module.Finite ℚ_[p] B] (a : (B ⊗[ℚ_[p]] Qr p r)ˣ), nrmG (Units.map (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] B) (frobQ p r)).toRingHom.toMonoidHom) r a = 1 → ∃ g : (B ⊗[ℚ_[p]] Qr p r)ˣ, a = g⁻¹ * Units.map (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] B) (frobQ p r)).toRingHom.toMonoidHom g := by
  first | (exact @GlobalTheory.LKMid.hilbert90_frobenius_tensor_unramified_padic) | (exact GlobalTheory.LKMid.hilbert90_frobenius_tensor_unramified_padic) | (intros; apply GlobalTheory.LKMid.hilbert90_frobenius_tensor_unramified_padic  <;> assumption)
