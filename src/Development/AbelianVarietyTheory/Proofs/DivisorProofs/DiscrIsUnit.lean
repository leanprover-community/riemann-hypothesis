module

public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Etale.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfEtaleAtHeightOnePrimes
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

open IsLocalRing

open TensorProduct

namespace GlobalTheory.EtaleCoker

theorem discr_isUnit (S A : Type) [CommRing S] [IsLocalRing S] [CommRing A] [Algebra S A]
    [Algebra.Etale S A] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι S A) :
    IsUnit (Algebra.discr S b) := by
  have h := GlobalTheory.PurityDisc.discr_ne_zero_of_etale (ResidueField S) (ResidueField S ⊗[S] A)
    (Algebra.TensorProduct.basis (ResidueField S) b)
  rw [GlobalTheory.PurityDisc.discr_baseChange] at h
  by_contra hn
  exact h ((residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr hn))

end GlobalTheory.EtaleCoker
