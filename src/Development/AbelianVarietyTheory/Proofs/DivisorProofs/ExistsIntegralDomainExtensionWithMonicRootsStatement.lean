module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralDomainExtensionWithMonicRoots
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

open Polynomial

theorem _root_.GlobalTheory.T.exists_integral_domain_extension_with_monic_roots : ∀ (D : Type) [CommRing D] [IsDomain D], ∃ (C : Type) (_ : CommRing C) (_ : Algebra D C), IsDomain C ∧ Algebra.IsIntegral D C ∧ Function.Injective (algebraMap D C) ∧ (∀ f : C[X], f.Monic → 0 < f.natDegree → ∃ y : C, f.eval y = 0) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (h : D →+* K), Function.Injective h → ∃ e : C →+* K, Function.Injective e ∧ e.comp (algebraMap D C) = h := by
  first | exact @GlobalTheory.exists_integral_domain_extension_monic_roots | exact GlobalTheory.exists_integral_domain_extension_monic_roots | (intros; apply GlobalTheory.exists_integral_domain_extension_monic_roots <;> assumption)
