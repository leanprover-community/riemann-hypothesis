module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.SpacesExOf
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped nonZeroDivisors Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.Gal.TP.Skew

theorem UpperTheory.Gal.TP.Skew.memDual :
    UpperTheory.Gal.TP.Skew.MemDual := by
  intro E _ _ z
  have h0 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  rw [FractionalIdeal.mem_dual h0]
  constructor
  · intro h o
    have h1 := h (algebraMap (𝓞 E) E o) ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)
    rw [Algebra.traceForm_apply, mul_comm] at h1
    obtain ⟨n, hn⟩ := h1
    have h2 : Algebra.trace ℚ E ((o : E) * z) = algebraMap ℤ ℚ n := hn.symm
    rw [h2]
    exact isIntegral_algebraMap
  · intro h a ha
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply, mul_comm]
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 (h o)
    exact ⟨n, hn⟩
