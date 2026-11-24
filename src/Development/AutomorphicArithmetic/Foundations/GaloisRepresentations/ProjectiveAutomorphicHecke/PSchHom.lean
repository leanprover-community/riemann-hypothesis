module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CharConj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClrHolds
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pSchHom_of :
    UpperTheory.Gal.CertificateRingHomMap.SchHom := by
  intro n t _
  refine ⟨fun lam c _ => UpperTheory.Gal.Schur.SchurHomog_holds ℂ n lam t c, fun m => ?_⟩
  obtain ⟨h0, h1⟩ := UpperTheory.Gal.Schur.SchurDet_holds ℂ n t
  have h := h1 (fun _ => 0) m
  simp only [zero_add] at h
  rw [h, h0, mul_one]
