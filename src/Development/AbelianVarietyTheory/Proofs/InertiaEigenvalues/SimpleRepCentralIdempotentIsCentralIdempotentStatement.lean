module

public import Formalism.PadicSubsetSums.CentralIdempotents.IsConstituent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SimpleRepCentralIdempotentIsCentralIdempotent
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
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory

theorem _root_.GlobalTheory.T.simpleRepCentralIdempotent_isCentralIdempotent : ∀ {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ), Simple τ → zIdem τ * zIdem τ = zIdem τ ∧ ∀ a, zIdem τ * a = a * zIdem τ := by
  first | exact @GlobalTheory.SerOSys.zIdem_centralIdempotent | exact GlobalTheory.SerOSys.zIdem_centralIdempotent | (intros; apply GlobalTheory.SerOSys.zIdem_centralIdempotent <;> assumption)
