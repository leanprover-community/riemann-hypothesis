module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem step_chars_unrAt : ∀ (D : D7) (c : Com D), c.Is → ∀ k < D.R.m, ∀ v ∉ c.S, ∀ w : HeightOneSpectrum (𝓞 D.host.E),
    w.under (𝓞 D.host.F) = v → UnrAt (c.chS (k + 1)) w ∧ UnrAt (c.chT (k + 1)) w := by
  intro D c hc k hk v hv w hw
  have hμ : UnrAt (c.μ (k + 1)) w := by
    have := hc.unr ⟨k, hk⟩ w
    exact this (by rw [GlobalTheory.LFun.above, Set.mem_setOf_eq, hw]; exact hv)
  have hη : UnrAt c.η⁻¹ w := (GlobalTheory.LFun.unrAt_of_unramEverywhere hc.chars.2.1 w).inv
  have hμη : UnrAt (c.μ (k + 1) * c.η⁻¹) w := hμ.mul hη
  unfold Com.chS Com.chT Lift.chrStep
  split_ifs <;> exact ⟨by assumption, by assumption⟩

end GlobalTheory.ChainOnto
