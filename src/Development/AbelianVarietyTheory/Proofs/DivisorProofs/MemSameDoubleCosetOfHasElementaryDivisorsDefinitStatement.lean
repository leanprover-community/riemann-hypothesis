module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSameDoubleCosetOfHasElementaryDivisorsDefinit
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_sameDoubleCoset_of_hasElementaryDivisors_definiteUnitary : ∀ (D : D7) [IsCMField D.host.E] (n : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ)
    (x y : UA D.host.E n), x ∈ locU n P → y ∈ locU n P →
    HasDiv (Ov D.host.E P) d (cLoc P x) → HasDiv (Ov D.host.E P) d (cLoc P y) →
    ∃ k₁ ∈ KP (D := D) n P, ∃ k₂ ∈ KP (D := D) n P, y = k₁ * x * k₂ := by
  first | exact @GlobalTheory.LocalCartan.doubleCoset_of_hasDiv | exact GlobalTheory.LocalCartan.doubleCoset_of_hasDiv | (intros; apply GlobalTheory.LocalCartan.doubleCoset_of_hasDiv <;> assumption)
