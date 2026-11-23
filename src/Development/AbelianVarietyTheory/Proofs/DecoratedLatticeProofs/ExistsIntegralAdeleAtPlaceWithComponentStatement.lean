module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SigV
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralAdeleAtPlaceWithComponent
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_integralAdele_atPlace_with_component : ∀ (D : D7) (v : Pl D) (z : Fv D.host.F v ⊗[D.host.F] D.host.E), z ∈ intV D v → ∃ x ∈ intAt D (· = v), compAt D v x = z := by
  first | exact @GlobalTheory.FixedUnitNorm.exists_intAt_compAt_eq | exact GlobalTheory.FixedUnitNorm.exists_intAt_compAt_eq | (intros; apply GlobalTheory.FixedUnitNorm.exists_intAt_compAt_eq <;> assumption)
