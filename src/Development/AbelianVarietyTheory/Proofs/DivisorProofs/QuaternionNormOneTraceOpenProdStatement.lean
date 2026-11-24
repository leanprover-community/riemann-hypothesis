module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneTraceOpenProd
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

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

theorem _root_.GlobalTheory.T.quaternionNormOneTraceOpen_prod : ∀ (R₁ R₂ : Type) [CommRing R₁] [TopologicalSpace R₁] [CommRing R₂] [TopologicalSpace R₂] (a₁ b₁ : R₁) (a₂ b₂ : R₂), TraceOpen R₁ a₁ b₁ → TraceOpen R₂ a₂ b₂ → TraceOpen (R₁ × R₂) (a₁, a₂) (b₁, b₂) := by
  first | exact @GlobalTheory.QSA.traceOpen_prod | exact GlobalTheory.QSA.traceOpen_prod | (intros; apply GlobalTheory.QSA.traceOpen_prod <;> assumption)
