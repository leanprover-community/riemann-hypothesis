module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryOfPreservesHermitianTraceFormIntegralBasi
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

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo

theorem _root_.GlobalTheory.T.unitary_of_preserves_hermitianTraceForm_integralBasis : ∀ (I : AutInst) {N : ℕ} (e : Fin N → Fin I.n → I.E) (M : Matrix (Fin I.n) (Fin I.n) I.E), IsZBasis I e →
    (∀ i j, trForm I (M *ᵥ e i) (M *ᵥ e j) = trForm I (e i) (e j)) →
    Formalism.UG.cT (starRingEnd I.E) M * I.J * M = I.J := by
  first | exact @GlobalTheory.CuspGeo.unitary_of_trForm_zBasis | exact GlobalTheory.CuspGeo.unitary_of_trForm_zBasis | (intros; apply GlobalTheory.CuspGeo.unitary_of_trForm_zBasis <;> assumption)
