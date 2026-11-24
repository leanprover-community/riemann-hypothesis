module

public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothConjugateInverseMem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec PositivityTheory.PRW.GKD

theorem _root_.GlobalTheory.T.smooth_conjugate_inverse_mem : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}, ∀ {φ : GA E a → ℂ}, φ ∈ Sm E a → (fun g => star (φ (invA E a g))) ∈ Sm E a := by
  first | exact @GlobalTheory.CompanionTheory.DualSm.conj_invA_mem_Sm | exact GlobalTheory.CompanionTheory.DualSm.conj_invA_mem_Sm | (intros; apply GlobalTheory.CompanionTheory.DualSm.conj_invA_mem_Sm <;> assumption)
