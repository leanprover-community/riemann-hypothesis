module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitLocF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureSplitCongruenceIdelesOfFinPartEqOne
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

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mem_closure_split_congruence_ideles_of_finPart_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N : ℕ), 0 < N → ∀ z : (AF F ⊗[F] E)ˣ, finPartF F E (z : AF F ⊗[F] E) = 1 → z ∈ closure (GlobalTheory.HeckeSplitGen.grpHF σ N : Set (AF F ⊗[F] E)ˣ) := by
  first | exact @GlobalTheory.HeckeSplitGen.mem_closure_grpHF_of_finPart_eq_one | exact GlobalTheory.HeckeSplitGen.mem_closure_grpHF_of_finPart_eq_one | (intros; apply GlobalTheory.HeckeSplitGen.mem_closure_grpHF_of_finPart_eq_one <;> assumption)
