module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGroupStructuresPermConjInvariant
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients

@[expose] public section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder

theorem _root_.GlobalTheory.T.unitaryGroup_structures_perm_conj_invariant : ∀ (n : ℕ) (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)), (∀ g : Matrix (Fin n) (Fin n) ℂ, (g ∈ UJset (ε ∘ s) ↔ g.submatrix s.symm s.symm ∈ UJset ε) ∧ (g ∈ Kset (ε ∘ s) ↔ g.submatrix s.symm s.symm ∈ Kset ε) ∧ (inP (ε ∘ s) g ↔ inP ε (g.submatrix s.symm s.symm)) ∧ NormedSpace.exp (g.submatrix s.symm s.symm) = (NormedSpace.exp g).submatrix s.symm s.symm) ∧ ∀ (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (p : ENNReal), (MemLp (fun g : UJ ε => f (umat g)) p (muG ε) ↔ MemLp (fun g : UJ (ε ∘ s) => f ((umat g).submatrix s.symm s.symm)) p (muG (ε ∘ s))) ∧ (MemLp (fun g : UJ ε => f (umat g)) p (muG ε) ↔ MemLp (fun g : UJ ε => f ((umat g).map star)) p (muG ε)) := by
  first | exact @GlobalTheory.Dec.PermGroup.permGroup | exact GlobalTheory.Dec.PermGroup.permGroup | (intros; apply GlobalTheory.Dec.PermGroup.permGroup <;> assumption)
