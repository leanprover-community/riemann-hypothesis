module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceFormSpanRepNondegenerateMapRepIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LatticeConditions

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

theorem _root_.GlobalTheory.T.traceForm_nondegenerate_span_mapRep_iff : ∀ (Γ K L : Type) [Group Γ] [Field K] [Field L] (f : K →+* L) (a : ℕ) (ρ : Γ →* GL (Fin a) K), (∀ x ∈ Submodule.span L (Set.range fun g => ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)), (∀ g, (x * ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)).trace = 0) → x = 0) ↔ (∀ x ∈ Submodule.span K (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)), (∀ g, (x * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).trace = 0) → x = 0) := by
  first | exact @GlobalTheory.traceForm_span_rep_nondegenerate_mapRep_iff | exact GlobalTheory.traceForm_span_rep_nondegenerate_mapRep_iff | (intros; apply GlobalTheory.traceForm_span_rep_nondegenerate_mapRep_iff <;> assumption)
