module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PaddedLastEntry
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetOperatorBoundAtEmbeddingOfComplexOpNormSq
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.jetOperatorBound_at_embedding_of_complexOpNormSq : ∀ (K : Type) [Field K] [CharZero K] [StarRing K] (σ : K →+* ℂ) (ι : Type) [Fintype ι] (a b : ℕ) (lam nu : ι → DomWeight a) (lam' : ι → DomWeight b), (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.StepWeights (lam τ) (nu τ) (lam' τ)) → (JetInVV K lam lam' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) → (JetInVV ℂ lam lam' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) → ∀ (J : (DVar ι a b →₀ ℕ) → K) (J' : (DVar ι a b →₀ ℕ) → ℂ), (∀ e, (∀ τ, ((degAt e τ : ℕ) : ℤ) = ∑ i, (nu τ).w i) → σ (J e) = J' e) → ∀ t : ℝ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.OpNormSqLe lam lam' (jetOp lam lam' J' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) t → CoefOpLe σ lam lam' (jetOp lam lam' J fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) t := by
  first | exact @GlobalTheory.coefOpLe_jetOp_of_opNormSqLe | exact GlobalTheory.coefOpLe_jetOp_of_opNormSqLe | (intros; apply GlobalTheory.coefOpLe_jetOp_of_opNormSqLe <;> assumption)
