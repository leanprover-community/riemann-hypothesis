module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import GroundTheory.AutomorphicForms.GeometricLemmaNormal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RefinedBlockOrderCompat
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

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

theorem _root_.GlobalTheory.T.refined_block_order_compat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {c : α → β' → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (e : (Σ i, m i) ≃ Fin N) (f : ∀ i, (Σ j, c i j) ≃ m i) (β δ : Fin N → ℕ) (hβ : ∀ x y, β x < β y ↔ blk e x < blk e y) (hδ : ∀ i j j' (t : c i j) (t' : c i j'), δ (e ⟨i, f i ⟨j, t⟩⟩) < δ (e ⟨i, f i ⟨j', t'⟩⟩) ↔ j < j') (hmem : ∀ x : Levi k m, x ∈ relParab k f ↔ leviEmb k e x ∈ blockUpper k N δ) (φ : Levi k m ≃* levi k N β) (hφ : ∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) (x : Levi k m) (hx : x ∈ relParab k f) (h : ((φ x : levi k N β) : GL (Fin N) k) ∈ leviPar k N β δ), normLeviParSqrtModular k β δ ⟨_, h⟩ = ((relDeltaHalf k c (relProj k f ⟨x, hx⟩) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.CellChar.normLeviParSqrtModular_eq_relDeltaHalf | exact GlobalTheory.CompanionTheory.CellChar.normLeviParSqrtModular_eq_relDeltaHalf | (intros; apply GlobalTheory.CompanionTheory.CellChar.normLeviParSqrtModular_eq_relDeltaHalf <;> assumption)
