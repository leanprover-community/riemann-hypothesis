module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardThetaDatumEigenvectorBlockLevel
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)


theorem _root_.GlobalTheory.T.standardThetaDatum_eigenvector_blockLevel : ∀ (D : D7) (δ t0 : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), oddE0 D ⊤ δ t0 a d e0 → a ≤ d → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → (∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) → ∀ R : Finset (GA D a), (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) → (∀ k ∈ intG D a, W.Om k 1 (stdSum W 𝔪 0 R) = stdSum W 𝔪 0 R) → ∀ h ∈ blockLev D 𝔪 d a, ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om 1 h (stdSum W 𝔪 0 R) = c • stdSum W 𝔪 0 R := by
  first | exact @GlobalTheory.FunObj.StdDatum.CapelliMinorMembership.stdSum_eig | exact GlobalTheory.FunObj.StdDatum.CapelliMinorMembership.stdSum_eig | (intros; apply GlobalTheory.FunObj.StdDatum.CapelliMinorMembership.stdSum_eig <;> assumption)
