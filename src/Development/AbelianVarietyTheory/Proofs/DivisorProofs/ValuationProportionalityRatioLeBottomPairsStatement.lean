module

public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationProportionalityRatioLeBottomPairs
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.valuation_proportionalityRatio_le_bottomPairs : ∀ (D : D7) (N : ℕ) (B : ℝ) (Q : ℕ) (S : Finset ℕ) (del_vp : ℕ → ℝ) (b : ℝ), GlobalTheory.NormSum.Inp D →
    GlobalTheory.NormSum.Exponents S del_vp b → GlobalTheory.NormSum.CoordInt D N B Q del_vp →
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (w : Formalism.PairingDivisionLocalBalance.Pl K) (p : ℕ) [Fact p.Prime],
    (p : 𝓞 K) ∈ w.asIdeal → ∀ (δ t0 : ℂ) (Q₁ Q₂ : ℕ), padicValNat p Q₁ ≤ padicValNat p Q →
    padicValNat p Q₂ ≤ padicValNat p Q →
    ∀ (P₁ P₁' : Pair D ⊤ δ t0 Q₁) (P₂ P₂' : Pair D ⊤ δ t0 Q₂), P₁.Small N B → P₁'.Small N B → P₂.Small N B →
    P₂'.Small N B → ∀ (hd₁ : P₁'.d = P₁.d) (hd₂ : P₂'.d = P₂.d) (b₁ b₂ v : ℂ)
    (M₁ : Tup D P₁.a P₁.d P₁.n → Tup D P₁'.a P₁'.d P₁'.n → ℤ) (M₂ : Tup D P₂'.a P₂'.d P₂'.n → Tup D P₂.a P₂.d P₂.n → ℤ),
    (∀ (h : GA D P₁.d) T, starRingEnd ℂ (P₁.coord h T) = b₁ * ∑ T', (M₁ T T' : ℂ) * P₁'.coord (hd₁ ▸ h) T') →
    (∀ (h : GA D P₂.d) T', P₂'.coord (hd₂ ▸ h) T' * b₂ = ∑ T, (M₂ T' T : ℂ) * starRingEnd ℂ (P₂.coord h T)) →
    b₂ ≠ 0 → v ∈ Qbar → (∀ lam : Qbar →+* ℂ_[p], ‖lamC lam v‖ = 1) →
    ∀ (γ z z' : K), b₁ = σ γ * b₂ * v → σ z = (P₁.norm : ℂ) → σ z' = (P₂'.norm : ℂ) → z ≠ 0 → z' ≠ 0 →
    (vw w γ : ℝ) ≤ vw w z + vw w z' + 6 * Formalism.PairingDivisionLocalBalance.wt S del_vp w := by
  first | exact @GlobalTheory.NormSum.LemmaC.vw_le_of_bottom_pairs | exact GlobalTheory.NormSum.LemmaC.vw_le_of_bottom_pairs | (intros; apply GlobalTheory.NormSum.LemmaC.vw_le_of_bottom_pairs <;> assumption)
