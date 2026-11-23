module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportSelfDualDataOneHermitianSpace
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

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.exists_transport_selfDual_data_one_hermitianSpace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (r : ℕ) (Y Y' : ReciprocityTheory.ChartRestriction.G.FD.Data E r), (∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0) → Y'.Ψ = Y.Ψ → Y'.p0 = Y.p0 → 1 ≤ Y.p0 → Y.p0 < r → GlobalTheory.EqCovol.IsLevGrp l Y' → GlobalTheory.EqCovol.IsSelfDualTr Y → GlobalTheory.EqCovol.IsSelfDualTr Y' → ∃ Y'' : ReciprocityTheory.ChartRestriction.G.FD.Data E r, Y''.Ψ = Y.Ψ ∧ Y''.Gm = Y.Gm ∧ Y''.ξ0 = Y.ξ0 ∧ Y''.p0 = Y.p0 ∧ GlobalTheory.EqCovol.IsLevGrp l Y'' ∧ GlobalTheory.EqCovol.IsSelfDualTr Y'' ∧ GlobalTheory.TrueCx.covol Y'' = GlobalTheory.TrueCx.covol Y' := by
  first | exact @GlobalTheory.EqCovol.exists_transport | exact GlobalTheory.EqCovol.exists_transport | (intros; apply GlobalTheory.EqCovol.exists_transport <;> assumption)
