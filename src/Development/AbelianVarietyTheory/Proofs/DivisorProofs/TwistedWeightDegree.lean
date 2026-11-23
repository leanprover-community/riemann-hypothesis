module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentRanksDegreesAddWithMassesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentsPeterssonOrthogonalAndMassesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormSupLatticeDegreeTwistLowerBoundStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsSupLatticeSplitOverComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistingSectionPreservesHermitianLatticesRanksStatement
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum



namespace GlobalTheory.Proof.TwistedWeightDegree

theorem degW_twist : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → ∀ (G₀ G : WTZ D.host.E) (s : ∀ Z : Comp Xo c, TwSec U (xiR D) Z G₀) (B : Finset ℕ) (τ : ℝ), Even G.2 → (∀ p ∈ B, p.Prime) → (∀ Z, IntOff B (s Z).lo) → (∀ Z, τ ≤ (s Z).degLo) → GoodW U (xiR D) V dict G → GoodW U (xiR D) V dict (G + G₀) ∧ rankW U (G + G₀) = rankW U G ∧ degW U (xiR D) V dict G + (rankW U G : ℝ) * (τ - logSum B) ≤ degW U (xiR D) V dict (G + G₀) := by
  intro D H Dw l Xo c r U V dict hC G₀ G s B τ hev hB hint hτ hG
  have hU : ∀ σ, GoodEmb c σ → IsUnf (U σ) := fun σ hσ => (hC.2 σ hσ).1
  have hA : ∀ G' : WTZ D.host.E, Adds U V dict G' := fun G' =>
    GlobalTheory.T.component_ranks_degrees_add_with_masses D H Dw l Xo c r U V dict G' (GlobalTheory.T.cuspForms_supLattice_split_over_components D H Dw l Xo c r U V dict hU G')
      ((GlobalTheory.T.components_peterssonOrthogonal_and_masses D H Dw l Xo c r U V dict hC G').1)
  have hOn : ∀ Z, GoodOn U (xiR D) V dict Z G := (hA G).1.1 hG
  have hgr : ∀ Z, GoodOn U (xiR D) V dict Z (G + G₀) ∧ rankOn U Z (G + G₀) = rankOn U Z G := fun Z =>
    GlobalTheory.T.twistingSection_preserves_hermitianLattices_ranks D.host.E H Dw l Xo c r U (xiR D) D V dict Z G₀ (s Z) G hU hev (hOn Z)
  have hG' : GoodW U (xiR D) V dict (G + G₀) := (hA (G + G₀)).1.2 (fun Z => (hgr Z).1)
  obtain ⟨-, hr1, -, -, hd1⟩ := (hA G).2 hG
  obtain ⟨-, hr2, -, -, hd2⟩ := (hA (G + G₀)).2 hG'
  have hrank : rankW U (G + G₀) = rankW U G := by
    rw [hr1, hr2]; exact finsum_congr fun Z => (hgr Z).2
  refine ⟨hG', hrank, ?_⟩
  haveI : Finite (Comp Xo c) := finite_comp
  letI := Fintype.ofFinite (Comp Xo c)
  have hZ : ∀ Z, degOn U (xiR D) V dict Z G + (rankOn U Z G : ℝ) * (τ - logSum B) ≤
      degOn U (xiR D) V dict Z (G + G₀) := fun Z => by
    have h1 := GlobalTheory.T.cuspForm_supLattice_degree_twist_lower_bound D.host.E H Dw l Xo c r U (xiR D) D V dict Z G₀ (s Z) G B hU hev hB (hint Z) (hOn Z)
    have h2 : (rankOn U Z G : ℝ) * (τ - logSum B) ≤ (rankOn U Z G : ℝ) * ((s Z).degLo - logSum B) :=
      mul_le_mul_of_nonneg_left (by linarith [hτ Z]) (Nat.cast_nonneg _)
    linarith
  rw [hd1, hd2, hr1]
  simp only [finsum_eq_sum_of_fintype, Nat.cast_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro Z _
  rw [(hgr Z).2]
  linarith [hZ Z]

end GlobalTheory.Proof.TwistedWeightDegree
