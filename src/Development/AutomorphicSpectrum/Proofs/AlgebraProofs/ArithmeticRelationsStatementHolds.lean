module

public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.RelationsStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DescentRelationsFromModelsStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UniformizerModelPermModuleLatticeStatement
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

namespace GlobalTheory.CompanionTheory.Ar.Num.TopRel

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

theorem relations : GlobalTheory.CompanionTheory.Ar.Num.RelationsStatement := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x _ ϖ hϖ d hmod hfn F _ _ _ n Sg _ r s p hp w χ φ D hD Lie W Om OmHT hB lie om hflag
  have hck := GlobalTheory.T.lattice_family_ckRelations O Ω K ι x d hmod hfn p hp w χ φ D hD Lie W Om OmHT hB
  have hp0 : (p : O) ≠ 0 := hD.char.1
  have hw0 : w ≠ 0 := by
    rintro rfl
    obtain ⟨u, hu, he⟩ := hD.char.2.1
    have h1 : p - 1 ≠ 0 := by have := hp.two_le; omega
    rw [zero_pow h1] at he
    exact hp0 (by
      rcases mul_eq_zero.mp he.symm with h | h
      · exact absurd h hu.ne_zero
      · exact h)
  have hsame : ∀ τ, SameGeneric O x (Lie τ) (W τ) ∧ SameGeneric O x (Om τ) (OmHT τ) := by
    intro τ
    constructor
    · intro c hc
      obtain ⟨h1, h2, -, -⟩ := hB τ c hc
      have hinc := ((hD.base c hc).incl τ)
      rw [h1, h2]
      refine ⟨fun v hv => ⟨1, one_ne_zero, ?_⟩, fun v hv => ⟨w, hw0, ?_⟩⟩
      · simpa using hinc.1 hv
      · exact hinc.2.1 hv
    · intro c hc
      obtain ⟨-, -, h3, h4⟩ := hB τ c hc
      have hinc := ((hD.base c hc).incl τ)
      rw [h3, h4]
      refine ⟨fun v hv => ⟨w, hw0, ?_⟩, fun v hv => ⟨1, one_ne_zero, ?_⟩⟩
      · exact hinc.2.2.2 hv
      · simpa using hinc.2.2.1 hv
  exact GlobalTheory.T.uniformizer_model_perm_module_lattice O Ω K ι x ϖ hϖ d hmod p hp0 φ (VL := fun τ => Fin (r τ) → Ω)
    (VO := fun τ => Fin (s τ) → Ω) Lie W Om OmHT hsame hck lie om hflag

end GlobalTheory.CompanionTheory.Ar.Num.TopRel
