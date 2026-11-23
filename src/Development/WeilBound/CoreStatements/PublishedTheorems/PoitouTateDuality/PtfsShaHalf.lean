module

public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDualInjectiveEquivStatement
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
import Mathlib.Tactic.Linter.HaveILetI
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

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

theorem shaHalf_of_perfectPair {n : ℕ} [NeZero n] {X Y : Type} [AddCommGroup X]
    [Module (ZMod n) X] [AddCommGroup Y] [Module (ZMod n) Y] (h : PerfectPair (R := ZMod n) X Y) :
    Finite Y ∧ Finite X ∧ Nonempty (X ≃ₗ[ZMod n] Module.Dual (ZMod n) Y) ∧
      Nat.card Y = Nat.card X := by
  obtain ⟨hX, hY, P, hP, hP'⟩ := h
  have key := GlobalTheory.T.finite_dual_injective_equiv n Y X ⟨P, hP.1⟩ ⟨P.flip, hP'.1⟩
  exact ⟨hY, hX, key.1, key.2⟩

section Published

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
  (Av : S → ValuationSubring Ω)
  (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)

theorem shaDual_of_perfectPair
    (h1 : PerfectPair (R := ZMod (l ^ r)) (Sha2 ρ (locFam S Av) (continuous_locFam S Av))
      (Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)))
    (h2 : PerfectPair (R := ZMod (l ^ r)) (Sha2 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av))
      (Sha1 ρ (locFam S Av) (continuous_locFam S Av))) : ShaDual S Av μ ρ := by
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩
  exact ⟨shaHalf_of_perfectPair h1, shaHalf_of_perfectPair h2⟩

end Published

end PositivityTheory.Lit1.PTN
