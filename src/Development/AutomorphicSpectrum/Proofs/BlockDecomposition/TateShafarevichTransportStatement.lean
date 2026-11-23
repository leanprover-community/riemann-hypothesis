module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NineTermExactIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateShafarevichTransport
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PoitouTateExactSecond

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

theorem _root_.GlobalTheory.T.tate_shafarevich_transport : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R] {Γ Γ' : Type} [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] {I I' : Type} [Fintype I] [Fintype I'] {D : I → Type} {D' : I' → Type} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)] [∀ i, Group (D' i)] [∀ i, TopologicalSpace (D' i)] (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i)) (φ' : ∀ i, D' i →* Γ') (hφ' : ∀ i, Continuous (φ' i)) (χ : Γ →* Rˣ) (χ' : Γ' →* Rˣ) {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M) (ρ' : Representation R Γ' M) (eG : Γ ≃ₜ* Γ') (eI : I ≃ I') (eD : ∀ i, D i ≃ₜ* D' (eI i)), (∀ i d, φ' (eI i) (eD i d) = eG (φ i d)) → (∀ g, χ' (eG g) = χ g) → (∀ g m, ρ' (eG g) m = ρ g m) → ShaG φ' hφ' χ' ρ' → ShaG φ hφ χ ρ := by
  exact @GlobalTheory.CompanionTheory.PTIso.ShaTransfer.shaG_transfer
