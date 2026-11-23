module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingBijectiveLocalizedModuleMapOfRank
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section


theorem _root_.GlobalTheory.T.exists_localizedModule_map_bijective_of_rankAtStalk_eq : ∀ (R Q : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Module.Flat R Q] (N r : ℕ) (b : Fin N → Q), Submodule.span R (Set.range b) = ⊤ → (∀ P : PrimeSpectrum R, Module.rankAtStalk Q P = r) → ∀ P₀ : PrimeSpectrum R, ∃ (σ : Fin r ↪ Fin N) (f : R), f ∉ P₀.asIdeal ∧ Function.Bijective (LocalizedModule.map (Submonoid.powers f) (Fintype.linearCombination R (b ∘ σ))) := by
  first | (exact @GlobalTheory.exists_embedding_bijective_localizedModule_map_of_rankAtStalk) | (exact GlobalTheory.exists_embedding_bijective_localizedModule_map_of_rankAtStalk) | (intros; apply GlobalTheory.exists_embedding_bijective_localizedModule_map_of_rankAtStalk  <;> assumption)
