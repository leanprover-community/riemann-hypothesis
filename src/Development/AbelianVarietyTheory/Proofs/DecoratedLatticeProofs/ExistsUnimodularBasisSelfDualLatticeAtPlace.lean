module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralBasisOfLatticeAtPlaceStableStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatMulSelfDualLatticeAtPlaceIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeAtPlaceBasisGramIntegralInvertiblStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeAtPlaceSmulIntegralMemStatement
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

namespace GlobalTheory.IwaPlace.SDBasis

theorem exists_basis_unimodular : ∀ (D : D7) (S : HSp D) (v : Pl D) (ε : AE D) (Λ : AddSubgroup (Fin S.rank → AE D)), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → IsSDAt S v Λ → ∃ β β' : Matrix (Fin S.rank) (Fin S.rank) (AE D), (∀ i j, β i j ∈ idAt D (· = v)) ∧ (∀ i j, β' i j ∈ idAt D (· = v)) ∧ β * β' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ∧ β' * β = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ∧ (∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ ∀ i, (β' *ᵥ y) i ∈ intAt D (· = v))) ∧ (∀ i j, (adj β * (gA S * β)) i j ∈ intAt D (· = v)) ∧ (∀ i j, cA D ((adj β * (gA S * β)) i j) = (adj β * (gA S * β)) j i) ∧ ∃ H' : Matrix (Fin S.rank) (Fin S.rank) (AE D), (∀ i j, H' i j ∈ intAt D (· = v)) ∧ adj β * (gA S * β) * H' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
  intro D S v ε Λ hT hεε hcε hεO hε hΛ
  obtain ⟨β, β', hβ, hβ', h1, h2, h3⟩ :=
    GlobalTheory.T.exists_integralBasis_of_latticeAtPlace_stable D S.rank v ε Λ hT hεε hcε hεO hε hΛ.1 (GlobalTheory.T.selfDualLatticeAtPlace_smul_integral_mem D S v Λ hΛ) hΛ.2.1 (GlobalTheory.T.exists_nat_mul_selfDualLatticeAtPlace_integral D S v Λ hΛ)
  exact ⟨β, β', hβ, hβ', h1, h2, h3, GlobalTheory.T.selfDualLatticeAtPlace_basis_gram_integral_invertible D S v ε Λ β β' hεε hcε hεO hε hΛ hβ hβ' h1 h2 h3⟩

end GlobalTheory.IwaPlace.SDBasis
