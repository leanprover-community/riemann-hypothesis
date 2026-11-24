module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictlyDominantContractsUnipotent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

theorem _root_.GlobalTheory.T.strictly_dominant_contracts_unipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∀ t : Levi k (Bl d), IsStrictlyDominant k N J d hd t → ∀ n ∈ unipRad k (stdBlocks d hd), ∃ r : ℕ, leviEmb k (stdBlocks d hd) t ^ r * n * (leviEmb k (stdBlocks d hd) t ^ r)⁻¹ ∈ KN k N J d hd := by
  first | exact @GlobalTheory.CompanionTheory.ExpandN.exists_pow_conj_mem_KN | exact GlobalTheory.CompanionTheory.ExpandN.exists_pow_conj_mem_KN | (intros; apply GlobalTheory.CompanionTheory.ExpandN.exists_pow_conj_mem_KN <;> assumption)
