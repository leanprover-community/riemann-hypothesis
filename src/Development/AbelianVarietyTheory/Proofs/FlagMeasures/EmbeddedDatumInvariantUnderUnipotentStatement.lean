module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AdaptSelf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddedDatumInvariantUnderUnipotent
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.embeddedDatum_invariant_under_unipotent : ∀ (K V W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (H : HermSpace K V) (HW : HermSpace K W) (e : W →ₗ[K] V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F G G' : FlagD H r) (𝔡 : Ideal (𝓞 K)) (N : NF H r) (g : ℕ), IsEmb F HW e → Adapt F G 𝔡 N → (∀ (s : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V), F.InN (s : V →ₗ[K] V) → (∀ a, s (G.e a) - G'.e a ∈ G'.Xa a.val) → datOf F G' e g (s • Λ) = datOf F G e g Λ ∧ lat0 F e (s • Λ) = lat0 F e Λ ∧ latL F G (s • Λ) = latL F G Λ) ∧ ∀ Λ Λ' : Submodule (𝓞 K) V, datOf F G e g Λ = datOf F G e g Λ' → flagPairDefinitePartLattice G F Λ = flagPairDefinitePartLattice G F Λ' ∧ iotaGraph F G Λ (g : 𝓞 K) = iotaGraph F G Λ' (g : 𝓞 K) := by
  first | exact @GlobalTheory.DegAsm.datOf_move | exact GlobalTheory.DegAsm.datOf_move | (intros; apply GlobalTheory.DegAsm.datOf_move <;> assumption)
