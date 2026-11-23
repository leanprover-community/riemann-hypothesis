module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActWOneApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabiliserSplittingAdelic
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

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage

theorem _root_.GlobalTheory.T.stabiliser_splitting_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∃ (ι : HA (AF F) σ J →* stabilizer₂ (AF F) σ J) (π : stabilizer₂ (AF F) σ J →* HA (AF F) σ J), Continuous ι ∧ Continuous π ∧ (∀ u, π (ι u) = u) ∧ (∀ u ∈ HFinIn (AF F) σ J, ι u ∈ ratP (AF F) σ J) ∧ (∀ p ∈ ratP (AF F) σ J, π p ∈ HFinIn (AF F) σ J) ∧ (∃ K : Set (stabilizer₂ (AF F) σ J), IsCompact K ∧ ∀ m ∈ π.ker, ∃ γ ∈ ratP (AF F) σ J, π γ = 1 ∧ γ * m ∈ K) ∧ (∀ (k : ℕ) (u : HA (AF F) σ J) (a : Fin 1 → Fin k → AF F ⊗[F] E) (Y : Fin k → Fin M → AF F ⊗[F] E), actW (AF F) σ (hypOne J) (ι u : HA (AF F) σ (hypOne J)) (consA a Y) = consA a (actW (AF F) σ J u Y)) ∧ ∀ (k : ℕ) (Y : Fin k → Fin M → E), LinearIndependent E Y → ∃ l : π.ker → Fin 1 → Fin k → AF F ⊗[F] E, Continuous l ∧ (∀ x y, l (x * y) = l x + l y) ∧ Function.Surjective l ∧ (∀ m : π.ker, (m : stabilizer₂ (AF F) σ J) ∈ ratP (AF F) σ J → l m ∈ ratA (F := F) (E := E) k) ∧ ∀ (m : π.ker) (a : Fin 1 → Fin k → AF F ⊗[F] E), actW (AF F) σ (hypOne J) ((m : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)) (consA a (ratTup (AF F) Y)) = consA (a + l m) (ratTup (AF F) Y) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Struct.stab_structure | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Struct.stab_structure | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Struct.stab_structure <;> assumption)
