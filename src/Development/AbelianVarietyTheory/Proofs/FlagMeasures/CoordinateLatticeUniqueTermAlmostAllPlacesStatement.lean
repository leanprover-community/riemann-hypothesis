module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordinateLatticeUniqueTermAlmostAllPlaces
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

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.coordinateLattice_unique_term_almost_all_places : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → {p | ¬ ((G.S p).gg = false ∧ (G.S p).Hp = 1 ∧ (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V))) = (G.S p).K0 ∧ ∃ d₀, (G.S p).IsTermW d₀ (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V))) 1 1 ∧ (G.S p).om d₀ (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V))) = 1 ∧ (G.S p).H0 ⊓ MulAction.stabilizer (G.S p).GLV d₀ = (G.S p).complementReferenceCompactSubgroup ∧ (∀ Λ, (G.S p).IsTerm d₀ Λ → ∃ h ∈ (G.S p).St, Λ = h • (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V)))) ∧ (∀ Λ, (G.S p).IsTerm d₀ Λ → (G.S p).Fr d₀ Λ = (G.S p).frameCls (G.S p).f (G.S p).f' → Λ = (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V)))) ∧ ∀ d Λ, (G.S p).IsTerm d Λ → ∃ h ∈ (G.S p).H0, d = h • d₀)}.Finite := by
  first | exact @GlobalTheory.HL.StdPlace.coordinate_lattice_standard | exact GlobalTheory.HL.StdPlace.coordinate_lattice_standard | (intros; apply GlobalTheory.HL.StdPlace.coordinate_lattice_standard <;> assumption)
