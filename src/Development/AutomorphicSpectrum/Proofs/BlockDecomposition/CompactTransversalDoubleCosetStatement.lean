module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactTransversalDoubleCoset
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
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.compact_transversal_double_coset : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Q P : Subgroup G} {x : G}, LocSec Q P x → IsClosed (P : Set G) → ∀ (B₀ : Set G), IsCompact B₀ → B₀ ∈ 𝓝 (1 : G) → ∀ (D : Set G), IsCompact D → D ⊆ dcos Q P x → ∃ C : Set P, IsCompact C ∧ ∀ g ∈ D, ∃ q ∈ Q, ∃ c ∈ C, g = q * x * c := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.dcos_compact_lift | exact GlobalTheory.CompanionTheory.BZRes.dcos_compact_lift | (intros; apply GlobalTheory.CompanionTheory.BZRes.dcos_compact_lift <;> assumption)
