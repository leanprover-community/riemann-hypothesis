module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Mathlib.Algebra.Module.Lattice.Full
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameMatrixCloseGivesLatticeCloseIntegral
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

theorem _root_.GlobalTheory.T.frameMatrix_close_gives_lattice_close_integral : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ Λ : G.Lt, Submodule.IsFullLattice E Λ → ∃ d : ∀ p, (A.loc p).Fp, (∀ p, d p ≠ 0) ∧ {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = d p}.Finite ∧ ∀ p (c0 : (A.loc p).Fp) (h : (G.S p).GLV) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) (A.loc p).Ep), c0 ≠ 0 → c0 ∈ 𝒪[(A.loc p).Fp] → h ∈ (G.S p).St → (∀ j, h (A.bc p (G.f j)) = ∑ i, M i j • A.bc p (G.f i)) → (∀ i j, ∃ o ∈ (A.L p).O, (M - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (c0 * d p) * o) → h ∈ (G.S p).K0 ∧ ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, h x - x = algebraMap (A.loc p).Fp (A.loc p).Ep c0 • y := by
  first | exact @GlobalTheory.HL.FrameClose.close_lattice | exact GlobalTheory.HL.FrameClose.close_lattice | (intros; apply GlobalTheory.HL.FrameClose.close_lattice <;> first | assumption | exact (show Submodule.IsFullLattice _ _ from by assumption).toIsLattice)
