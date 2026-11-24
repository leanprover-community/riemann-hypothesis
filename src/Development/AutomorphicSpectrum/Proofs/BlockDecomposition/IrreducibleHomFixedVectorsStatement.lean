module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleHomFixedVectors
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

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

theorem _root_.GlobalTheory.T.irreducible_hom_fixed_vectors : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι] (K : Subgroup (GL ι F)), IsOpen (K : Set (GL ι F)) → IsCompact (K : Set (GL ι F)) → ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL ι F) V) (τ : Representation ℂ (GL ι F) W), GlobalTheory.PRep.IsSmooth π → π.IsIrreducible → GlobalTheory.PRep.IsSmooth τ → τ.IsIrreducible → (∃ v ∈ fixed π K, v ≠ 0) → ∀ T : V →ₗ[ℂ] W, (∀ v ∈ fixed π K, T v ∈ fixed τ K) → (∀ w ∈ fixed τ K, ∃ v ∈ fixed π K, T v = w) → (∀ v ∈ fixed π K, T v = 0 → v = 0) → (∀ e, IsHk K e → ∀ v ∈ fixed π K, T (hk π K e v) = hk τ K e (T v)) → Nonempty (π.Equiv τ) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeInj.hecke_determines | exact GlobalTheory.CompanionTheory.HeckeInj.hecke_determines | (intros; apply GlobalTheory.CompanionTheory.HeckeInj.hecke_determines <;> assumption)
