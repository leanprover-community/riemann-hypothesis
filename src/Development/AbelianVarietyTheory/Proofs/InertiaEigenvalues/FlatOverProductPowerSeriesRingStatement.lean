module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.RingTheory.Flat.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatOverProductPowerSeriesRing
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.flat_over_product_power_series_ring : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (n : ℕ) [NeZero n] (E : Type) [CommRing E] [Algebra (LetA O n) E] (p : ℕ), IsUnit (algebraMap (LetA O n) E letπ) → IsAdicComplete (Ideal.span {(p : E)}) E → (∀ (x : E) (k : ℕ), ∃ (a : LetA O n) (m : ℕ), x * algebraMap (LetA O n) E (letπ ^ m) - algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k}) → (∀ (a : LetA O n) (k : ℕ), algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k} → ∃ b : LetA O n, a = (p : LetA O n) ^ k * b) → Module.Flat (LetA O n) E := by
  first | exact @GlobalTheory.FlatLocCompl.flat_letA | exact GlobalTheory.FlatLocCompl.flat_letA | (intros; apply GlobalTheory.FlatLocCompl.flat_letA <;> assumption)
