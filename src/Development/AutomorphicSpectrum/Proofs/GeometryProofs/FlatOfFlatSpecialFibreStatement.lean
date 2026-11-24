module

public import Mathlib.RingTheory.RingHom.Flat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatOfFlatSpecialFibre
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

open TensorProduct

theorem _root_.GlobalTheory.T.flat_of_flat_special_fibre : ∀ (R P Q : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing P] [CommRing Q] [Algebra R P] [Algebra R Q] [Module.Finite R P] [Module.Finite R Q] [Module.Flat R Q] (φ : P →ₐ[R] Q), (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom.Flat → φ.toRingHom.Flat := by
  first | exact @GlobalTheory.CompanionTheory.FinAlgFlat.ringHom_flat_of_fibre_flat | exact GlobalTheory.CompanionTheory.FinAlgFlat.ringHom_flat_of_fibre_flat | (intros; apply GlobalTheory.CompanionTheory.FinAlgFlat.ringHom_flat_of_fibre_flat <;> assumption)
