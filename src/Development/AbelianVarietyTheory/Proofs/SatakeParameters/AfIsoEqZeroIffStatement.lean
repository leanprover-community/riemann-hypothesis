module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AfIsoEqZeroIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct

theorem _root_.GlobalTheory.T.afIso_ringEquiv_eq_zero_iff : ∀ (F E F' E' : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field F'] [NumberField F'] [Field E'] [NumberField E'] [Algebra F' E'] (s : E ≃+* E') (φ : AfE F E ≃+* AfE F' E'), (∀ x : E, φ (x ⊗ₜ[F] 1) = s x ⊗ₜ[F'] 1) → (∀ y, φ y ∈ RInt F' E' ↔ y ∈ RInt F E) → ∀ y ∈ RInt F E, ∀ P : HeightOneSpectrum (𝓞 E), (GlobalTheory.Mem.Col2.afIso F' E' (φ y) (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s) P) = 0 ↔ GlobalTheory.Mem.Col2.afIso F E y P = 0) := by
  first | exact @GlobalTheory.AfeLocTr.afIso_eq_zero_iff | exact GlobalTheory.AfeLocTr.afIso_eq_zero_iff | (intros; apply GlobalTheory.AfeLocTr.afIso_eq_zero_iff <;> assumption)
