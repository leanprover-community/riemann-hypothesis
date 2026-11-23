module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdeleIsoComponentZeroOfInfinitelyDivisible
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

theorem _root_.GlobalTheory.T.finiteAdele_iso_component_zero_of_infinitely_divisible : ∀ {F E F' E' : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field F'] [NumberField F'] [Field E'] [NumberField E'] [Algebra F' E'] (iE : E' ≃+* E) (iA : AfE F' E' ≃+* AfE F E), (∀ x : E', iA (x ⊗ₜ[F'] 1) = iE x ⊗ₜ[F] 1) → (∀ y, iA y ∈ RInt F E ↔ y ∈ RInt F' E') → ∀ (ι : AfE F' E' ≃+* FiniteAdeleRing (𝓞 E') E'), GlobalTheory.TwU.IsAdIso ι → ∀ (z : AfE F E) (ℓ D : ℕ), 0 < ℓ → 0 < D → (∀ n : ℕ, (((D : E) / (ℓ : E) ^ n) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * z ∈ RInt F E) → ∀ (P : HeightOneSpectrum (𝓞 E')), ((ℓ : ℕ) : 𝓞 E') ∈ P.asIdeal → ι (iA.symm z) P = 0 := by
  first | exact @GlobalTheory.TwV.Xc.adIso_comp_zero_of_div | exact GlobalTheory.TwV.Xc.adIso_comp_zero_of_div | (intros; apply GlobalTheory.TwV.Xc.adIso_comp_zero_of_div <;> assumption)
