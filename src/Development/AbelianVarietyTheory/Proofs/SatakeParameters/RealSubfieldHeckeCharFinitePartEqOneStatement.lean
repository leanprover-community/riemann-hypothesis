module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOneOfMemLev
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealSubfieldHeckeCharFinitePartEqOne
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.HeckeUnrExt
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj)

theorem _root_.GlobalTheory.T.realSubfield_heckeChar_finitePart_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ψ : HChar (maximalRealSubfield E)) (M : ℕ), (∀ a : Ideles (maximalRealSubfield E), a ∈ GlobalTheory.Mem.Chr.unitIdl (maximalRealSubfield E) → (∀ w, (a : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).1 w = 1) → (∀ P : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Valued.v ((a : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 P - 1) ≤ Valued.v ((M : maximalRealSubfield E) : P.adicCompletion (maximalRealSubfield E))) → ψ.1 a = 1) → (∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → ψ.UnrAt (w.under (𝓞 (maximalRealSubfield E)))) → ∀ (w₀ : HeightOneSpectrum (𝓞 E)) (N : ℕ), M ∣ N → ∀ b : Ideles (maximalRealSubfield E), ideleMap (maximalRealSubfield E) E b ∈ levT E {w | GlobalTheory.UnitaryBC.IsSplitAt w ∧ w ≠ w₀} N → ψ.1 (GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b) = 1 := by
  first | exact @GlobalTheory.HeckeFinTriv.finPart_eq_one | exact GlobalTheory.HeckeFinTriv.finPart_eq_one | (intros; apply GlobalTheory.HeckeFinTriv.finPart_eq_one <;> assumption)
