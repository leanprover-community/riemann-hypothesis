module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIdemOfAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicUnitarySupportedAtFinitePlaceEqLocalUnitar
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

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.adelicUnitary_supportedAtFinitePlace_eq_localUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (e : AF F ⊗[F] E), IsIdemOf E v e → (∀ g, Supp hc V e g ↔ IsFin hc V g ∧ ∀ w, w ≠ v → locMat hc V w g = 1) ∧ (∀ g g', Supp hc V e g → Supp hc V e g' → locMat hc V v g = locMat hc V v g' → g = g') ∧ ∀ u ∈ HR (Fv F v) hc.sig V.gram, ∃ g, Supp hc V e g ∧ locMat hc V v g = u := by
  first | exact @GlobalTheory.SuppLocal.supp_local | exact GlobalTheory.SuppLocal.supp_local | (intros; apply GlobalTheory.SuppLocal.supp_local <;> assumption)
