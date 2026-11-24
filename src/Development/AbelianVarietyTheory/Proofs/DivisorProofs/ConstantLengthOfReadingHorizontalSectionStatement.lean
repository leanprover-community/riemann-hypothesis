module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantLengthOfReadingHorizontalSection
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal

@[expose] public section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.BdryUnit

theorem _root_.GlobalTheory.T.constant_length_of_reading_horizontal_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1) (f : Rul Xo c), (V : Set (Xo.XF c)) = Z → sig ∈ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.sections Y V τ.1 → GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig → GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsHorizontal sig → f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0) → Reads Y V τ sig f → ∀ σ, GoodEmb c σ → ∃ b : ℝ, 0 < b ∧ homN (U σ) x (wtOf Dw (flatWt Dw τ) 0) f '' framesOn (U σ) Z = {b} := by
  first | exact @GlobalTheory.BdryUnit.const_length_of_reads | exact GlobalTheory.BdryUnit.const_length_of_reads | (intros; apply GlobalTheory.BdryUnit.const_length_of_reads <;> assumption)
