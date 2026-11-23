module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSkewA
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddHaarCharSkewHermitianNormScale
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
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj


theorem _root_.GlobalTheory.T.addHaarChar_skewHermitian_normScale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (j : ℕ) [LocallyCompactSpace (GlobalTheory.ResidueEisenstein.ModConj.skewA σ j)] [SecondCountableTopology (GlobalTheory.ResidueEisenstein.ModConj.skewA σ j)] [MeasurableSpace (GlobalTheory.ResidueEisenstein.ModConj.skewA σ j)] [BorelSpace (GlobalTheory.ResidueEisenstein.ModConj.skewA σ j)] (l : (AF F ⊗[F] E)ˣ) (L : GlobalTheory.ResidueEisenstein.ModConj.skewA σ j ≃ₜ+ GlobalTheory.ResidueEisenstein.ModConj.skewA σ j), (∀ s, (L s : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) = ((l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E)) • (s : Matrix (Fin j) (Fin j) (AF F ⊗[F] E))) → addEquivAddHaarChar L = absE F E l ^ (j * j) := by
  first | exact @GlobalTheory.ResidueEisenstein.ModConj.addEquivAddHaarChar_skewA_scale | exact GlobalTheory.ResidueEisenstein.ModConj.addEquivAddHaarChar_skewA_scale | (intros; apply GlobalTheory.ResidueEisenstein.ModConj.addEquivAddHaarChar_skewA_scale <;> assumption)
