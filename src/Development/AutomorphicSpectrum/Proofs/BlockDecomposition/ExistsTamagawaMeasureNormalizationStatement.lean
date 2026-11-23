module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTamagawaMeasureNormalization
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_tamagawa_measure_normalization : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J → ∀ n : ℕ, ∃ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F)) (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v)) (minf : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) σ n → Measure (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E)) (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) σ n → Measure (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf ∧ (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) ∧ IsGramFibFree (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) b laminf n M) (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) σ b laminf n) minf ∧ ∀ v, IsGramFibFree (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) b (lam v) n M) (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) σ b (lam v) n) (m v) := by
  exact @GlobalTheory.CompanionTheory.WeilSiegel.Frame.exists_coord_fibres
