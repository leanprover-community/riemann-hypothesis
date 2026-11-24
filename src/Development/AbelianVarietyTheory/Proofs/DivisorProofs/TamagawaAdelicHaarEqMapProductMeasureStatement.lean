module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPoissonSummationAnyHaar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamagawaAdelicHaarEqMapProductMeasure
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit


theorem _root_.GlobalTheory.T.tamagawa_adelicHaar_eq_map_product_measure : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : ℕ) (e : κ ≃ Fin N) (ν : Measure (AF F)), GlobalTheory.SWQ.IsCov1 ν → ∀ μ : Measure (κ → AF F), IsTamagawa F κ μ → μ = Measure.map (GlobalTheory.PoissonReindex.reidx (F := F) e) (GlobalTheory.SWQ.muV N ν) := by
  first | exact @GlobalTheory.SWLit.tamagawa_eq_map_pi | exact GlobalTheory.SWLit.tamagawa_eq_map_pi | (intros; apply GlobalTheory.SWLit.tamagawa_eq_map_pi <;> assumption)
