module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBorelSphericalSameDoubleCosetSumsZonal
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

@[expose] public section

open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling


theorem _root_.GlobalTheory.T.exists_borel_spherical_same_double_coset_sums_zonal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (α : Fin n → ℂˣ), HasSatake π α → ∀ ω : GL (Fin n) k → ℂ, IsZonal π (KO k (Fin n)) ω → ∃ φ : GL (Fin n) k → ℂ, IsBorelSph k (fun i : Fin n => (α i : ℂ) * (((resCard k : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ)) φ ∧ ∀ g, Formalism.UG.hAct (KO k (Fin n)) (Formalism.UG.dosetInd ℂ (KO k (Fin n)) g) ω 1 = Formalism.UG.hAct (KO k (Fin n)) (Formalism.UG.dosetInd ℂ (KO k (Fin n)) g) φ 1 := by
  first | exact @GlobalTheory.ZonalBorel.exists_isBorelSph_hAct_eq | exact GlobalTheory.ZonalBorel.exists_isBorelSph_hAct_eq | (intros; apply GlobalTheory.ZonalBorel.exists_isBorelSph_hAct_eq <;> assumption)
