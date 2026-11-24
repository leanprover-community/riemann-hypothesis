module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugationDerivCutoffPolynomialMemUnitarySpan
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

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

theorem _root_.GlobalTheory.T.conjugationDerivCutoffPolynomial_mem_unitarySpan : ∀ {n : ℕ} (ε : Fin n → Bool) (Z : GlobalTheory.PsCo.Pc1.Mat n) (H : ℝ → ℝ) (P : GlobalTheory.PsCo.Pc1.Poly n), GlobalTheory.PsCo.Pc1.IsCutFn H → GlobalTheory.PsCo.Pc1.adBas ε Z H P ∈ GlobalTheory.PsCo.Pc1.AdSpanM ε := by
  first | exact @GlobalTheory.PsCo.Pc1.adBas_mem_adSpanM | exact GlobalTheory.PsCo.Pc1.adBas_mem_adSpanM | (intros; apply GlobalTheory.PsCo.Pc1.adBas_mem_adSpanM <;> assumption)
