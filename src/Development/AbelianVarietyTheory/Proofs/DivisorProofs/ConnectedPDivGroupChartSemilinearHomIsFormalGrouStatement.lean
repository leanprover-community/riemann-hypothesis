module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupChartSemilinearHomIsFormalGrou
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

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.connectedPDivGroupChart_semilinearHom_isFormalGroupHom : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k') (φ : Fin d → MvPowerSeries (Fin e) k'), c.IsLawOf μ → c'.IsLawOf ν → (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → IsHom ν (fun i => MvPowerSeries.map σ (μ i)) φ := by
  first | exact @GlobalTheory.Katz.isHom_map_of_semiHom_ev | exact GlobalTheory.Katz.isHom_map_of_semiHom_ev | (intros; apply GlobalTheory.Katz.isHom_map_of_semiHom_ev <;> assumption)
