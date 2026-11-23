module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBoundedOfPhiEquationDisc
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_bounded_of_phi_equation_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ (φ : A →+* A), φ (s X) = s X ^ l → ∀ (Φ : Disc l (s X) bk.ρ₀ →+* Disc l (s X) bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) φ Φ → ∀ (κ : Type) (c : κ → κ → A), (∀ i (n : ℕ), {j | c i j ∉ (bk.J ^ n).map s}.Finite) → ∀ (h : ℕ) (V : κ → Disc l (s X) bk.ρ₀), Filter.Tendsto V Filter.cofinite (nhds 0) → (∀ j, HasSum (fun i => Φ (V i) * toDisc l (s X) bk.ρ₀ (c i j)) (toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * V j)) → ∃ (k : ℕ) (v : κ → A), (∀ j, toDisc l (s X) bk.ρ₀ (v j) = (l : Disc l (s X) bk.ρ₀) ^ k * V j) ∧ ∀ n : ℕ, {j | v j ∉ (bk.J ^ n).map s}.Finite := by
  first | exact @GlobalTheory.BSP.exists_bounded_of_phi_equation | exact GlobalTheory.BSP.exists_bounded_of_phi_equation | (intros; apply GlobalTheory.BSP.exists_bounded_of_phi_equation <;> assumption)
