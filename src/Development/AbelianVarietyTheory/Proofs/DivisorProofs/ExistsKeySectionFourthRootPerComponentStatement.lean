module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeySectionFourthRootPerComponent
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

theorem _root_.GlobalTheory.T.exists_keySection_fourthRoot_perComponent : ∀ (κ : GlobalTheory.KeyCl.Rule), GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.FamUnit κ → GlobalTheory.KeyCl.ThetaOne κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (K : (Rul Xo c)ˣ), GoodEmb c σ → IsUnf U → FnAlgClosed (Xo := Xo) (c := c) → 1 ≤ Dw.p + Dw.q → (K : Rul Xo c) ∈ secZ Xo c ((4 : ℤ) • keyEx Dw) → (∀ (F : Type) [Field F] [CharZero F] [Algebra c.F F] (y : FrPt Xo c F) (Φ : FibKey Xo F y.x), Tied e y.s y.u Φ → evR Xo c (K : Rul Xo c) y = (κ F Φ.key : F)) → ∃ ρ : KeySec Xo c, ∀ Z : Comp Xo c, ∃ a : c.F, a ≠ 0 ∧ idem Z * (ρ.ρ : Rul Xo c) ^ 4 = a • (idem Z * (K : Rul Xo c)) := by
  first | exact @GlobalTheory.KeyRoot.exists_keySec_pow_four | exact GlobalTheory.KeyRoot.exists_keySec_pow_four | (intros; apply GlobalTheory.KeyRoot.exists_keySec_pow_four <;> assumption)
