module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSqThetaConstantSpanningClassesLeExp
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

theorem _root_.GlobalTheory.T.normSq_thetaConstant_spanning_classes_le_exp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (x : ℝ), GoodEmb c σ → IsUnf U → ∀ R : ℕ, Odd R → 1 < R → ∀ (xs : Fin (Dw.p + Dw.q) → GlobalTheory.EtaForm.LatMod Dw (R ^ 4)) (f : Rul Xo c), Submodule.span (𝓞 E) (Set.range xs) = ⊤ → GlobalTheory.ThetaConst.IsTauRule Xo c R (fun _ : Unit => 1) (fun _ => xs) f → ∀ (DF q m : ℕ) (R0 : ℝ), GlobalTheory.EtaAn.RunOK E r DF q R0 m → (Dw.p ≤ m ∨ Dw.q ≤ m) → ∀ z : Σ k, Frame (U.X k).Ψ r, z.2 ∈ (U.X z.1).dom → homN U x (wtZ 0 (2 * (Dw.p + Dw.q))) (f ^ 2) z ≤ Real.exp ((GlobalTheory.EtaAn.p16 E r q m R 1 - ReciprocityTheory.ChartRestriction.G.I2.phiFD (U.X z.1) (ReciprocityTheory.ChartRestriction.G.I2.th (E := E) q R0) z.2) / (R : ℝ) ^ 4) := by
  first | exact @GlobalTheory.ThetaConst.normSq_thetaConst_le_exp | exact GlobalTheory.ThetaConst.normSq_thetaConst_le_exp | (intros; apply GlobalTheory.ThetaConst.normSq_thetaConst_le_exp <;> assumption)
