module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsHermitianFormDescentCoefficientField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

theorem _root_.GlobalTheory.T.exists_hermitianForm_descent_coefficientField : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) {n : ℕ} (S : GStep E K n) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok) (z : S.Cl → GlobalTheory.Mem.Col2.Fr emb σ n → ℂ), z ∈ S.Fi emb σ lam → ∀ v : S.Cl → Formalism.L2.DIV.VV K lam, (∀ c, z c = evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (v c)) → ∃ y : S.FormsK emb lam h, (∀ c, y.1 c = v c) ∧ S.embF emb σ lam h y = z := by
  first | exact @GlobalTheory.Glob.FormDescent.desc | exact GlobalTheory.Glob.FormDescent.desc | (intros; apply GlobalTheory.Glob.FormDescent.desc <;> assumption)
