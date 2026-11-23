module

public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetCCompSubst
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

theorem _root_.GlobalTheory.T.jetC_constr_aeval_monomial : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (cD : ι → ℂ) (G : VCx ι a b → ℂ) (g : ι → Matrix (Fin a) (Fin a) ℂ) (h : ι → Matrix (Fin b) (Fin b) ℂ), (∀ k : ℕ, ContDiff ℂ k G) → ∀ m : DVar ι a b →₀ ℕ, jetC cD (fun z : VCx ι a b => G (fun τ i j => ∑ k : Fin b, ∑ l : Fin a, h τ i k * z τ k l * g τ l j)) m = (MvPolynomial.basisMonomials (DVar ι a b) ℂ).constr ℂ (jetC cD G) (MvPolynomial.aeval (fun k : DVar ι a b => ∑ i : Fin b, ∑ j : Fin a, (MvPolynomial.C (h k.1 i k.2.1 * g k.1 k.2.2 j) * MvPolynomial.X (k.1, i, j) : MvPolynomial (DVar ι a b) ℂ)) (MvPolynomial.monomial m (1 : ℂ))) := by
  first | exact @GlobalTheory.Glob.JetChainLin.jetC_comp_subst | exact GlobalTheory.Glob.JetChainLin.jetC_comp_subst | (intros; apply GlobalTheory.Glob.JetChainLin.jetC_comp_subst <;> assumption)
