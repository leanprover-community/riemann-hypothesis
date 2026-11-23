module

public import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ClassicalThetaOfDatumSmulMove
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.classicalThetaOfDatum_smul_move : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ} (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (AA : Submodule (𝓞 E) E) (SS : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (c : ℕ) (p : ℂ) (Ξ : Formalism.L2.Col.HomE E a b → ℂ) (θ : Formalism.L2.Ker.VV ι a b → ℂ), Formalism.L2.Ker.thC emb δ d sc AA SS N N' c (fun x => p * Ξ x) θ = Formalism.L2.Ker.thC emb δ d sc AA SS N N' c Ξ (fun z => p * θ z) := by
  first | exact @GlobalTheory.Corev.ThCLin.thC_smul_move | exact GlobalTheory.Corev.ThCLin.thC_smul_move | (intros; apply GlobalTheory.Corev.ThCLin.thC_smul_move <;> assumption)
