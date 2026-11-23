module

public import Formalism.LocalToGlobal.HermitianForms.PrkSmul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDvdOfAdicValuationLtOne
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
open scoped TensorProduct

theorem _root_.GlobalTheory.T.levelPrime_dvd_of_adicValuation_lt_one : ∀ (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (A : Formalism.L2.Forms.AtTTied u) (v : HeightOneSpectrum (𝓞 D.host.F)) (_ : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal)
    (a : v.adicCompletionIntegers D.host.F) (_ : Valued.v (a : v.adicCompletion D.host.F) < 1),
    ∃ b : v.adicCompletionIntegers D.host.F, a = (((D.mem u).A.T : ℕ) : v.adicCompletionIntegers D.host.F) * b := by
  first | exact @GlobalTheory.LevelUnif.dvd_of_val_lt_one | exact GlobalTheory.LevelUnif.dvd_of_val_lt_one | (intros; apply GlobalTheory.LevelUnif.dvd_of_val_lt_one <;> assumption)
