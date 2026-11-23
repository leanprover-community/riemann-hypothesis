module

public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagCoefIntegralOfLocalIntegral
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

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain

theorem _root_.GlobalTheory.T.flag_coef_integral_of_local_integral : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : StarRing E] {S : HSpace E} {r : ℕ} (Λ : Submodule (𝓞 E) S.V) (g : ℕ) {T : E} (F : LFlag S r T), IsFixedConv Λ g F → ∀ (j : ℕ) (x : S.V), x ∈ Xflag F j → (∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ)) → ∃ w : Fin r → E, x = ∑ c, w c • F.fl.e c ∧ (∀ c : Fin r, j ≤ c.val → w c = 0) ∧ ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ c, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 E, (s : E) * w c = o := by
  first | exact @GlobalTheory.FlagCoef.coef_integral_of_flag | exact GlobalTheory.FlagCoef.coef_integral_of_flag | (intros; apply GlobalTheory.FlagCoef.coef_integral_of_flag <;> assumption)
