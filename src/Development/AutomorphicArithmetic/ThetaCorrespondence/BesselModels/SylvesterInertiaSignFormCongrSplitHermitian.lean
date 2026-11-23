module

public import Formalism.FormalDegreeBessel.StatementG
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.TransportIntA
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

@[expose] public section

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.Inertia

theorem card_plus_of_congr_Hpk : ∀ {m r : ℕ} (ε : Fin (2 * r + m + 1) → Bool)
    {Q Qi : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1)
    (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk m r),
    (Finset.univ.filter fun i => ε i = true).card = m + r := by
  intro m r ε Q Qi h1 h2 hg
  have hu : IsUnit Q := ⟨⟨Q, Qi, h1, h2⟩, rfl⟩
  have hc : Formalism.MainNotions.S.IsCayley m r ε Q := ⟨hu, hg⟩
  exact (ReciprocityTheory.ChartRestriction.DS.Lap.TransportIntA.cayley_signature' hc).1

end UpperTheory.Lit.Bur.Inertia

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

theorem _root_.UpperTheory.Lit.Bur.sylvester_inertia_signForm_congr_splitHermitian : ∀ {m r : ℕ} (ε : Fin (2 * r + m + 1) → Bool) {Q Qi : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk m r), (Finset.univ.filter fun i => ε i = true).card = m + r := by
  first | exact @UpperTheory.Lit.Bur.Inertia.card_plus_of_congr_Hpk | exact UpperTheory.Lit.Bur.Inertia.card_plus_of_congr_Hpk | (intros; apply UpperTheory.Lit.Bur.Inertia.card_plus_of_congr_Hpk <;> assumption)
