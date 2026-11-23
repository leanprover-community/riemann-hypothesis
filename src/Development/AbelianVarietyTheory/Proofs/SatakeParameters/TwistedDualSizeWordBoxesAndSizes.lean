module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxSizeAtNonThickPlaceLeParametersWindowEndsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RoundedSizeBoundWindow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordNonThickSizeBoundsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordMiAddHiLeTwoHeightStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordLetterEqPageWordStatement
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

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem recWord_wordBox : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ}
    (g : ZMod n → D.R.GG) (ψ : D.R.GG), Roomy L C → IsOrbit g ψ → WordBox L (recWord L j ε g) := by
  intro D L C j ε n g ψ hR hO
  obtain ⟨hn, hg⟩ := hO
  subst hn
  have hgl : g = letter (g 0) ψ := funext fun a => hg a
  rw [hgl]
  have hb := GlobalTheory.HTW.bHat_window L C hR
  refine ⟨?_, ?_, hb.1, hb.2⟩
  · intro a
    obtain ⟨-, hM, hh, -⟩ := GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord L C j ε (g 0) ψ hR a
    rw [hM, hh]
    exact GlobalTheory.T.twistedDualPageWord_Mi_add_hi_le_two_height L C j ε (g 0) ψ hR a
  · intro a hnt
    obtain ⟨hsz, -, -, hth⟩ := GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord L C j ε (g 0) ψ hR a
    obtain ⟨s, hs1, hs2, -, hs3⟩ := GlobalTheory.T.twistedDualOrbitPageWord_nonThick_size_bounds L C j ε (g 0) ψ hR a (fun h => hnt (hth.2 h))
    refine ⟨s, hs1, le_trans hs2 (GlobalTheory.T.maxSizeAtNonThickPlace_le_windowEnds L).1, ?_⟩
    have hc : (((recWord L j ε (letter (g 0) ψ)).sz a : ℕ) : ℝ) = (((pageWord L j ε (g 0) ψ).sz a : ℤ) : ℝ) := by
      rw [← hsz]; push_cast; rfl
    rw [hc]; exact hs3

end GlobalTheory.HTW.Rec
