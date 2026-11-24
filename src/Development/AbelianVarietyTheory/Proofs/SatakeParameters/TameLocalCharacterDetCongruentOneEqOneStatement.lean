module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameLocalCharacterDetCongruentOneEqOne
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsRowFrame
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Formalism.LocalToGlobal.KernelLattices.TopLawQ
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG


theorem _root_.GlobalTheory.T.tameLocalCharacter_det_congruent_one_eq_one : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)), cst.Ok → ∀ (i n : ℕ) (P : rowSG Pr sel mu) (k : GLint X.E n P.1),
    (∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : X.E) ^ (cst.D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp X.E n) l))) →
    rhoS Ch sel mu i P ((LinearEquiv.det k.1 : X.Eˣ) : X.E) = 1 := by
  first | exact @GlobalTheory.TwV.AwayCpl.RhoOne.rhoS_det_one | exact GlobalTheory.TwV.AwayCpl.RhoOne.rhoS_det_one | (intros; apply GlobalTheory.TwV.AwayCpl.RhoOne.rhoS_det_one <;> assumption)
