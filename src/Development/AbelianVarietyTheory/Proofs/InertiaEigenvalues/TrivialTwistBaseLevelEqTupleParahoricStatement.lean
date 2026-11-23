module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivialTwistBaseLevelEqTupleParahoric
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.trivialTwist_baseLevel_eq_tuple_parahoric : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q →
    ∀ x : GL (Fin (Vc D j).rank) (Lev.EAf D),
      (x ∈ lev D.sp.cm (Vc D j).gram (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) ↔
        x ∈ parLev D.sp.cm (Vc D j).gram (X.R.βV j) (X.R.datVt j t) ∧
          X.cG (rTup (X.R.βV j) (X.R.datVt j t) x) ∈ D.nexp.U) ∧
      ∀ (hx : x ∈ parLev D.sp.cm (Vc D j).gram (X.R.βV j) (X.R.datVt j t))
        (hu : X.cG (rTup (X.R.βV j) (X.R.datVt j t) x) ∈ D.nexp.U),
        ((levFn (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) x : ℂˣ) : ℂ) =
          ((levFn (X.R.βV j) (Lev.flagL (X.R.datVt j t)) x : ℂˣ) : ℂ) *
            Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨_, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) := by
  first | exact @GlobalTheory.TrivTwistLevel.levS_triv_iff_and_levFn | exact GlobalTheory.TrivTwistLevel.levS_triv_iff_and_levFn | (intros; apply GlobalTheory.TrivTwistLevel.levS_triv_iff_and_levFn <;> assumption)
