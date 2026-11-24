module

public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
namespace GlobalTheory.Cong.LevelExt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_locU_iff {w : HeightOneSpectrum (𝓞 E)} (x : UA E n) :
    x ∈ locU n w ↔ x ∈ finU (E := E) (n := n) ∧ ∀ u, Apart u w → cLoc u x = 1 := by
  unfold locU Apart
  simp only [Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker]

theorem cLoc_conj_eq_one {w : HeightOneSpectrum (𝓞 E)} (x : UA E n) (h1 : cLoc w x = 1) :
    cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x = 1 := by
  have hw1 : ∀ v, v = w → cLoc v x = 1 := by
    rintro v rfl
    exact h1
  have hce := GlobalTheory.SplitPts.comp_eq x (conjSrc (GlobalTheory.SplitPts.conjE E) w)
  rw [hw1 _ (GlobalTheory.SplitPts.conjSrc_conjSrc_cm w), Units.val_one, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.transpose_one, Matrix.one_mul] at hce
  exact Units.ext hce

theorem one_of_cLoc {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (x : UA E n) (h1 : cLoc w x = 1) :
    ∀ u, ¬ Apart u w → cLoc u x = 1 := by
  intro u hu
  have hu' : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) := by
    by_contra h
    exact hu h
  rcases (GlobalTheory.SplitPts.over_split hw).2.2 u hu' with rfl | rfl
  · exact h1
  · exact cLoc_conj_eq_one x h1

end GlobalTheory.Cong.LevelExt
