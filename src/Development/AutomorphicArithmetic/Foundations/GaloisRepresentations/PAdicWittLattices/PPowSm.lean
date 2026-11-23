module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartBundleQuotientEquivalence
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PowerOfAbelianSchemeProjective
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private lemma smooth_pow_hom {S : Scheme.{0}} (A : Over S) (hA : Smooth A.hom) (k : ℕ) :
    Smooth (GlobalTheory.KS.pow A k).hom := by
  have hiso : ∀ {X Y : Over S} (e : X ≅ Y), Smooth Y.hom → Smooth X.hom := by
    intro X Y e h
    rw [← Over.w e.hom]
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).mapIso e).hom)
    infer_instance
  have hprod : ∀ (Y Z : Over S), Smooth Y.hom → Smooth Z.hom → Smooth (Y ⨯ Z).hom := by
    intro Y Z hY hZ
    rw [← Over.w (prod.snd (X := Y) (Y := Z)), ← Over.prodLeftIsoPullback_hom_snd]
    infer_instance
  induction k with
  | zero =>
    exact hiso (((isLimitEquivIsTerminalOfIsEmpty _ _) (productIsProduct _)).uniqueUpToIso
      Over.mkIdTerminal) (by dsimp; infer_instance)
  | succ k ih =>
    exact hiso ((productIsProduct _).conePointUniqueUpToIso
      (extendFanIsLimit _ (productIsProduct fun _ : Fin k => A) (prodIsProd _ _))) (hprod _ _ hA ih)

theorem UpperTheory.Gal.G3.pPowSm :
    GenSm → PowSm := by
  intro hG p _ D R _ _ gb N X k
  obtain ⟨hs, hsep, -, hproj⟩ := hG p D R gb N X
  haveI := hs
  haveI := hsep
  haveI : Smooth X.univ.A.hom := X.univ.ab.smooth
  haveI : Smooth (GlobalTheory.KS.pow X.univ.A k).hom := smooth_pow_hom _ inferInstance k
  haveI : IsProper (GlobalTheory.KS.pow X.univ.A k).hom :=
    GlobalTheory.KS.Leray.isProper_pow_hom _ X.univ.ab.proper k
  refine ⟨inferInstance, inferInstance, fun hD => ?_⟩
  exact GlobalTheory.KS.isProjOver_pow R X.X X.s (hproj hD) X.univ.A X.univ.ab _
    (LB.isLB_pull X.univ.isLB _) X.univ.ample k
