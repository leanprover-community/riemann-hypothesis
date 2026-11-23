module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientOfFullRepresentation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClsEqHomModInertia
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumpsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentOfIndepMod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient

@[expose] public section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.TopSteps

theorem admissibleUntwistedCharUnramified_of_residueRealisation {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (hT : Nonempty (LocTied l P AI)) (hR : ∀ S : TopSit P, S.Real) :
    GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.AdmChiOneUnramified P := by
  intro K LL n r emb D Γ hst hgal h1 h2 h3 X _ _ _
  let S : TopSit P :=
    { K := K, LL := LL, n := n, r := r, nz := ⟨GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.letters_ne_zero hst⟩, emb := emb, D := D, Γ := Γ,
      hyp := ⟨hst, hgal, h1, h2, h3⟩ }
  have hcrys : S.CrysCalc := GlobalTheory.T.crystalline_sums_twists_characters_expected_jumps AI hT S
  have hcl : S.Closed := GlobalTheory.AdmClosure.admissible_closed S
  have hstd : S.StdAdm := StdAdm.stdAdm S hcrys hcl
  have hL : S.Lem0 (S.Γ.Wchi 1) := (GlobalTheory.AdmClasses.admissibleLocalSituation_admissible_classes S hcl hstd).2 1 le_rfl S.D.one_le_letterBlockLength
  have hb : S.ResBound (S.Γ.Wchi 1) 1 := (CharBound.resBound_chars S (hR S)).2 hL
  have hu : S.UnrAdm := GlobalTheory.UnramAdm.unramified_admissible S hcrys hcl hstd hL
  exact ChiOne.cls_eq_homModInertia S hL hb hu X

end GlobalTheory.TopSteps
