module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTripleAtOfConj
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntSubMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLamTie0OfIsLamTie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumThEmptyNeZero
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisHypothesesOfIsTriple
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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



section
noncomputable section
namespace GlobalTheory.SettingHypotheses
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen
variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
theorem setHyp_of_isTriple_of_nonzeroIndexPlace (hC : GlobalTheory.Published.ChebotarevDegreeOne) (D : D7)
    (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (C₀ : Formalism.L2.Host.CharFrame D) (S : GlobalTheory.HeightCounting.CharSide D C₀)
    (hG : _root_.UpperTheory.GalS.GalHodgeN D T) (h2 : Formalism.MainNotions.BlochKatoReduction.adm2 D) (h : _root_.GlobalTheory.Triple.IsGaloisTriple D)
    (Z : GlobalTheory.LamTie.LamDat D) (hZ : Z.Ok) (hL : GlobalTheory.LamTie.IsLamTie D.ntw Z)
    (hr : 100 ≤ D.R.r) (hg : ∀ k, 2 * D.R.r ≤ D.host.g k) :
    ∀ i, D.ntw.NonzeroIndexPlace i → SetHyp (bk0 D) i := fun i hi =>
  have hA := (_root_.GlobalTheory.TripleLocal.adm1_adm8_selfDual_noJump_of_isTriple S
    (GlobalTheory.SplitFrobDense.frobDense D (GlobalTheory.Published.chebotarevDegreeOne_iff_cheb.1 hC)) hG h2 h).2.2 i hi
  have hT := GlobalTheory.LamTie.sum_th_empty_ne_zero D D.nd D.ntw Z hZ
    (GlobalTheory.LamTieWeak.isLamTie0_of_isLamTie D D.nd D.ntw Z hL) i hi
  ⟨hA.1, fun s _ => (hA.2 s).1, fun s _ => (hA.2 s).2, fun lam => (hT lam).1, fun lam => (hT lam).2, hr, hg⟩
end GlobalTheory.SettingHypotheses
end
end
