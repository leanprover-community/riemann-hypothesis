module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumRealEq
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoInfMulProd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem realEq_of_colOK_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.ColOK → RealEq f.t := by
  intro D L hT Gi Gl Kc Yd cX ex W u _ f hf j hj s s' a ha b hb φ hφ
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  have hL := W.Q.charW.base.lev
  let k : Fin D.R.m := ⟨j, hj⟩
  have hexp : ∀ τ, ∃ e : ℚ, HasInfExp D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu s (j + 1)) τ e ∧
      HasInfExp D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu s' (j + 1)) τ e := by
    intro τ
    obtain ⟨n, hn, ho⟩ := hL.xi_fin s
    obtain ⟨n', hn', ho'⟩ := hL.xi_fin s'
    have h0 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 k)
      (GlobalTheory.Chain.StepVac.hasInfQ_tau ((_root_.GlobalTheory.Fam.pk_z W).C.isMu0 k).inf) τ
    exact ⟨_, GlobalTheory.Chain.StepVac.hasInfExp_mul h0 (GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hL.xi s) hn ho τ),
      GlobalTheory.Chain.StepVac.hasInfExp_mul h0 (GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hL.xi s') hn' ho' τ)⟩
  exact GlobalTheory.RealEqWeil.weilDatum_realEq D _ _ _ _ _ _ _ _ _ (hf.kom s j hj) (hf.kom s' j hj) hexp hexp a ha b hb φ hφ
end GlobalTheory.Fam
end
