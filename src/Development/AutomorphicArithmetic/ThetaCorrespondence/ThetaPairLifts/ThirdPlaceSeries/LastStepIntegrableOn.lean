module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopStepVectorProperty
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainStepVectorsAndAdjointVectorsAreTheta
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EasyInputs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaChainLastStepIntertwinesMatchedHecke
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BaseChain
theorem lastStep_integrableOn_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ j (h : j + 2 * 0 + 2 = D.R.m) v, IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).ΛX ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 (j + 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi D.R.m) ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) v → ∀ (F : CXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) W.P.A3.A.μ0) Q x g, IntegrableOn (fun y => thetaKO (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h) g y (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) v Q) * F.1 x y) ((_root_.GlobalTheory.Fam.pk_z W).fdX W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).νX W.P.A3.A.μ0) := by
  intro D L hT Gi Gl Kc Yd cX ex W hP j h v hv F Q x g
  have hC := hP.bot.hyp.2.2.2.1
  have hω : IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' _ _ (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h) :=
    weil_transport ((_root_.GlobalTheory.Fam.pk_z W).ωX W.P.A3.A.μ0) (hC.chain.ωX W.P.A3.A.μ0) (j + 1) (idx_top h)
  obtain ⟨c1, hc1⟩ := hC.lev.βY (j + 1) (by omega)
  obtain ⟨c2, hc2⟩ := hC.lev.βX
  have hv' : IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' v :=
    (GlobalTheory.VecTheta.vecThetaSD D).1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hc1) (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hc2) hc1.1 hc2.1 hv
  have hf := GlobalTheory.Chain.InnerSteps.theta_pureTensorO hω.std hC.models.inf (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)))
    (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) hv' Q
  have hν := hC.models.νX W.P.A3.A.μ0
  have key := GlobalTheory.Hk3.StepX.integ_X hω hf (F.1 x)
    (multT_apply_continuous _ _ _ _ F.1 F.2 x) (multT_apply_left _ _ _ _ F.1 F.2 x) _ hν.1.1 _ hν.2 g 1
  simpa only [mul_one] using key
end GlobalTheory.BaseChain
end
