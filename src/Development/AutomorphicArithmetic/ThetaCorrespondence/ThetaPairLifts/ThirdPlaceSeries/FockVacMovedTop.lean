module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesConsecutiveStep
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesTopStep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
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

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.TopMove
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
theorem fock_vac_moved_top_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (g : GA D (Yc D (j + 1))) (gT : GA D D.sp.X'), g ∈ GfC (Yc D (j + 1)) → gT ∈ GfC D.sp.X' → ∀ (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (LT : GlobalTheory.FinPl.Lat D.sp.X'), IsSelfDualC (Yc D (j + 1)) M' → IsSelfDualC D.sp.X' LT → (∀ P, GlobalTheory.FinPl.Moves (Yc D (j + 1)) g ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' P) → (∀ P, GlobalTheory.FinPl.Moves D.sp.X' gT (_root_.GlobalTheory.Fam.pk_z W).ΛX LT P) → (∀ P, GlobalTheory.FinPl.Vac (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' M' LT (fun _ => True) (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (g, gT) (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) P))) ∧ omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (g, gT) (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) 1) ≠ 0 := by
  intro D L hT Gi Gl Kc Yd cX ex W hW j h g gT hg hgT M' LT hM' hLT hm hmT
  have hLev := hW.bot.hyp.2.2.2.1.lev
  have sdY : IsSelfDualC (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY (j + 1) (by omega))
  have sdX : IsSelfDualC D.sp.X' (_root_.GlobalTheory.Fam.pk_z W).ΛX := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hLev.βX
  have key := GlobalTheory.StepMove.gen (θ := (_root_.GlobalTheory.Fam.pk_z W).θ)
    (sS := cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (sT := cart (_root_.GlobalTheory.Fam.pk_z W).MX) (weil_omT (_root_.GlobalTheory.Fam.pk_z W) W.Q.charW.base.chain.ωX W.P.A3.A.μ0 j h) sdY hM' sdX hLT hg hgT (hm _) (hmT _)
    (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (isVacO_vacT (_root_.GlobalTheory.Fam.pk_z W) W.Q.charW.base.chain.vX W.P.A3.A.μ0 j h)
  refine ⟨fun P => ?_, key.2⟩
  have h1 := key.1 P 1 (one_mem _) 1 (one_mem _)
  rwa [one_mul, one_mul] at h1
end GlobalTheory.TopMove
end
end
