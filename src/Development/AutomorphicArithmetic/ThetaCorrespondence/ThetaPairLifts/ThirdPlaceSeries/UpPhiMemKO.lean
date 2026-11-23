module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelSubgroupAtPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeStepValue
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PhiMemKOOfNotTwAtStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PhiMemKOStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
noncomputable section
namespace GlobalTheory.LevProd
theorem up_phi_mem_KO_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ g ∈ _root_.GlobalTheory.LevProd.upperLevelSubgroup a j hj, ∀ i, _root_.GlobalTheory.LevProd.localHomProduct J j hj g i ∈ KO (J.G i).k _ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ g hg i
  unfold _root_.GlobalTheory.LevProd.upperLevelSubgroup at hg
  split_ifs at hg with h
  · obtain ⟨⟨hsup, hgf⟩, hphi⟩ := Subgroup.mem_inf.1 hg |>.imp_left Subgroup.mem_inf.1
    by_cases hv : _root_.GlobalTheory.LevProd.quadraticTwistAtPlace h.choose_spec.choose (J.G i).q.v
    · obtain ⟨i₀, hi₀⟩ := hv
      exact _root_.GlobalTheory.T.true_geometry_lattice_closed_alt W hW u a ha hTr j hj _ _ h.choose_spec.choose_spec.1 t J hJ i₀ i hi₀ g hgf
        ((Subgroup.mem_pi _).1 (Subgroup.mem_comap.1 hphi) i₀ (Set.mem_univ _))
    · have hle : h.choose_spec.choose.A.U j (h.choose_spec.choose.ι j h.choose_spec.choose_spec.2.some) ⊔
          GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.LevProd.quadraticTwistAtPlace h.choose_spec.choose) ≤
          (KO (J.G i).k _).comap ((Pi.evalMonoidHom _ i).comp (_root_.GlobalTheory.LevProd.localHomProduct J j hj)) := by
        refine sup_le (fun x hx => ?_) (fun x hx => ?_)
        · exact _root_.GlobalTheory.T.true_geometry_lattice_final_alt W hW u a ha hTr j hj _ _ h.choose_spec.choose_spec.1 _ t J hJ i hv x hx
        · rw [Subgroup.mem_comap, MonoidHom.comp_apply, Pi.evalMonoidHom_apply]
          change GlobalTheory.LevIdx.locHom (J.G i).q _ _ x ∈ KO (J.G i).k _
          rw [locHom_eq_one_of_grpAt _ _ _ hv hx]
          exact one_mem _
      exact hle hsup
  · rw [Subgroup.mem_bot.1 hg, map_one]
    exact one_mem _
end GlobalTheory.LevProd
end
end
