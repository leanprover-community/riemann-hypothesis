module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsOfVal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoefficientVectorReadingRealRepresentation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchurScalarLemma
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section



section
noncomputable section
namespace GlobalTheory.TopVal.Scalar
section Alg
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms Matrix GlobalTheory.CoefSpace
variable {ι : Type} [Fintype ι] {n : ℕ}
end Alg
section Group
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Forms Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.DefLift GlobalTheory.CoefSpace GlobalTheory.DefiniteMult Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {θ : InfFam D} {c : CoefA V}
  {pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ}
end Group
end GlobalTheory.TopVal.Scalar
end
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem GlobalTheory.TopVal.exists_jVal_smul_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : GlobalTheory.Mem.Col2.TC B X} {l : I.Laws} {Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), Formalism.L2.Forms.gramP (I.rec7 l Z) = 1 → ∀ (u : B.Word) (cv : GlobalTheory.TopVal.Val B →ₛₗ[B.embLL] (_root_.GlobalTheory.Fam.pk_z W).cX.W), _root_.GlobalTheory.TopVal.ValEqvAlt W cv → cv ≠ 0 → ∀ j₀, GlobalTheory.Core.Rk.Top.IsJ u (_root_.GlobalTheory.Fam.pk_z W).MX j₀ → ∃ a : ℂ, a ≠ 0 ∧ _root_.GlobalTheory.TopVal.ValuationCompatible W cv (a • j₀) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u cv hcv h0 j₀ hJ
  have hm := W.Q.charW.base.models
  have hr := hJ.range
  rw [GlobalTheory.Core.Rk.Top.sgT_eq_perIn_sgT I l Z u I.mu0] at hr
  have e : (fun τ => ((GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)).1 τ)⁻¹) = 1 := funext fun τ => inv_one
  obtain ⟨a, ha, h⟩ := GlobalTheory.TopVal.Scalar.exists_scalar (D := I.rec7 l Z) (M := (_root_.GlobalTheory.Fam.pk_z W).MX) (θ := (_root_.GlobalTheory.Fam.pk_z W).θ) (c := (_root_.GlobalTheory.Fam.pk_z W).cX)
    (pr := (_root_.GlobalTheory.Fam.pk_z W).prX) hm.inf (GlobalTheory.DefiniteMult.allPlus_parB _ (Nat.sub_le _ _) _) hm.cX hm.prX
    (Formalism.L2.Forms.rankP (I.rec7 l Z)) B.wts.sgTrue B.embLL B.fields.emb
    (fun τ x => DFunLike.congr_fun (B.fields_embC τ) x) cv hcv h0 _ _ _ e j₀ hJ.inj hr hJ.eqv
  refine ⟨a, ha, fun w v => (h w v).trans ?_⟩
  delta GlobalTheory.TopVal.pairVal
  rw [LinearMap.smul_apply]
  erw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.smul_apply]
  rfl
end
