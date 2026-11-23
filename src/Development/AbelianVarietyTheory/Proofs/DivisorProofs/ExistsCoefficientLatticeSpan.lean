module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResidueCharIsOfFinOrder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaKernelFiniteAdelicLawsStatement
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.ToricLatticeDenominators
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily

@[expose] public section

open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigOn.Exp


open GlobalTheory.TraceIncl in
theorem clSum_equiv_of_lift {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m} {t : T0}
    (hS : HidaSetting R i t) (hl : (∀ g0 : G0 R.Pg D.R.r, ∃ κ', Formalism.IndefR.Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ')) (g : G) (f : (A.MtCSD i t).Forms) :
    clSum (presV R i t) (kern R i t) (A.leftGroupActionLift i t g f) = actS R i g (clSum (presV R i t) (kern R i t) f) := by
  refine clSum_act (presV R i t) (kernelLaws hS.models hS.thP hS.typ) (R.B.L i t).act_tie (envV R i t).J_le (actS R i)
    (fun q y w => funext fun v => ?_) g f
  exact (GlobalTheory.T.thetaKernelFiniteAdelic_laws R i t hS.models.inf hS.models.cV hS.thP.ωP hS.thP.pt_theta hS.thP.ioP hS.typ).2.2.2 _ q (hS.red i t q)
    (hl _) y w v


open GlobalTheory.TraceIncl in
theorem clSum_trU_of_lift {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m} {t : T0}
    (hS : HidaSetting R i t) (hl : (∀ g0 : G0 R.Pg D.R.r, ∃ κ', Formalism.IndefR.Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ')) (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (f : (A.MtCSD i t).Forms)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    clSum (presV R i t) (kern R i t) (trU (A.leftGroupActionLift i t) U ψ f) v =
      levelTrace R i U ψ (clSum (presV R i t) (kern R i t) f v) := by
  unfold levelTrace gaL

  rw [trU_apply, map_sum, Finset.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smulₛₗ, clSum_equiv_of_lift hS hl, LinearMap.smul_apply, invChar, apply_dite D.what₂.embLL, map_zero]
  rfl


open GlobalTheory.TraceIncl in

theorem exists_adForm_levelTrace {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m} {t : T0}
    (hS : HidaSetting R i t) (hl : ∀ g0 : G0 R.Pg D.R.r, ∃ κ', Formalism.IndefR.Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ')
    (hχ : ∀ k, ∃ a : D.what₂.LL, D.what₂.embLL a = (((envV R i t).χ k : ℂˣ) : ℂ))
    {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {θ : (Fin (srcDim A i t U ψ) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)}
    (hθ : IsClassSum R i t U ψ 1 θ) {h : GA D (Vc D i)} (hh : h ∈ GfC (Vc D i)) {w : (R.cV i).W} (hw : InCoefLat R i h w) :
    ∃ y ∈ LinearMap.range θ, ∀ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ,
      adForm R i y (fun ρ => v ρ) = levelTrace R i U ψ (singleSeries R i (R.ωP i t) (R.vP i t) h w v) := by
  obtain ⟨gramR, c0R, c0L, hT, P, hP, rfl⟩ := hw
  obtain ⟨e, r, h1, hL⟩ := exists_latSys (i := i) (t := t) hS.lev hT
  obtain ⟨f, hf, j, hj⟩ := hL.exists_trace (GlobalTheory.LevelCharOrder.levEnv_chi_isOfFinOrder _ _ _)
    (kernelLaws hS.models hS.thP hS.typ) (h := fin _ h) (x := e.symm P)
    (Submodule.mem_comap.2 ((e.apply_symm_apply P).symm ▸ hP : e (e.symm P) ∈ nabAtr (labLL D) (lamV D i) _))
  obtain ⟨y, -, ey⟩ := exists_src_trU i t U ψ hS.act hf
  have hcw : (presV R i t).coef (e.symm P) = c0L i P := (h1 _).trans (congrArg (c0L i) (e.apply_symm_apply P))
  obtain ⟨a, ha⟩ := hχ j
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact (Units.ne_zero _) ha.symm
  refine ⟨θ (a⁻¹ • y), LinearMap.mem_range_self _ _, fun v => ?_⟩
  have e1 : singleSeries R i (R.ωP i t) (R.vP i t) h (c0L i P) v =
      ((((envV R i t).χ j)⁻¹ : ℂˣ) : ℂ) • clSum (presV R i t) (kern R i t) f v :=
    (hS.kern_fin hh _ v).symm.trans ((congrArg (fun w' => kern R i t (fin _ h) w' v) hcw.symm).trans (congrFun hj v))
  have e2 : adForm R i (θ y) (fun ρ => v ρ) = (1 : ℂ) • levelTrace R i U ψ (clSum (presV R i t) (kern R i t) f v) := by
    rw [hS.adForm_theta hθ y v, ey, clSum_trU_of_lift hS hl]
  have e3 : adForm R i (θ (a⁻¹ • y)) (fun ρ => v ρ) = D.what₂.embLL a⁻¹ • adForm R i (θ y) (fun ρ => v ρ) := by
    rw [map_smul, adForm_smul]
    rfl
  rw [e3, e2, one_smul, e1, (levelTrace R i U ψ).map_smul, map_inv₀, ha, Units.val_inv_eq_inv_val]

end GlobalTheory.BigOn.Exp
