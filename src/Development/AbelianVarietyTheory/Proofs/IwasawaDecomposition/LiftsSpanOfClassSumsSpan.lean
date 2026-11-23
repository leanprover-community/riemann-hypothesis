module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsSpanOfOnto
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IoOverLeftUnique
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsEmbExt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SecBCAndCuspBC
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneMapOfOfPtIdent
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.LiftSpan

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.OneMapTuples GlobalTheory.OneMapAll GlobalTheory.FieldBC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}
  {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
  {ι : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
  {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}




end GlobalTheory.LiftSpan

namespace GlobalTheory.LiftSpan

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.OneMapTuples GlobalTheory.OneMapAll

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}


section Guard

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}
  {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
  {ι : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
  {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}


set_option maxHeartbeats 1000000 in
theorem lam_geo_mem_span {O : OMDat T.toCore R i Unit fun _ => A.μ0} (hP : O.Pins κ v₀ ι x₀) (hspan : ClassSumsSpan O κ)
    {lam : AutQ (Wc D i) → ℂ} {z : G} {c0 : ℂ} (hid : PtIdent O κ lam z c0) :
    ∀ f ∈ cuspOver O κ, (fun q => lam q * geo O (fun _ => 1) z f q) ∈ Submodule.span ℂ (Set.range (liftQ R i v₀ A.μ0)) := by
  obtain ⟨ζ, -, hζ, h⟩ := hid ()
  intro f hf
  have hf' := hspan hf
  clear hf
  induction hf' using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨hg, x, hx, hgx⟩ := hg
    obtain ⟨y, hy⟩ := lift_of_plc hP hx
    have e : (fun q => lam q * geo O (fun _ => 1) z g q) = (c0 / ζ) • liftQ R i v₀ A.μ0 y := by
      funext q
      rw [Pi.smul_apply, smul_eq_mul, ← hy, div_mul_eq_mul_div, eq_div_iff (ne_zero_of_root hζ),
        h x hx g ((mem_cusp _ _ _ _ _ _).1 hg).1 hgx q]
      show lam q * (1 * rdQ O z g q) * _ = _
      ring
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
  | zero =>
    have e : (fun q => lam q * geo O (fun _ => 1) z 0 q) = 0 := funext fun q => by
      have := geo_smul O (fun _ => 1) z 0 0 q
      rw [zero_smul] at this
      rw [this]
      simp
    rw [e]
    exact Submodule.zero_mem _
  | add f g _ _ hf hg =>
    convert Submodule.add_mem _ hf hg using 1
    funext q
    rw [geo_add, mul_add, Pi.add_apply]
  | smul a f _ hf =>
    convert Submodule.smul_mem _ (a : ℂ) hf using 1
    funext q
    rw [geo_smul, mul_left_comm, Pi.smul_apply, smul_eq_mul]



theorem liftsSpan_of_ptIdent {O : OMDat T.toCore R i Unit fun _ => A.μ0} (hP : O.Pins κ v₀ ι x₀) (hspan : ClassSumsSpan O κ)
    {O' : OMDat T.toCore R i T0 id} (hP' : O'.Pins κ v₀ ι x₀) (hlev : O'.lev = O.lev) (hex : ClsEx O' κ)
    {lam : AutQ (Wc D i) → ℂ} {z : G} {c0 c1 : ℂ} (hc1 : c1 ≠ 0) (hid : PtIdent O κ lam z c0) (hid' : PtIdent O' κ lam z c1) :
    LiftsSpan R i v₀ := by
  intro t y
  have e2 : O'.lev2 = O.lev2 := by funext g; simp only [OMDat.lev2, hlev]
  obtain ⟨x, hx, e⟩ := plc_of_lift hP' t y
  obtain ⟨f, hf, hfx, -⟩ := hex t x hx
  obtain ⟨s, -, -, h⟩ := hid' t
  have hf' := ((mem_cusp _ _ _ _ _ _).1 hf).1
  obtain ⟨m, as, fs, hfs, hBC⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O'.hle).2 _ (T.U ((i : ℕ) + 1)) _ _ f hf
  have hs : ∀ k, fs k ∈ sec _ T.Q.c (wtA κ) (Vc D i).rank := fun k => ((mem_cusp _ _ _ _ _ _).1 (hfs k)).1
  have key : liftQ R i v₀ t y = ∑ k, (s / c1 * (as k : ℂ)) •
      fun q => lam q * geo O (fun _ => 1) z (GlobalTheory.FieldBC.rulBC O.hle (fs k)) q := by
    funext q
    have h1 : c1 * O'.thAd t x q = s * lam q * rdQ O' z f q := h x hx f hf' hfx q
    have h2 : 1 * rdQ O' z f q = _ := geo_of_isBC O' hP'.act.1 (fun _ => 1) z hf' hs hBC q
    rw [phi_eq O' O (fun _ _ => 1), e2, one_mul] at h2
    have h3 : ∀ k, geo O (fun _ => 1) z (GlobalTheory.FieldBC.rulBC O.hle (fs k)) q =
        O.phi (fun _ => 1) (actLev T.Q.c O.lev2 z (fs k)) q.out := fun k => by
      have hs1 : ∀ k', ![fs k] k' ∈ sec _ T.Q.c (wtA κ) (Vc D i).rank := fun k' => by
        rw [Subsingleton.elim k' 0]; exact hs k
      rw [geo_of_isBC O hP.act.1 _ z (GlobalTheory.FieldBCModel.rulBC_mem_sec O.hle (hs k)) hs1
        (GlobalTheory.FieldBCModel.isBC_rulBC O.hle (hs k).1)]
      simp only [Fin.sum_univ_one, Matrix.cons_val_zero, OneMemClass.coe_one, one_mul]
    refine mul_left_cancel₀ hc1 ?_
    rw [show liftQ R i v₀ t y = O'.thAd t x from e.symm, h1, h2]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  rw [key]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (lam_geo_mem_span hP hspan hid _
    (((GlobalTheory.FieldBC.rulBC_cusp _ _ _ _ _ _ _ O.hle _ (T.U ((i : ℕ) + 1)) _ _ _ (hs k)).2).2 (hfs k)))

end Guard


end GlobalTheory.LiftSpan
