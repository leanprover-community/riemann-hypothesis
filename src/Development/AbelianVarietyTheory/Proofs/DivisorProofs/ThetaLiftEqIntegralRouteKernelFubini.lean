import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteKernelIntegrableOnUnitaryQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteCombinationMulLiftByDegree
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightOrthogonalSumEmbeddingLeMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunOOfMatchedSquareBigRoute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumAdjointNegSourceKernelsAgree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawOneSourceOrthogonalSumTargets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleExistsSignatureRankSumLt

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.BigRoute

theorem theta_of_matched_big : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {B : Frames G} {ρ : RealMatch W} {t : T} {i j : Fin D.R.m}
    {Θ : TotT G (routeBig t i j)} {Θ' : TotT G (routeSmall t i j)} (_ : IsMatched B t ρ i j Θ Θ')
    {d : PureT G (routeBig t i j)} (_ : d ∈ Θ.support),
    IsThetaFunO W.ψ (G.pS (.chi i (j + 1))) (G.pT (.chi i (j + 1))) d.1.2 ∧
      IsThetaFunO W.ψ (G.pS (.mu t (i + 1) j)) (G.pT (.mu t (i + 1) j)) d.2 := by
  intro D T L sc G W B ρ t i j Θ Θ' hΘ d hd
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, -, ⟨φ₁, φ₂, hloc, -⟩⟩, rfl, -⟩ := hΘ
  obtain ⟨d₀, hd₀, P, rfl⟩ := GlobalTheory.SmallRoute.mem_support_tensT W hd
  obtain ⟨h1, h2⟩ := hloc d₀ hd₀
  have v1 := ρ.vX_is i (j + 1) i.2 j.2
  have v2 := ρ.vT_is t (i + 1) j i.2 j.2
  have t1 := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is h1.2 v1.2.theta
  have t2 := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is h2.2 v2.2.theta
  exact ⟨GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t1 _,
    GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t2 _⟩

theorem continuous_kerBig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (_ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    Continuous (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
      kerBig W Θ p.1 g₁ p.2) := by
  intro D T L sc G W B ρ t i j Θ Θ' hΘ g₁
  have hc := W.om_is (.chi (i : ℕ) (j + 1)) ⟨i.2, j.2⟩
  have hm := W.om_is (.mu t ((i : ℕ) + 1) j) ⟨i.2, j.2⟩
  have hK : ∀ d ∈ Θ.support, Continuous (fun q : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
      W.kerA (.right i (j + 1)) d.1.2 q.1 q.2 * W.kerA (.down t (i + 1) j) d.2 q.2 g₁) := by
    intro d hd
    obtain ⟨h1, h2⟩ := theta_of_matched_big hΘ hd
    refine Continuous.mul ?_ ?_
    · show Continuous fun q : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
        thetaKO (W.om (.chi (i : ℕ) (j + 1))) (negGA _ q.2) q.1 d.1.2
      exact (hc.om_cont _ h1 0).comp (((continuous_negGA _).comp continuous_snd).prodMk continuous_fst)
    · show Continuous fun q : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
        thetaKO (W.om (.mu t ((i : ℕ) + 1) j)) g₁ q.2 d.2
      exact (hm.om_cont _ h2 0).comp (continuous_const.prodMk continuous_snd)
  unfold kerBig
  simp only [Finsupp.sum]
  exact continuous_finset_sum _ fun d hd => continuous_const.mul (hK d hd)

theorem aestronglyMeasurable_kerBig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    AEStronglyMeasurable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) => kerBig W Θ p.1 g₁ p.2)
      (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1))))) := by
  intro D T L sc G μ₀ hL W B ρ t i j M hM Θ Θ' hΘ g₁
  exact (continuous_kerBig W B ρ t i j Θ Θ' hΘ g₁).aestronglyMeasurable

end GlobalTheory.BigRoute
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aestronglyMeasurable_kernel_route_big_vertex : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    AEStronglyMeasurable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) => kerBig W Θ p.1 g₁ p.2)
      (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1))))) := by
  atlas_forward_decl GlobalTheory.BigRoute.aestronglyMeasurable_kerBig
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.BigRouteInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem theta_first_of_matched {W : G.Weil} {B : Frames G} {ρ : RealMatch W} {t : T} {i j : Fin D.R.m}
    {Θ : TotT G (routeBig t i j)} {Θ' : TotT G (routeSmall t i j)} (hΘ : IsMatched B t ρ i j Θ Θ')
    {d : PureT G (routeBig t i j)} (hd : d ∈ Θ.support) :
    IsThetaFunO W.ψ (G.pS (.chi (i : ℕ) ((j : ℕ) + 1))) (G.pT (.chi (i : ℕ) ((j : ℕ) + 1))) d.1.2 := by
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, -, ⟨φ₁, φ₂, hloc, -⟩⟩, rfl, -⟩ := hΘ
  obtain ⟨d₀, hd₀, P, rfl⟩ := GlobalTheory.SmallRoute.mem_support_tensT W hd
  obtain ⟨h1, -⟩ := hloc d₀ hd₀
  have v1 := ρ.vX_is i (j + 1) i.2 j.2
  have t1 := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is h1.2 v1.2.theta
  exact GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t1 _

theorem kerBig_rat_mul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∀ γ ∈ GQ (G.V (.grid i (j + 1))), ∀ g : GA D (G.V (.grid i (j + 1))), kerBig W Θ (γ * g) g₁ = kerBig W Θ g g₁ := by
  intro D T L sc G μ₀ hL W B ρ t i j Θ Θ' hΘ g₁ γ hγ g
  have hc := W.om_is (.chi (i : ℕ) ((j : ℕ) + 1)) ⟨i.2, j.2⟩
  funext u
  unfold kerBig
  refine Finsupp.sum_congr fun d hd => ?_
  have h1 := theta_first_of_matched hΘ hd
  congr 2
  show thetaKO (W.om (.chi (i : ℕ) ((j : ℕ) + 1))) (negGA _ u) (γ * g) d.1.2 =
    thetaKO (W.om (.chi (i : ℕ) ((j : ℕ) + 1))) (negGA _ u) g d.1.2
  unfold thetaKO
  have e : ((negGA _ u, γ * g) : GA D (G.pS (.chi (i : ℕ) ((j : ℕ) + 1))) × GA D (G.pT (.chi (i : ℕ) ((j : ℕ) + 1)))) =
      (1, γ) * (negGA _ u, g) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hc.om_aut 1 (one_mem _) γ hγ _ (hc.om_pres _ _ h1)

end GlobalTheory.BigRouteInv
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_route_big_vertex_rational_left_invariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∀ γ ∈ GQ (G.V (.grid i (j + 1))), ∀ g : GA D (G.V (.grid i (j + 1))), kerBig W Θ (γ * g) g₁ = kerBig W Θ g g₁ := by
  atlas_forward_decl GlobalTheory.BigRouteInv.kerBig_rat_mul
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.RouteSeesaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaFunO_of_matchedSquare_bigRoute : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)), IsMatched B t ρ i j Θ Θ' →
    ∀ d ∈ Θ.support, IsThetaFunO W.ψ (G.pS (.chi i (j + 1))) (G.pT (.chi i (j + 1))) d.1.2 ∧
      IsThetaFunO W.ψ (G.pS (.mu t (i + 1) j)) (G.pT (.mu t (i + 1) j)) d.2 := by
  first | exact @GlobalTheory.RouteSeesaw.isThetaFunO_of_isMatched | exact GlobalTheory.RouteSeesaw.isThetaFunO_of_isMatched | (intros; apply GlobalTheory.RouteSeesaw.isThetaFunO_of_isMatched <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.RouteSeesaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatum_adjoint_negSource_kernels_agree : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S B : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (ω₂ : GA D B × GA D S →* Module.End ℂ (WO B S → ℂ)), IsWeilDatumO ψ B S χS χT ω₂ →
    ∃ (ω : GA D (negSp S) × GA D B →* Module.End ℂ (WO (negSp S) B → ℂ)) (χ χ' : (AE D)ˣ →* Circle),
      IsWeilDatumO ψ (negSp S) B χ χ' ω ∧ ∀ f : WO B S → ℂ, IsThetaFunO ψ B S f →
        IsThetaFunO ψ (negSp S) B (fun y => f (adjM S B y)) ∧
        ∀ g₁ u, thetaKO ω (negGA S u) g₁ (fun y => f (adjM S B y)) = thetaKO ω₂ g₁ u f := by
  first | exact @GlobalTheory.AdjSwap.weil_adjoint_negSource | exact GlobalTheory.AdjSwap.weil_adjoint_negSource | (intros; apply GlobalTheory.AdjSwap.weil_adjoint_negSource <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.RouteSeesaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_oneSource_orthogonalSumTargets : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B : HSp D) (χ₁ χ₁' χ₂ χ₂' : (AE D)ˣ →* Circle)
    (ω₁ : GA D S × GA D A →* Module.End ℂ (WO S A → ℂ)) (ω₂ : GA D S × GA D B →* Module.End ℂ (WO S B → ℂ)),
    IsWeilDatumO ψ S A χ₁ χ₁' ω₁ → IsWeilDatumO ψ S B χ₂ χ₂' ω₂ →
    ∃ (ω : GA D S × GA D (GlobalTheory.Doubling.hsum A B) →* Module.End ℂ (WO S (GlobalTheory.Doubling.hsum A B) → ℂ))
      (χ χ' : (AE D)ˣ →* Circle) (c : GA D S → GA D A → GA D B → ℂ),
      IsWeilDatumO ψ S (GlobalTheory.Doubling.hsum A B) χ χ' ω ∧ (∀ u g g₁, ‖c u g g₁‖ = 1) ∧
      ∀ φ φ', IsThetaFunO ψ S A φ → IsThetaFunO ψ S B φ' → IsThetaFunO ψ S (GlobalTheory.Doubling.hsum A B) (box2 φ φ') ∧
        ∀ u g g₁, thetaKO ω u (GlobalTheory.SquareComm.blk A B (g, g₁)) (box2 φ φ') =
          c u g g₁ * (thetaKO ω₁ u g φ * thetaKO ω₂ u g₁ φ') := by
  first | exact @GlobalTheory.SeesawSumTarget.seesaw_sum | exact GlobalTheory.SeesawSumTarget.seesaw_sum | (intros; apply GlobalTheory.SeesawSumTarget.seesaw_sum <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.BigRouteIdent

open GlobalTheory.RouteSeesaw

theorem kerBig_norm_le_thetaKO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∃ (ε : Bool) (ω : GlobalTheory.Grid.WRep (G.V (.grid (i + 1) (j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))))
      (χ χ' : (AE D)ˣ →* Circle) (Φ : WO (G.V (.grid (i + 1) (j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) → ℂ) (C₀ : ℝ),
      GlobalTheory.Grid.IsWeil W.ψ ε _ _ χ χ' ω ∧ IsThetaFunO W.ψ (GlobalTheory.Grid.sgn ε (G.V (.grid (i + 1) (j + 1)))) _ Φ ∧
      ∀ g u, ‖kerBig W Θ g g₁ u‖ ≤ C₀ * ‖thetaKO ω u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) Φ‖ := by
  intro D T L sc G μ₀ hL W B ρ t i j hT M hM Θ Θ' hΘ g₁
  have hd := GlobalTheory.T.isThetaFunO_of_matchedSquare_bigRoute hL W B ρ t i j Θ Θ' hΘ
  have h1 := W.om_is (.chi i (j + 1)) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)
  have h2 := W.om_is (.mu t (i + 1) j) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)
  obtain ⟨ω₂, χa, χb, hω₂, hadj⟩ := GlobalTheory.T.weilDatum_adjoint_negSource_kernels_agree W.ψ W.ψ_std _ _ _ _ _ h2
  obtain ⟨ω', χ, χ', c, hω', hc, hbox⟩ := GlobalTheory.T.seesaw_oneSource_orthogonalSumTargets W.ψ W.ψ_std _ _ _ _ _ _ _ _ ω₂ h1 hω₂
  let S := G.V (.grid (↑i + 1) (↑j + 1))
  let A := G.V (.grid (↑i) (↑j + 1))
  let Bs := G.V (.grid (↑i + 1) ↑j)
  let Φ : WO (negSp S) (GlobalTheory.Doubling.hsum A Bs) → ℂ :=
    Θ.sum fun d a => a • box2 (S := negSp S) (A := A) (B := Bs) d.1.2 (fun y => d.2 (adjM S Bs y))
  have hth : ∀ d ∈ Θ.support, IsThetaFunO W.ψ (negSp S) (GlobalTheory.Doubling.hsum A Bs)
      (box2 (S := negSp S) (A := A) (B := Bs) d.1.2 (fun y => d.2 (adjM S Bs y))) := fun d hdm =>
    (hbox _ _ (hd d hdm).1 ((hadj _ (hd d hdm).2).1)).1
  have e : ∀ u g, ∀ d ∈ Θ.support, thetaKO ω' (negGA S u) (GlobalTheory.SquareComm.blk A Bs (g, g₁))
      (box2 (S := negSp S) (A := A) (B := Bs) d.1.2 (fun y => d.2 (adjM S Bs y))) =
      c (negGA S u) g g₁ * (W.kerA (.right i (j + 1)) d.1.2 g u * W.kerA (.down t (i + 1) j) d.2 u g₁) := fun u g d hdm => by
    rw [(hbox _ _ (hd d hdm).1 ((hadj _ (hd d hdm).2).1)).2, (hadj _ (hd d hdm).2).2]
    rfl
  refine ⟨true, ω'.comp ((negGA S).toMonoidHom.prodMap (MonoidHom.id _)), χ, χ', Φ, 1, hω', ?_, ?_⟩
  · let U : Submodule ℂ (WO (negSp S) (GlobalTheory.Doubling.hsum A Bs) → ℂ) :=
      { carrier := {g | IsThetaFunO W.ψ (negSp S) (GlobalTheory.Doubling.hsum A Bs) g}
        add_mem' := fun ha hb => GlobalTheory.OrientedHeis.theta_add ha hb
        zero_mem' := GlobalTheory.OrientedHeis.theta_zero
        smul_mem' := fun c _ hg => GlobalTheory.OrientedHeis.theta_smul c hg }
    show Φ ∈ U
    exact U.sum_mem fun d hdm => U.smul_mem _ (hth d hdm)
  · intro g u
    have key : ω' (negGA S u, GlobalTheory.SquareComm.blk A Bs (g, g₁)) Φ 0 = c (negGA S u) g g₁ * kerBig W Θ g g₁ u := by
      simp only [Φ, kerBig, Finsupp.sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hdm => ?_
      have := e u g d hdm
      simp only [thetaKO] at this
      rw [this]; ring
    refine le_of_eq ?_
    show ‖kerBig W Θ g g₁ u‖ = 1 * ‖ω' (negGA S u, GlobalTheory.SquareComm.blk A Bs (g, g₁)) Φ 0‖
    rw [key, norm_mul, hc, one_mul, one_mul]

end GlobalTheory.BigRouteIdent

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigRoute_kernel_norm_le_const_mul_thetaKernel : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∃ (ε : Bool) (ω : GlobalTheory.Grid.WRep (G.V (.grid (i + 1) (j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))))
      (χ χ' : (AE D)ˣ →* Circle) (Φ : WO (G.V (.grid (i + 1) (j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) → ℂ) (C₀ : ℝ),
      GlobalTheory.Grid.IsWeil W.ψ ε _ _ χ χ' ω ∧ IsThetaFunO W.ψ (GlobalTheory.Grid.sgn ε (G.V (.grid (i + 1) (j + 1)))) _ Φ ∧
      ∀ g u, ‖kerBig W Θ g g₁ u‖ ≤ C₀ * ‖thetaKO ω u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) Φ‖ := by
  atlas_forward_decl GlobalTheory.BigRouteIdent.kerBig_norm_le_thetaKO
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareThetaTriple_exists_signature_rank_sum_lt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T) (i j : Fin D.R.m)
    (hT : SquareTriple W t i j) (M : Vol G) (hM : M.Is t),
    ∃ p : ℕ, (∃ τ, Formalism.UG.HasSignature (gramAt D (G.V (.grid (i + 1) (j + 1))) τ) ((G.V (.grid (i + 1) (j + 1))).rank - p) p) ∧
      (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank < 2 * ((G.V (.grid (i + 1) (j + 1))).rank - p) := by
  first | exact @GlobalTheory.FunObj.squareTriple_sig_rank | exact GlobalTheory.FunObj.squareTriple_sig_rank | (intros; apply GlobalTheory.FunObj.squareTriple_sig_rank <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.BigRoute

theorem modGrowth_integral_norm_kerBig {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hWC : GlobalTheory.SquareSt.WeilConvergence) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))) :
    GlobalTheory.Grow.ModGrowth (G.V (.grid i (j + 1))) (fun g => ∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1))) := by
  obtain ⟨ε, ω, χ, χ', Φ, C₀, hω, hΦ, hb⟩ := GlobalTheory.T.bigRoute_kernel_norm_le_const_mul_thetaKernel hL W B ρ t i j hT M hM Θ Θ' hΘ g₁
  obtain ⟨p, hsig, hrk⟩ := GlobalTheory.T.squareThetaTriple_exists_signature_rank_sum_lt W t i j hT M hM
  have hHF : GlobalTheory.SquareComm.IsHaarFD _ (M.ν (.grid (i + 1) (j + 1))) (M.fd (.grid (i + 1) (j + 1))) :=
    (hM.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).haar_fund
  obtain ⟨N, Cw, hMI⟩ := hWC D W.ψ W.θ W.θ_is ε _ _ χ χ' ω hω p hsig hrk _ _ hHF Φ hΦ
  obtain ⟨Cc, hCc, hcmp⟩ := GlobalTheory.Grow.height_comparison (G.V (.grid i (j + 1))) W.θ_is
  set h₁ : ℝ := (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ g₁ : ℝ)
  refine ⟨max C₀ 0 * (max Cw 0 * (Cc * h₁) ^ N), N, fun g => ?_⟩
  have hI := (hMI (GlobalTheory.SquareComm.blk _ _ (g, g₁))).1
  have hle := (hMI (GlobalTheory.SquareComm.blk _ _ (g, g₁))).2
  have hpos : 0 ≤ ∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1)) :=
    integral_nonneg fun _ => norm_nonneg _
  rw [Real.norm_of_nonneg hpos]
  have h1 : ∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1)) ≤
      ∫ u in M.fd (.grid (i + 1) (j + 1)), max C₀ 0 * ‖thetaKO ω u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) Φ‖ ∂M.ν (.grid (i + 1) (j + 1)) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) (hI.norm.const_mul _)
      (Filter.Eventually.of_forall fun u => (hb g u).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
  rw [integral_const_mul] at h1
  have hX := GlobalTheory.T.unitaryAdelicHeight_orthogonalSum_embedding_le_mul D W.θ _ _ g g₁
  have hXg : ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ (GlobalTheory.SquareComm.blk _ _ (g, g₁)) : NNReal) : ℝ) ≤
      Cc * GlobalTheory.Grow.height _ g * h₁ := by
    have := (hcmp g).1
    calc _ ≤ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ g : ℝ) * h₁ := by exact_mod_cast hX
      _ ≤ _ := mul_le_mul_of_nonneg_right this (NNReal.coe_nonneg _)
  have h0 : (0 : ℝ) ≤ ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ (GlobalTheory.SquareComm.blk _ _ (g, g₁)) : NNReal) : ℝ) := NNReal.coe_nonneg _
  have h2 : ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ (GlobalTheory.SquareComm.blk _ _ (g, g₁)) : NNReal) : ℝ) ^ N ≤
      (Cc * h₁) ^ N * GlobalTheory.Grow.height _ g ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ h0 (hXg.trans_eq (by ring)) N
  have h3 : Cw * ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ (GlobalTheory.SquareComm.blk _ _ (g, g₁)) : NNReal) : ℝ) ^ N ≤
      max Cw 0 * ((Cc * h₁) ^ N * GlobalTheory.Grow.height _ g ^ N) :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg h0 _)).trans
      (mul_le_mul_of_nonneg_left h2 (le_max_right _ _))
  calc _ ≤ _ := h1
    _ ≤ max C₀ 0 * (max Cw 0 * ((Cc * h₁) ^ N * GlobalTheory.Grow.height _ g ^ N)) :=
      mul_le_mul_of_nonneg_left (hle.trans h3) (le_max_right _ _)
    _ = _ := by ring

end GlobalTheory.BigRoute
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moderateGrowth_integral_norm_kernel_bigVertexRoute : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hWC : GlobalTheory.SquareSt.WeilConvergence) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    GlobalTheory.Grow.ModGrowth (G.V (.grid i (j + 1))) (fun g => ∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1))) := by
  atlas_forward_decl GlobalTheory.BigRoute.modGrowth_integral_norm_kerBig
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.BigRoute

theorem lift_eq_integral_kerBig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hWC : GlobalTheory.SquareSt.WeilConvergence) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hP : GlobalTheory.Published.CuspDecayBound) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (F : Fn G (.grid i (j + 1))) (hF : IsAutFunSm W.θ _ F) (hFc : IsCuspFun _ F) (hFl : G.IsListed W.θ _ F) (hA : TotConv W M _ Θ F) (g₁ : GA D (G.V (.grid (i + 1) j))),
    (∀ᵐ g ∂(M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1))),
      IntegrableOn (kerBig W Θ g g₁) (M.fd (.grid (i + 1) (j + 1))) (M.ν (.grid (i + 1) (j + 1)))) ∧
    liftT W M (routeBig t i j) Θ F g₁ = ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid (i + 1) (j + 1)),
      kerBig W Θ g g₁ u ∂M.ν (.grid (i + 1) (j + 1)) ∂M.ν (.grid i (j + 1)) := by
  intro D T L sc G hWC hK hP μ₀ hL W B ρ t i j hT M hM Θ Θ' hΘ F hF hFc hFl hA g₁
  classical
  have hσ : ∀ X : Node, X.InRange D.R.m → SigmaFinite (M.ν X) := fun X hX => by
    obtain ⟨h1, h2, -⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D (G.V X)
    haveI := (hM.vtx X hX).haar_fund.1
    infer_instance
  haveI := hσ (.grid i (j + 1)) ⟨i.2.le, j.2⟩
  haveI := hσ (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩
  have hK1 : ∀ g, IntegrableOn (kerBig W Θ g g₁) (M.fd (.grid (i + 1) (j + 1))) (M.ν (.grid (i + 1) (j + 1))) := GlobalTheory.T.bigRoute_kernel_integrableOn_unitary_quotient hWC hL W B ρ t i j hT M hM Θ Θ' hΘ g₁
  have hmeas : AEStronglyMeasurable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
      kerBig W Θ p.1 g₁ p.2) (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod
        ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1))))) := GlobalTheory.T.aestronglyMeasurable_kernel_route_big_vertex hL W B ρ t i j M hM Θ Θ' hΘ g₁
  have hinv : ∀ γ ∈ GQ (G.V (.grid i (j + 1))), ∀ g, kerBig W Θ (γ * g) g₁ = kerBig W Θ g g₁ := GlobalTheory.T.kernel_route_big_vertex_rational_left_invariant hL W B ρ t i j Θ Θ' hΘ g₁
  have hgrow : GlobalTheory.Grow.ModGrowth (G.V (.grid i (j + 1))) (fun g => ∫ u in M.fd (.grid (i + 1) (j + 1)),
      ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1))) := GlobalTheory.T.moderateGrowth_integral_norm_kernel_bigVertexRoute hWC hL W B ρ t i j hT M hM Θ Θ' hΘ g₁
  have hRD : GlobalTheory.Grow.RapidDec _ F := GlobalTheory.Grow.rapidDec_of_cuspForm (GlobalTheory.Grow.cuspRapidDecay_of_bound hP) W.θ_is hF hFc
  obtain ⟨hH, hfd⟩ := (hM.vtx (.grid i (j + 1)) ⟨i.2.le, j.2⟩).haar_fund
  have hkm : AEStronglyMeasurable (fun g => ((∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖
      ∂M.ν (.grid (i + 1) (j + 1)) : ℝ) : ℂ)) ((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hmeas.norm.integral_prod_right'
  obtain ⟨C, A, hCA⟩ := hgrow
  have hkb : ∀ g, ‖((∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1)) : ℝ) : ℂ)‖ ≤
      C * 2 ^ A * GlobalTheory.Grow.quotHeight _ g ^ A := fun g => by
    rw [Complex.norm_real]
    exact GlobalTheory.Grow.norm_le_quotHeight_pow (fun γ hγ g => by simp only [hinv γ hγ g]) hCA g
  have hkF := hRD.integrableOn_mul_of_le hH hfd hkm hkb
  have hJ : Integrable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) => F p.1 * kerBig W Θ p.1 g₁ p.2)
      (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod
        ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1))))) := by
    have hFm : AEStronglyMeasurable F ((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))) :=
      hRD.continuous.aestronglyMeasurable
    have hm2 : AEStronglyMeasurable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
        F p.1 * kerBig W Θ p.1 g₁ p.2) (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod
          ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1))))) :=
      hFm.comp_fst.mul hmeas
    refine (integrable_prod_iff hm2).2
      ⟨.of_forall fun g => (hK1 g).const_mul (F g), ?_⟩
    refine hkF.norm.congr (.of_forall fun g => ?_)
    simp only [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, integral_const_mul]
    rw [abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), mul_comm]
  refine ⟨Filter.Eventually.of_forall hK1, ?_⟩
  have hpt : ∀ u, ∫ g in M.fd (.grid i (j + 1)), F g * kerBig W Θ g g₁ u ∂M.ν (.grid i (j + 1)) =
      Θ.sum fun d c => c * (W.kerA (.down t (i + 1) j) d.2 u g₁ *
        ∫ g in M.fd (.grid i (j + 1)), W.kerA (.right i (j + 1)) d.1.2 g u * F g ∂M.ν (.grid i (j + 1))) := by
    intro u
    have hint : ∀ d ∈ Θ.support, IntegrableOn (fun g => W.kerA (.right i (j + 1)) d.1.2 g u * F g)
        (M.fd (.grid i (j + 1))) (M.ν (.grid i (j + 1))) := fun d hd => (hA d hd).1.2 u
    have e : ∀ g, F g * kerBig W Θ g g₁ u = ∑ d ∈ Θ.support,
        Θ d * (W.kerA (.down t (i + 1) j) d.2 u g₁ * (W.kerA (.right i (j + 1)) d.1.2 g u * F g)) := by
      intro g
      simp only [kerBig, Finsupp.sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun d _ => by ring
    simp_rw [e]
    rw [integral_finset_sum _ fun d hd => ((hint d hd).const_mul _).const_mul _]
    simp only [integral_const_mul, Finsupp.sum]
  have hint2 : ∀ d ∈ Θ.support, Integrable (fun u => W.kerA (.down t (i + 1) j) d.2 u g₁ *
        ∫ g in M.fd (.grid i (j + 1)), W.kerA (.right i (j + 1)) d.1.2 g u * F g ∂M.ν (.grid i (j + 1)))
      ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1)))) := fun d hd => (hA d hd).2 g₁
  symm
  calc ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid (i + 1) (j + 1)), kerBig W Θ g g₁ u ∂M.ν (.grid (i + 1) (j + 1))
        ∂M.ν (.grid i (j + 1))
      = ∫ g in M.fd (.grid i (j + 1)), ∫ u in M.fd (.grid (i + 1) (j + 1)), F g * kerBig W Θ g g₁ u ∂M.ν (.grid (i + 1) (j + 1))
        ∂M.ν (.grid i (j + 1)) := by simp_rw [integral_const_mul]
    _ = ∫ u in M.fd (.grid (i + 1) (j + 1)), ∫ g in M.fd (.grid i (j + 1)), F g * kerBig W Θ g g₁ u
        ∂M.ν (.grid i (j + 1)) ∂M.ν (.grid (i + 1) (j + 1)) := integral_integral_swap hJ
    _ = ∫ u in M.fd (.grid (i + 1) (j + 1)), (Θ.sum fun d c => c * (W.kerA (.down t (i + 1) j) d.2 u g₁ *
        ∫ g in M.fd (.grid i (j + 1)), W.kerA (.right i (j + 1)) d.1.2 g u * F g ∂M.ν (.grid i (j + 1))))
        ∂M.ν (.grid (i + 1) (j + 1)) := by
        simp_rw [hpt]
    _ = _ := by
        simp only [Finsupp.sum]
        rw [integral_finset_sum _ fun d hd => (hint2 d hd).const_mul _]
        simp_rw [integral_const_mul]
        simp only [liftT, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rfl

end GlobalTheory.BigRoute

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_eq_integral_routeKernel_fubini : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hWC : GlobalTheory.SquareSt.WeilConvergence) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hP : GlobalTheory.Published.CuspDecayBound) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (F : Fn G (.grid i (j + 1))) (hF : IsAutFunSm W.θ _ F) (hFc : IsCuspFun _ F) (hFl : G.IsListed W.θ _ F) (hA : TotConv W M _ Θ F) (g₁ : GA D (G.V (.grid (i + 1) j))),
    (∀ᵐ g ∂(M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1))),
      IntegrableOn (kerBig W Θ g g₁) (M.fd (.grid (i + 1) (j + 1))) (M.ν (.grid (i + 1) (j + 1)))) ∧
    liftT W M (routeBig t i j) Θ F g₁ = ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid (i + 1) (j + 1)),
      kerBig W Θ g g₁ u ∂M.ν (.grid (i + 1) (j + 1)) ∂M.ν (.grid i (j + 1)) := by
  atlas_forward_decl GlobalTheory.BigRoute.lift_eq_integral_kerBig
end
