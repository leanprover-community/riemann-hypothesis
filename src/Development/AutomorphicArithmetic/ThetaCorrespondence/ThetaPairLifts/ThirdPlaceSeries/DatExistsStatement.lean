import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowPairRelationAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DatExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowPairRelationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowPairRelation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.XiLevEqConstMulLocFacStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryChainDescentStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMore
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypePrimesDisjointStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypePrimesDisjoint
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistReductionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistReduction
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IdemEqAddTwistStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatDatumAddTwistPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistQuadraticValueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistQuadraticValue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PkPlaces

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_chain_descent_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j, j + 1 ≤ B.R.m → IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.g.vac j) ∧ IsLatVac (heisO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _) (stdHom _ _) (a.g.vac j) ∧ IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dT j) (a.g.vac j)) := by
  first | exact @_root_.GlobalTheory.Fam.VacTheta.main_alt_alt | exact _root_.GlobalTheory.Fam.VacTheta.main_alt_alt | (intros; apply _root_.GlobalTheory.Fam.VacTheta.main_alt_alt <;> assumption)
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Col2.DisjProof
theorem vT_disjoint_vGs_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ u : B.Word, Disjoint ((B.primes X).vT u) (B.primes X).vGs := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  have hT0 : (B.primes X).piT u ≠ 0 := fun h => by
    have := hPr.piT_norm u
    rw [h, zero_mul] at this
    exact (hPr.T_prime u).ne_zero (Nat.cast_eq_zero.1 this.symm)
  exact Finset.disjoint_left.2 fun P h1 h2 =>
    Formalism.L2.Col.piT_notMem_vGs hPr u ⟨P, h2⟩ ((Formalism.L2.Col.mem_divs hT0 P).1 h1)
end GlobalTheory.Mem.Col2.DisjProof
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_primes_disjoint' : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ u : B.Word, Disjoint ((B.primes X).vT u) (B.primes X).vGs := by
  atlas_forward_decl _root_.GlobalTheory.Mem.Col2.DisjProof.vT_disjoint_vGs_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem ratDatum_dT_levelPrime_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ eT, IsIdemSum eT ((B.primes X).vT u) → ∀ j (hj : j + 1 ≤ B.R.m) (α : J.Ch₀ j) (γ : J.Ch₀ (j + 1)), IsRatDatum (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ eT (fun z => B.embLL (Formalism.L2.Col.phiT B.fields.K (J.A.p0 j α).1.1.deco.1 (J.A.p0 (j + 1) γ).1.1.deco.1 (GlobalTheory.QTw.homOf I l Z j hj z))) (a.g.vac j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dT j) (a.g.vac j)) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hAll u a ha hTr t J hJ eT heT j hj α γ
  letI : Field a.k := a.fld
  letI : ValuativeRel a.k := a.val
  letI : TopologicalSpace a.k := a.top
  letI : IsNonarchimedeanLocalField a.k := a.loc
  have hS := ha.shape
  have hP : (fun v => v ∈ a.v.tP) = (fun v => ∃ i, v = (a.o.p i).v) := funext fun x => propext (hS.pre.tP x)
  have hPl : GlobalTheory.FinPl.Places a.o.p a.o.I (fun v => ∃ i, v = (a.o.p i).v) :=
    ⟨hS.pre.nodup, hS.pre.all, hS.pre.inj, fun _ => Iff.rfl, fun i => (hS.pre.char i).2⟩
  have hR : GlobalTheory.FinPl.Reps (_root_.GlobalTheory.Fam.pk_z W).ψ (a.o.β j) (a.o.β (j + 1)) (a.g.x j).L (a.g.x (j + 1)).L
      (fun i => GlobalTheory.LatPair.phiOne (a.o.Q j i) (a.o.Q (j + 1) i)) a.o.I (fun v => ∃ i, v = (a.o.p i).v) (a.v.dT j) := by
    rw [← hP]; exact ⟨(ha.vis.atT j).1, hS.rep j hj⟩
  exact GlobalTheory.T.twistFiniteDatum_theta_at_levelPrime I hAll.tr.ok hAll.tr.pins.some l Z u (W.P.I.tup t) J.Ch₀ J.A hJ.is _ _ _ _ _ hTr.pinX a.k a.ι a.o.p a.o.β a.o.Q
    hTr.std a.o.I hPl j hj α γ (a.v.dT j) hR eT heT
end GlobalTheory.Fam
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_twist_reduction_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ eT, IsIdemSum eT ((B.primes X).vT u) → ∀ j (hj : j + 1 ≤ B.R.m) (α : J.Ch₀ j) (γ : J.Ch₀ (j + 1)), IsRatDatum (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ eT (fun z => B.embLL (Formalism.L2.Col.phiT B.fields.K (J.A.p0 j α).1.1.deco.1 (J.A.p0 (j + 1) γ).1.1.deco.1 (GlobalTheory.QTw.homOf I l Z j hj z))) (a.g.vac j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dT j) (a.g.vac j)) := by
  atlas_forward_decl _root_.GlobalTheory.Fam.ratDatum_dT_levelPrime_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam
theorem ratDatum_xiOff_common_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∃ C : ℕ → ℂ, (∀ j, j < B.R.m → C j ≠ 0) ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ e, IsIdemSum e ((B.primes X).vT u ∪ (B.primes X).vGs) → ∀ j (hj : j + 1 ≤ B.R.m) α γ, IsRatDatum (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ e (fun z => C j * xiOff J.A j hj (J.ι j α) (J.ι (j + 1) γ) z) (a.g.vac j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dG j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dT j) (a.g.vac j))) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hAll u a ha haT hiA
  obtain ⟨C, hC, hloc⟩ := _root_.GlobalTheory.T.true_geometry_row_pair_symmetry_alt W hAll u a ha haT hiA
  refine ⟨fun j => (C j)⁻¹, fun j hj => inv_ne_zero (hC j hj), ?_⟩
  intro t J hJ e he j hj α γ
  obtain ⟨Ξl, hΞl, hfac⟩ := hloc t J hJ j hj α γ
  obtain ⟨hv0, hvl, hvT⟩ := _root_.GlobalTheory.T.true_geometry_chain_descent_alt W hAll u a ha haT j hj
  have hinj : Function.Injective fun n : Fin a.n => ((a.pl n : (_root_.GlobalTheory.Fam.pk_z W).Pg) : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) :=
    fun n n' h => a.pl.injective (Subtype.ext h)
  have hmem : ∀ PP, PP ∈ (B.primes X).vGs ↔ ∃ n : Fin a.n, ((a.pl n : (_root_.GlobalTheory.Fam.pk_z W).Pg) : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) = PP := by
    intro PP
    refine Iff.trans (hAll.lev.2.1 PP).symm ⟨fun h => ⟨a.pl.symm ⟨PP, h⟩, by rw [Equiv.apply_symm_apply]⟩, ?_⟩
    rintro ⟨n, rfl⟩
    exact (a.pl n).2
  have hL : ∀ i, i ≤ B.R.m → IsSelfDualC _ (a.g.x i).L ∧
      ((a.g.x i).L : Set (Fin ((I.rec7 l Z).sp.X i).rank → (I.rec7 l Z).host.E)) = intVec _ _ :=
    fun i hi => ⟨(ha.x i hi).sd, Set.ext (haT.pinX.xs i hi).2.2⟩
  have key := GlobalTheory.T.rationalDatum_foldr_local_combinations (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ haT.pinX.std _ _ ((B.primes X).vT u) (B.primes X).vGs a.n _ hinj hmem
    (_root_.GlobalTheory.T.type_primes_disjoint' W hAll u) (fun n => (a.G n).cg j) Ξl hΞl (a.g.x j).L (a.g.x (j + 1)).L
    (hL j (by omega)).1 (hL (j + 1) hj).1 (hL j (by omega)).2 (hL (j + 1) hj).2 _ (a.g.vac j) _ hv0 hvl
    (fun e₀ he₀ => _root_.GlobalTheory.T.true_geometry_twist_reduction_alt W hAll u a ha haT t J hJ e₀ he₀ j hj (J.ι j α) (J.ι (j + 1) γ)) e he
  rw [← ha.gpin.dG j (by exact hj) _ hvT] at key
  have hCj : C j ≠ 0 := hC j (by omega)
  convert key using 2 with z
  simp only [xiOff, map_mul, hfac z]
  field_simp
end GlobalTheory.Fam
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_row_pair_relation_alt_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∃ C : ℕ → ℂ, (∀ j, j < B.R.m → C j ≠ 0) ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ e, IsIdemSum e ((B.primes X).vT u ∪ (B.primes X).vGs) → ∀ j (hj : j + 1 ≤ B.R.m) α γ, IsRatDatum (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ e (fun z => C j * xiOff J.A j hj (J.ι j α) (J.ι (j + 1) γ) z) (a.g.vac j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dG j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dT j) (a.g.vac j))) := by
  atlas_forward_decl _root_.GlobalTheory.Fam.ratDatum_xiOff_common_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem xi_eq_xiOff_mul_join_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ j (hj : j + 1 ≤ B.R.m) α γ z, J.A.xi j hj (J.ι j α) (J.ι (j + 1) γ) z = xiOff J.A j hj (J.ι j α) (J.ι (j + 1) γ) z * ∏ i, B.embLL (locXi J.A j (J.ι j α) (J.ι (j + 1) γ) (J.P i) (homOf I l Z j hj z)) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ _ t J hJ j hj α γ z
  rw [(GlobalTheory.T.finiteDatum_factors_over_twistPrimes_local I hW.tr.ok hW.tr.tw l Z u (W.P.I.tup t) J.Ch₀ J.A hJ.is).1 j hj (J.ι j α) (J.ι (j + 1) γ) z]
  congr 1
  symm
  refine Finset.prod_bij (fun i _ => J.P i) ?_ ?_ ?_ ?_
  · intro i _
    rw [Finset.mem_filter, hJ.eq i]
    refine ⟨Finset.mem_univ _, fun h => ?_⟩
    exact Finset.disjoint_left.1 ((_root_.GlobalTheory.PkPlaces.pk_places_alt W hW.pk).2 t).1 ((hW.lev.2.1 _).2 h) (J.mem i)
  · intro i₁ _ i₂ _ h
    exact hJ.inj (((hJ.eq i₁).symm.trans (congrArg Subtype.val h)).trans (hJ.eq i₂))
  · intro P hP
    have hv : P.1 ∉ (B.primes X).vGs := (Finset.mem_filter.1 hP).2
    have hq : P.1 ∈ Formalism.L2.Col.QE I.sel (I.tup (W.P.I.tup t) : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K) := by
      rcases Finset.mem_union.1 P.2 with h | h
      · exact absurd h hv
      · exact h
    obtain ⟨i, hi⟩ := hJ.surj _ ((hW.tq.Q t P.1).2 hq)
    exact ⟨i, Finset.mem_univ _, Subtype.ext ((hJ.eq i).trans hi)⟩
  · intro i _
    rfl
end GlobalTheory.Fam
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_twist_quadratic_value_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ j (hj : j + 1 ≤ B.R.m) α γ z, J.A.xi j hj (J.ι j α) (J.ι (j + 1) γ) z = xiOff J.A j hj (J.ι j α) (J.ι (j + 1) γ) z * ∏ i, B.embLL (locXi J.A j (J.ι j α) (J.ι (j + 1) γ) (J.P i) (homOf I l Z j hj z)) := by
  atlas_forward_decl _root_.GlobalTheory.Fam.xi_eq_xiOff_mul_join_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam
theorem QuadraticExtensionData.dat_exists : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∃ C : ℕ → ℂ, (∀ j, j < B.R.m → C j ≠ 0) ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∃ s ζ ρ, J.Dat C s ζ ρ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr hoT
  obtain ⟨C, hC0, hC⟩ := _root_.GlobalTheory.T.true_geometry_row_pair_relation_alt_alt W hW u a ha hTr hoT
  refine ⟨C, hC0, fun t J hR => ?_⟩
  obtain ⟨e₀, he₀, hAe⟩ := _root_.GlobalTheory.T.true_geometry_twist_quadratic_level_alt W hW u a ha hTr t J hR
  obtain ⟨p, q, hA, hB, ⟨c0, hc0, h0⟩, hstep, hD⟩ := _root_.GlobalTheory.T.true_geometry_row_pair_property_alt W hW u a ha hTr hoT t J hR
  set Af : ∀ j, J.Ch j → ℂ := fun j α => p j α * (J.A.chr (j + 1) (J.A.xr j (J.ι j α)) : ℂ) with hAf
  set Bf : ∀ j, J.Ch (j + 1) → ℂ := fun j γ => q j γ * ((J.A.chr (j + 1) (J.A.xr (j + 1) (J.ι (j + 1) γ)) : ℂ))⁻¹ with hBf
  let k : ℕ → ℂ := fun j => if h : j + 1 < B.R.m then (hstep j h).choose else 1
  have hk : ∀ j, ∃ n : ℕ, 0 < n ∧ k j ^ n = 1 := fun j => by
    by_cases h : j + 1 < B.R.m
    · simp only [k, dif_pos h]; exact (hstep j h).choose_spec.1
    · simp only [k, dif_neg h]; exact ⟨1, one_pos, by simp⟩
  let cc : ℕ → ℂ := fun j => c0 * ∏ i ∈ Finset.range j, k i
  have hcc : ∀ j, ∃ n : ℕ, 0 < n ∧ cc j ^ n = 1 := fun j =>
    datRoot_mul hc0 (datRoot_prod _ _ fun i _ => hk i)
  let s : ∀ j, J.Ch j → ℂ := chartRescale B.R.m cc Bf
  have hs0 : ∀ α, s 0 α = 1 := fun _ => rfl
  have hsS : ∀ j γ, j < B.R.m → s (j + 1) γ = cc j * Bf j γ := fun j γ h => by
    show (if j < B.R.m then cc j * Bf j γ else 1) = _
    rw [if_pos h]
  have hsA : ∀ j, j < B.R.m → ∀ α, s j α * Af j α = cc j := by
    intro j
    induction j with
    | zero => intro _ α; rw [hs0, one_mul]; simp [cc, Af, h0 α]
    | succ j ih =>
      intro hj γ
      rw [hsS j γ (by omega)]
      have hk' : k j = (hstep j hj).choose := by simp only [k, dif_pos hj]
      have := (hstep j hj).choose_spec.2 γ
      calc cc j * Bf j γ * Af (j + 1) γ = cc j * (Bf j γ * Af (j + 1) γ) := by ring
        _ = cc j * k j := by rw [hk', ← this]
        _ = cc (j + 1) := by simp only [cc, Finset.prod_range_succ]; ring
  have hsroot : ∀ j α, ∃ n : ℕ, 0 < n ∧ s j α ^ n = 1 := by
    intro j
    cases j with
    | zero => intro α; exact ⟨1, one_pos, by rw [hs0, one_pow]⟩
    | succ j =>
      intro γ
      by_cases h : j < B.R.m
      · rw [hsS j γ h]; exact datRoot_mul (hcc j) (hB j h γ)
      · refine ⟨1, one_pos, ?_⟩
        show (if j < B.R.m then cc j * Bf j γ else 1) ^ 1 = 1
        rw [if_neg h, one_pow]
  refine ⟨s, fun j α γ => s j α * (s (j + 1) γ)⁻¹ * (p j α * q j γ), fun _ => 1, hsroot, hs0,
    fun _ => ⟨1, one_pos, one_pow 1⟩, fun j hj α γ => ⟨?_, ?_⟩⟩
  · have h1 := hD e₀ he₀ j hj α γ _ _ (hC t J hR e₀ he₀ j hj α γ)
    have h2 := isRatDatum_const_mul h1 (s j α * (s (j + 1) γ)⁻¹ * J.wt j α)
    rw [← hAe] at h2
    have hdQ : J.dQ s j α γ = (s j α * (s (j + 1) γ)⁻¹ * J.wt j α) • aconv (List.ofFn fun i => (J.E i).dL j (α i) (γ i)) := by
      simp only [_root_.GlobalTheory.Fam.QuadraticExtensionData.dQ, smul_smul]
    rw [hdQ, comb_smul_coef]
    convert h2 using 2
    rename_i z
    beta_reduce
    rw [_root_.GlobalTheory.T.true_geometry_twist_quadratic_value_alt W hW u a ha hTr t J hR j hj α γ z]
    ring
  · have hjm : j < B.R.m := by omega
    have hSA := hsA j hjm α
    have hBn : Bf j γ ≠ 0 := datRoot_ne_zero (hB j hjm γ)
    have hcn : cc j ≠ 0 := datRoot_ne_zero (hcc j)
    beta_reduce
    rw [hsS j γ hjm]
    have hx : ((J.A.chr (j + 1) (J.A.xr (j + 1) (J.ι (j + 1) γ)) : ℂ)) ≠ 0 := by
      exact Circle.coe_ne_zero _
    calc s j α * (cc j * Bf j γ)⁻¹ * (p j α * q j γ) * (J.A.chr (j + 1) (J.A.xr j (J.ι j α)) : ℂ) *
          ((J.A.chr (j + 1) (J.A.xr (j + 1) (J.ι (j + 1) γ)) : ℂ))⁻¹
        = (s j α * Af j α) * Bf j γ * (cc j * Bf j γ)⁻¹ := by simp only [hAf, hBf]; ring
      _ = 1 := by rw [hSA]; exact mul_inv_cancel₀ (mul_ne_zero hcn hBn)
end GlobalTheory.Fam
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_row_pair_relation_alt_alt_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∃ C : ℕ → ℂ, (∀ j, j < B.R.m → C j ≠ 0) ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∃ s ζ ρ, J.Dat C s ζ ρ := by
  atlas_forward_decl _root_.GlobalTheory.Fam.QuadraticExtensionData.dat_exists
end
end
