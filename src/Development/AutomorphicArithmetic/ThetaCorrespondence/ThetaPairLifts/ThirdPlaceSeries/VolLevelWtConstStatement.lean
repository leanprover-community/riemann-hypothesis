import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryExistsVolumeDataStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryExistsVolumeData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryExistsVolumeConstantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryExistsVolumeConstant
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLevelSphericalStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLevelSpherical
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemLevSph
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometrySubspacePropertyStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometrySubspaceProperty
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainIdentity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainBoundStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainBound
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QjPlaceNeLev
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainRelationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainRelation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacesInjectiveStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.VolLevMulWtMidStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PenVolStatement

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl
noncomputable section
namespace GlobalTheory.TopVol
theorem levSph_bT_compact_open_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → _root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT ≤ GfC _ ∧ IsCompact (_root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT : Set (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) ∧ IsOpen (((_root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT).subgroupOf (GfC _) : Subgroup (GfC (I.rec7 l Z).sp.X')) : Set (GfC (I.rec7 l Z).sp.X')) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a ha _
  have hx : a.g.bT ∈ GfC (I.rec7 l Z).sp.X' := ha.top.2.1
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA (I.rec7 l Z).sp.cm.sig (I.rec7 l Z).sp.X'.gram
  have hmem : ∀ h, h ∈ _root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT ↔
      a.g.bT⁻¹ * h * a.g.bT ∈ Formalism.IndefR.Lev.levG _ (_root_.GlobalTheory.Fam.pk_z W).βX (_root_.GlobalTheory.TopVol.datSph_alt W) := fun h => _root_.GlobalTheory.TopVol.mem_level_sphere_iff_conj_mem_levS h
  refine ⟨?_, ?_, ?_⟩
  · intro h hh
    have h1 : a.g.bT⁻¹ * h * a.g.bT ∈ GfC (I.rec7 l Z).sp.X' := ((hmem h).1 hh).1
    have h2 : h = a.g.bT * (a.g.bT⁻¹ * h * a.g.bT) * a.g.bT⁻¹ := by group
    rw [h2]
    exact mul_mem (mul_mem hx h1) (inv_mem hx)
  · have he : (_root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT : Set (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) =
        (fun k => a.g.bT * k * a.g.bT⁻¹) '' (Formalism.IndefR.Lev.levG _ (_root_.GlobalTheory.Fam.pk_z W).βX (_root_.GlobalTheory.TopVol.datSph_alt W) : Set _) := by
      ext h
      constructor
      · intro hh
        exact ⟨_, (hmem h).1 hh, by group⟩
      · rintro ⟨k, hk, rfl⟩
        refine (hmem _).2 ?_
        have : a.g.bT⁻¹ * (a.g.bT * k * a.g.bT⁻¹) * a.g.bT = k := by group
        rw [this]; exact hk
    rw [he]
    exact (GlobalTheory.ParahoricCompact.isCompact_levG _ _ _).image (by fun_prop)
  · have ho := GlobalTheory.ParahoricCompact.isOpen_comap_lev _ (_root_.GlobalTheory.Fam.pk_z W).βX (_root_.GlobalTheory.TopVol.datSph_alt W)
    have hc : Continuous fun k : GfC (I.rec7 l Z).sp.X' => a.g.bT⁻¹ * (k : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') * a.g.bT := by
      fun_prop
    convert ho.preimage hc using 1
    ext k
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage]
    rw [hmem]
    constructor
    · intro hk; exact hk.2
    · intro hk
      exact ⟨(GfC (I.rec7 l Z).sp.X').mul_mem ((GfC (I.rec7 l Z).sp.X').mul_mem ((GfC (I.rec7 l Z).sp.X').inv_mem hx) k.2) hx, hk⟩
end GlobalTheory.TopVol
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
open GlobalTheory.TopVol GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_level_spherical_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → _root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT ≤ GfC _ ∧ IsCompact (_root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT : Set (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) ∧ IsOpen (((_root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT).subgroupOf (GfC _) : Subgroup (GfC (I.rec7 l Z).sp.X')) : Set (GfC (I.rec7 l Z).sp.X')) := by
  atlas_forward_decl _root_.GlobalTheory.TopVol.levSph_bT_compact_open_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl
noncomputable section
namespace GlobalTheory.TopVol
theorem volLev_top_ne_zero_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ U : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X'), U ≤ GfC _ → IsCompact (U : Set (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) → IsOpen ((U.subgroupOf (GfC _) : Subgroup (GfC (I.rec7 l Z).sp.X')) : Set (GfC (I.rec7 l Z).sp.X')) → volLev a.g.volT U ≠ 0 := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a _ _ U hle hc ho
  exact volLev_ne_zero_of_isCompact _
    (Formalism.IndefR.Eqv.isCompact_GinfC (I.rec7 l Z).sp.X'_sig fun τ => Or.inl ((I.rec7 l Z).X'_posDef τ)) _ U hle hc ho
end GlobalTheory.TopVol
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
open GlobalTheory.TopVol GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_subspace_property_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ U : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X'), U ≤ GfC _ → IsCompact (U : Set (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) → IsOpen ((U.subgroupOf (GfC _) : Subgroup (GfC (I.rec7 l Z).sp.X')) : Set (GfC (I.rec7 l Z).sp.X')) → volLev a.g.volT U ≠ 0 := by
  atlas_forward_decl _root_.GlobalTheory.TopVol.volLev_top_ne_zero_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl
noncomputable section
namespace GlobalTheory.TopAgree
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.TopAgree
namespace GlobalTheory.TopAgree
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.TopAgree
namespace GlobalTheory.TopAgree
set_option maxHeartbeats 1000000 in
theorem main_alt_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (t : W.P.T) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ g, g ∈ _root_.GlobalTheory.TopVol.twistedLevelSubgroup W a.g.bT t ↔ g ∈ _root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT ∧ ∀ i x, (mt (I.rec7 l Z).sp.X' g).map (J.G i).q.pr = (J.G i).FT.β * Units.val x * (J.G i).FT.γ → x ∈ ((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).levTop.J := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a _ _ t J hJ g
  refine (_root_.GlobalTheory.TopVol.mem_level_twist_iff_conj_mem_levS_datXP g).trans ((levS_split _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t) (_root_.GlobalTheory.TopVol.datSph_alt W).xq _).trans
    ((and_congr_right fun hS => ?_).trans (and_congr_left fun _ => (_root_.GlobalTheory.TopVol.mem_level_sphere_iff_conj_mem_levS g).symm)))
  have key := fun i => red_iff_levTop (J.G i) (J.E i).δ (J.E i).tame (J.E i).η g (parLev_St hS.2.1)
  constructor
  · exact fun h i => (key i).1 (h _ (J.mem i))
  · intro h PP hP
    obtain ⟨i, rfl⟩ := hJ.surj PP hP
    exact (key i).2 (h i)
end GlobalTheory.TopAgree
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
open GlobalTheory.TopVol GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_twist_chain_identity_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (t : W.P.T) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ g, g ∈ _root_.GlobalTheory.TopVol.twistedLevelSubgroup W a.g.bT t ↔ g ∈ _root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT ∧ ∀ i x, (mt (I.rec7 l Z).sp.X' g).map (J.G i).q.pr = (J.G i).FT.β * Units.val x * (J.G i).FT.γ → x ∈ ((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).levTop.J := by
  atlas_forward_decl _root_.GlobalTheory.TopAgree.main_alt_alt
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
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem qj_place_ne_lev_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (i : Fin J.r) (P : HeightOneSpectrum (𝓞 B.fields.E)), P ∈ (B.primes X).vT u ∨ P ∈ (B.primes X).vGs → (J.G i).q.v ≠ P.under (𝓞 B.host.F) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha t J hJ i P hP
  have hv : (J.G i).q.v = (J.pl i).under (𝓞 (I.rec7 l Z).host.F) := by
    obtain ⟨ε, hε, hs⟩ := (J.G i).q.above
    exact (GlobalTheory.IdemUnder.under_eq_of_isIdemAt _ _ _ _ ε (J.G i).idem hε hs).symm
  have hQ : J.pl i ∈ I.SQ := I.Q_subset_SQ _ ((hW.tq.Q t (J.pl i)).1 (J.mem i))
  have hok : I.Ok := hW.tr.ok
  have key : ∀ PP : HeightOneSpectrum (𝓞 B.host.E), PP ∈ I.SQ → PP.under (𝓞 B.host.F) ≠ P.under (𝓞 B.host.F) := by
    intro PP hPP e
    apply (GlobalTheory.Mem.LevTwist.good_of_mem hok hPP).2.2.2
    rw [e]
    rcases hP with hP | hP
    · have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
      rw [(GlobalTheory.Mem.ReadTwist.plc_under_eq_iff (F := B.host.F) P (hPr.T_prime u)).2 (T_mem_vT hPr u ⟨P, hP⟩)]
      exact hok.T_mem u
    · exact GlobalTheory.Mem.LevTwist.plc_mem hok hP
  rw [hv]
  exact key (J.pl i) hQ
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
open GlobalTheory.TopVol GlobalTheory.FinPl
namespace GlobalTheory.TopVol.InKConj
variable {D : D7}
end GlobalTheory.TopVol.InKConj
namespace GlobalTheory.TopVol.InKConj
theorem inK_mem_levSph_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (t : W.P.T) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ κ, InK (I.rec7 l Z).sp.X' a.v.NT (fun p => ∃ i, (J.G i).q.v = p) κ → κ ∈ _root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat t J hJ κ hκ
  have hsd := W.Q.charW.base.lev.βX
  let row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t := fun t =>
    { vP := fun _ _ => 0, vT := fun _ _ _ => 0
      sBF := fun j ρ h => (GlobalTheory.Unf.Inhab.nonempty_stepBF W.Q.stdChar _ _).some
      sFB := fun j σ h => (GlobalTheory.Unf.Inhab.nonempty_stepFB W.Q.stdChar _ _).some
      io := fun _ => 0, ioT := fun _ _ => 0 }
  let col := fun t : W.P.T => (GlobalTheory.Fam.Check.colCh_nonempty (D := I.rec7 l Z) (u := u) ((I.rec7 l Z).chTw u (W.P.I.tup t))).choose
  have tie := (ha.tie row col).1
  have hNT : a.v.NT = a.g.LT := tie.bT.2
  have hm : ∀ v, (fun p => ∃ i, (J.G i).q.v = p) v → Moves _ a.g.bT (_root_.GlobalTheory.Fam.pk_z W).ΛX a.v.NT (· = v) := fun v _ => by
    rw [hNT]; exact tie.movesT _
  rw [_root_.GlobalTheory.TopVol.mem_level_sphere_iff_conj_mem_levS]
  exact conj_mem_levG _ (_root_.GlobalTheory.Fam.pk_z W).βX (_root_.GlobalTheory.Fam.pk_z W).ΛX a.v.NT (_root_.GlobalTheory.TopVol.datSph_alt W) _ a.g.bT κ (hsd.elim fun _ h => h.1)
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame _ _ _ _ _ hsd) ha.top.2.1 hm rfl
    (fun PP hP ⟨i, hi⟩ => _root_.GlobalTheory.Fam.qj_place_ne_lev_alt W hW u a ha t J hJ i PP (Or.inr ((hW.lev.2.1 PP).1 hP)) hi) hκ
end GlobalTheory.TopVol.InKConj
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_levSph_of_inK_of_quadraticExtensionData : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (t : W.P.T) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ κ, InK (I.rec7 l Z).sp.X' a.v.NT (fun p => ∃ i, (J.G i).q.v = p) κ → κ ∈ _root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT := by
  atlas_forward_decl _root_.GlobalTheory.TopVol.InKConj.inK_mem_levSph_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl
noncomputable section
namespace GlobalTheory.TopVol.MovesAt
open GlobalTheory.FinPl ValuativeRel
set_option maxHeartbeats 1000000 in
theorem main_alt_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (t : W.P.T) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ g ∈ _root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT, Moves (I.rec7 l Z).sp.X' g a.v.NT a.v.NT (fun p => ∃ i, (J.G i).q.v = p) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a ha _ t J _ g hg
  have hg' := (_root_.GlobalTheory.TopVol.mem_level_sphere_iff_conj_mem_levS g).1 hg
  have hSt : Lev.finE (I.rec7 l Z).sp.X' (a.g.bT⁻¹ * g * a.g.bT) ∈ Formalism.L2.DIV.St (_root_.GlobalTheory.Fam.pk_z W).βX :=
    Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hg'.2)
  classical
  have hP : (fun p => ∃ i, (J.G i).q.v = p) = (· ∈ Finset.univ.image (fun i => (J.G i).q.v)) := by
    funext p; simp
  rw [hP]
  refine GlobalTheory.T.carriesLatticeCompletion_of_each_place _ _ _ _ _ fun v hv => ?_
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
  obtain ⟨e, -, hM⟩ := (J.G i).frameTop
  exact GlobalTheory.T.splitPlace_conjugate_stabilizer_keeps_movedFrameLattice (J.G i).q (J.G i).idem _ _ ha.vis.sdT (J.G i).FT (J.G i).latT _ _ e hM g hSt
end GlobalTheory.TopVol.MovesAt
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
open GlobalTheory.TopVol GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_twist_chain_relation_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (t : W.P.T) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ g ∈ _root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT, Moves (I.rec7 l Z).sp.X' g a.v.NT a.v.NT (fun p => ∃ i, (J.G i).q.v = p) := by
  atlas_forward_decl _root_.GlobalTheory.TopVol.MovesAt.main_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl
noncomputable section
theorem GlobalTheory.TopVol.main_alt_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∃ VT : ℂ, VT ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → J.VolT VT := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT
  obtain ⟨hle, hc, ho⟩ := _root_.GlobalTheory.T.true_geometry_level_spherical_alt W hW u a ha haT
  have hv := _root_.GlobalTheory.T.true_geometry_subspace_property_alt W hW u a ha haT _ hle hc ho
  refine ⟨(volLev a.g.volT (_root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT) : ℂ), Complex.ofReal_ne_zero.2 hv, fun t J hJ => ?_⟩
  have hA := _root_.GlobalTheory.T.true_geometry_twist_chain_identity_alt W hW u a ha haT t J hJ
  have hK := _root_.GlobalTheory.T.mem_levSph_of_inK_of_quadraticExtensionData W hW u a ha haT t J hJ
  have hM := _root_.GlobalTheory.T.true_geometry_twist_chain_relation_alt W hW u a ha haT t J hJ
  have hinj := _root_.GlobalTheory.T.injective_q_v_of_reads W hW u a ha haT t J hJ
  set S := (I.rec7 l Z).sp.X'
  set U := _root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT
  set U' := _root_.GlobalTheory.TopVol.twistedLevelSubgroup W a.g.bT t
  let Jf : (i : Fin J.r) → Subgroup (GL _ (J.G i).k) := fun i => ((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).levTop.J
  let φ : GA (I.rec7 l Z) S →* ((i : Fin J.r) → GL _ (J.G i).k) :=
    MonoidHom.pi fun i => GlobalTheory.LevIdx.locHom (J.G i).q S (J.G i).FT
  have hφi : ∀ g i, φ g i = GlobalTheory.LevIdx.locHom (J.G i).q S (J.G i).FT g := fun _ _ => rfl
  have hU'' : ∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i, φ g i ∈ Jf i := by
    intro g
    rw [hA g]
    refine and_congr_right fun _ => forall_congr' fun i => ?_
    refine ⟨fun h => h _ ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).2 rfl), fun h x hx => ?_⟩
    rw [(GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).1 hx]; exact h
  have hle' : U' ≤ U := fun g hg => ((hU'' g).1 hg).1
  have hidx : U'.relIndex U = ∏ i, (Jf i).relIndex (GlobalTheory.SplitWeil.KO (J.G i).k _) := by
    refine GlobalTheory.T.relIndex_eq_prod_relIndex_of_surjective_pi φ U U' (fun i => GlobalTheory.SplitWeil.KO (J.G i).k _) Jf (fun i => (J.E i).leT) ?_ ?_ hU''
    · intro g hg i
      exact GlobalTheory.T.mem_integralGL_split_place_of_carries_latticeCompletion (J.G i).q S (J.G i).FT a.v.NT _ ⟨i, rfl⟩ (J.G i).latT g (hM g hg) _
        ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).2 rfl)
    · intro x hx
      obtain ⟨g, hg, hgx⟩ := GlobalTheory.T.exists_selfDual_stabilizer_with_prescribed_splitPlace_matrices S a.v.NT ha.vis.sdT (fun i => (J.G i).k) (fun i => (J.G i).q) _
        (fun i => (J.G i).FT) hinj (fun i => (J.G i).latT) x hx
      refine ⟨g, hK g hg, funext fun i => ?_⟩
      rw [hφi]; exact ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).1 (hgx i)).symm
  have hU'o : IsOpen ((U'.subgroupOf (GfC S) : Subgroup (GfC S)) : Set (GfC S)) := by
    have e : ((U'.subgroupOf (GfC S) : Subgroup (GfC S)) : Set (GfC S)) =
        ((U.subgroupOf (GfC S) : Subgroup (GfC S)) : Set (GfC S)) ∩
          ⋂ i, (fun g : GfC S => GlobalTheory.LevIdx.locHom (J.G i).q S (J.G i).FT g.1) ⁻¹' (Jf i : Set (GL _ (J.G i).k)) := by
      ext g
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
      rw [hU'']
      rfl
    rw [e]
    exact ho.inter (isOpen_iInter_of_finite fun i =>
      ((J.E i).openT).preimage ((GlobalTheory.LevIdx.continuous_locHom (J.G i).q S (J.G i).FT).comp continuous_subtype_val))
  have hvol := GlobalTheory.T.archimedeanLevelVolume_mul_relIndex (I.rec7 l Z) S a.g.volT U' U hle' hle hc hU'o
  refine ⟨U', fun h => _root_.GlobalTheory.TopVol.mem_level_twist_iff_conj_mem_levS_datXP h, fun β => ?_⟩
  have hw : ∀ i, (J.E i).wt B.R.m (β i) = (((Jf i).relIndex (GlobalTheory.SplitWeil.KO (J.G i).k _) : ℕ) : ℂ) := by
    intro i
    have key : ∀ j (e : (J.G i).s + 1 + 1 = j) (y : (J.E i).Ch j), (J.E i).wt j y = ((J.E i).idx j : ℂ) := by
      rintro j rfl y; exact (J.E i).wt_top y
    have e2 : (J.E i).wt B.R.m (β i) = ((J.E i).idx B.R.m : ℂ) := key _ (J.G i).hs (β i)
    have e3 : (J.E i).idx B.R.m = (J.E i).idx ((J.G i).s + 1 + 1) := congrArg (J.E i).idx (J.G i).hs.symm
    rw [e2, e3, (J.E i).idx_top]
  rw [← hvol, _root_.GlobalTheory.Fam.QuadraticExtensionData.wt]
  simp only [hw]
  rw [hidx]
  push_cast
  ring
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
theorem _root_.GlobalTheory.T.exists_volume_constant_of_true_geometry : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∃ VT : ℂ, VT ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → J.VolT VT := by
  atlas_forward_decl _root_.GlobalTheory.TopVol.main_alt_alt
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
theorem vol_level_wt_const_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∃ (V : ℕ → ℂ) (VT : ℂ), (∀ j, j < B.R.m → V j ≠ 0) ∧ VT ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → J.Vol V ∧ J.VolT VT := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT
  obtain ⟨VT, hVT, hT3⟩ := _root_.GlobalTheory.T.exists_volume_constant_of_true_geometry W hW u a ha haT
  refine ⟨fun j => if h : j + 2 ≤ B.R.m then Classical.choose (_root_.GlobalTheory.T.true_geometry_chain_step_identity_alt W hW u a ha haT j h)
    else if h' : j + 1 = B.R.m then Classical.choose (_root_.GlobalTheory.T.true_geometry_chain_step_value_alt W hW u a ha haT j h') else 1, VT, ?_, hVT, ?_⟩
  · intro j hj
    by_cases h : j + 2 ≤ B.R.m
    · simp only [dif_pos h]; exact (Classical.choose_spec (_root_.GlobalTheory.T.true_geometry_chain_step_identity_alt W hW u a ha haT j h)).1
    · have h' : j + 1 = B.R.m := by omega
      simp only [dif_neg h, dif_pos h']; exact (Classical.choose_spec (_root_.GlobalTheory.T.true_geometry_chain_step_value_alt W hW u a ha haT j h')).1
  · intro t J hJ
    refine ⟨?_, hT3 t J hJ⟩
    intro j hj α
    by_cases h : j + 2 ≤ B.R.m
    · simp only [dif_pos h]; exact (Classical.choose_spec (_root_.GlobalTheory.T.true_geometry_chain_step_identity_alt W hW u a ha haT j h)).2 t J hJ α
    · have h' : j + 1 = B.R.m := by omega
      simp only [dif_neg h, dif_pos h']; exact (Classical.choose_spec (_root_.GlobalTheory.T.true_geometry_chain_step_value_alt W hW u a ha haT j h')).2 t J hJ α
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
theorem _root_.GlobalTheory.T.true_geometry_exists_volume_data_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∃ (V : ℕ → ℂ) (VT : ℂ), (∀ j, j < B.R.m → V j ≠ 0) ∧ VT ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → J.Vol V ∧ J.VolT VT := by
  atlas_forward_decl _root_.GlobalTheory.Fam.vol_level_wt_const_alt
end
end
