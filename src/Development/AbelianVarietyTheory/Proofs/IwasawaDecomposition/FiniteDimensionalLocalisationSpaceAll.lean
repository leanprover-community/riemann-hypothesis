import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Formalism.LocalToGlobal.NumberFieldFamilies.HeckeStd0Of

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.FinDimVProof

theorem finDimV_all : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂), FinDimV B := by
  intro R H what₂ B j w
  classical
  have hfin : (Formalism.L2.Fam.NPC.LatticeFinitenessFree.latJ (what₂ := what₂) j w).Finite :=
    Set.Finite.subset ((what₂.MtLat (what₂.muTw w) j).gen.finite_toSet.preimage
      ((Formalism.L2.Fam.NPC.LatticeFinitenessFree.jMt_injective (what₂.muTw w) j).injOn)) fun x hx => hx
  have hs := Formalism.L2.Fam.NPC.LatticeFinitenessFree.span_iV (B := B) j w
  exact Module.finite_def.2 ⟨(hfin.image (B.iV j w)).toFinset, by simpa using hs⟩

end GlobalTheory.FinDimVProof
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_localisation_space_all : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂), FinDimV B := by
  atlas_forward_decl GlobalTheory.FinDimVProof.finDimV_all
