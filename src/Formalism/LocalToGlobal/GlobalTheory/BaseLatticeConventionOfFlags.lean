import Formalism.SharpRestriction.GlobalSchurBounds.JointsL
import Formalism.LocalToGlobal.HermitianColumns.ClsNonempty

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.FrobeniusOrbits NumberField



def AdmBRest (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E) : Prop :=
  letI := D.host.cmStar
  ∀ i, i ≤ D.R.m →
    ∃ (co : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)) (L0 : SDLat D.host.E (D.R.N i)),
      (∀ x y, stdH D.host.E (D.R.N i) (co x) (co y) = (D.sp.X i).hT x y) ∧
      (∀ y, co y ∈ L0.1 ↔ y ∈ (D.sp.X i).L0) ∧
      ∀ c : (D.mem u).C.cls i, ∃ Ln : SDLat D.host.E (D.R.N i),
        (∀ y, co y ∈ Ln.1 ↔ ∃ a ∈ D.clsLat u i c, ∃ b ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X i).hT (D.clsLat u i c),
          y = a + D.host.conj (π : D.host.E) • b) ∧
        (QuotientGroup.mk (D.detCls u i c) : D.Dt ⧸ D.UO) = D.relDet (D.R.N i) L0 Ln


end Formalism.L2.GlobalTheoryTheory

end
