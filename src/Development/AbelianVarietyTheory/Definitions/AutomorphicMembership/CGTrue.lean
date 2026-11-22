module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlocksUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

@[expose] public section

noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain

def wdCG {D : D7} (hE : IsEmpty D.nd.Loc) (K : CGK D.naut) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) :
    GlobalTheory.RowTie.WDTie (setCG D hE K).nd (setCG D hE K).naut := { T with }

def cfCG {D : D7} (hE : IsEmpty D.nd.Loc) (K : CGK D.naut) (c : CharFrame D) : CharFrame (setCG D hE K) :=
  ⟨c.P, c.W, c.mu0, c.eta, c.chiPsi, c.del, c.del', c.isMu0, c.isEta, c.isChi, c.isDel, c.isDel'⟩

end GlobalTheory.HeightCounting

end
