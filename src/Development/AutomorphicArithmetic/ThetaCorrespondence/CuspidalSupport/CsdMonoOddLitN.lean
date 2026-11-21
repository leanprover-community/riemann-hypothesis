import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.MemOfInduces
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CbcCOfCbcc
import Development.AutomorphicArithmetic.Foundations.Convolution.Cbcc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.SsMonoOdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfHyp

section
namespace UpperTheory.Lit.Car

theorem dualR_of_wbc (hW : PositivityTheory.Pf1.CLGD.K.WBC) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hGK : GlobalTheory.Published.GelfandKazhdanDual)
    (hP : GlobalTheory.Published.GaloisRepOfPolarizedPair) (hB : GlobalTheory.Published.DeRhamPotSemistable) (hL : GlobalTheory.Published.LocalLanglandsGL)
    (hJ : GlobalTheory.Published.JacquetShalikaRigidity) : DualR :=
  have hG := (bridge' hGK).2 hP
  ⟨lg_of (LocalGlobalAboveLAlt.local_global_compatibility_holds hW hG hB hL hJ) (LocalGlobalAboveLAlt.temperedness_transfer_holds hW hG hB hL hJ),
    csdSs_of hF hGK hG hB (LocalGlobalAboveLAlt.local_global_compatibility_holds hW hG hB hL hJ)⟩

theorem dualR_of_cbcc (hC : UpperTheory.V.Z.Bc.CBCc) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hGK : GlobalTheory.Published.GelfandKazhdanDual)
    (hP : GlobalTheory.Published.GaloisRepOfPolarizedPair) (hB : GlobalTheory.Published.DeRhamPotSemistable) (hL : GlobalTheory.Published.LocalLanglandsGL)
    (hJ : GlobalTheory.Published.JacquetShalikaRigidity) : DualR :=
  dualR_of_wbc (UpperTheory.V.Z.Bc.wbc_of_cbcc hC) hF hGK hP hB hL hJ

end UpperTheory.Lit.Car
end

section
namespace UpperTheory.Lit.Car

theorem dualR_closed (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hGK : GlobalTheory.Published.GelfandKazhdanDual)
    (hP : GlobalTheory.Published.GaloisRepOfPolarizedPair) (hB : GlobalTheory.Published.DeRhamPotSemistable) (hL : GlobalTheory.Published.LocalLanglandsGL)
    (hJ : GlobalTheory.Published.JacquetShalikaRigidity) : DualR :=
  dualR_of_cbcc UpperTheory.ConvolutionTheory.cbcc hF hGK hP hB hL hJ

end UpperTheory.Lit.Car
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.ContraPair
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open private UpperTheory.Lit.Car.regAlg_of_coh UpperTheory.Lit.Car.mem_of_induces from Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.MemOfInduces

namespace UpperTheory.Lit.Car

theorem csdMonoOdd_of (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hGK : GlobalTheory.Published.GelfandKazhdanDual)
    (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) (hB : GlobalTheory.Published.DeRhamPotSemistable) (h1 : LocalGlobalAboveLAlt.LocalGlobalSubnormal) :
    UpperTheory.V.Lev.CsdMonoOdd := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha _ π hd hcoh
  have hreg := UpperTheory.Lit.Car.regAlg_of_coh E a π hcoh
  have hc : π.IsCsd := GlobalTheory.CsdBack.isCsd_of_paired hF E a π (hGK E a π) hd
  obtain ⟨r, wt, HT, hr⟩ := hG.of_isCsd Ω ι (by omega) hreg hc
  refine ⟨r, hr.cont, hr.ss, hr.away, fun P AI hT w A h O _ _ _ Bw hj =>
    ⟨hT.elim fun T => hr.isPstAt hB T h Bw hj, fun σ hσ rc hrc => ?_⟩⟩
  exact (h1 E Ω l ι a ha π hc hreg r wt HT hr P AI hT w (UpperTheory.Lit.Car.mem_of_induces h Bw hj) A h O Bw hj σ hσ rc hrc).2.1.1

end UpperTheory.Lit.Car

end
end

section
namespace UpperTheory.Lit.Car

private theorem ll (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) : GlobalTheory.Published.LocalLanglandsGL :=
  GlobalTheory.LocLanglandsBridge.localLanglandsGL_of_depthZero_zelevinsky_bernstein hN.loc.llc hN.loc.conv hN.loc.dzc hN.loc.dzi hN.loc.brauer hN.loc.chev
    hN.aut.art hN.loc.exh hN.loc.multi hN.loc.cos hN.loc.zel hN.loc.geo hN.loc.bz

theorem csdSs_litN (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) : UpperTheory.V.Lev.CsdSs :=
  (dualR_closed hN.aut.fin hN.aut.gk hN.aut.gal hN.aut.berger (ll hN) hN.aut.js.1).2

theorem csdMonoOdd_litN (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) : UpperTheory.V.Lev.CsdMonoOdd :=
  have hG := (bridge' hN.aut.gk).2 hN.aut.gal
  csdMonoOdd_of hN.aut.fin hN.aut.gk hG hN.aut.berger
    (LocalGlobalAboveLAlt.local_global_compatibility_holds (UpperTheory.V.Z.Bc.wbc_of_cbcc UpperTheory.ConvolutionTheory.cbcc) hG hN.aut.berger (ll hN) hN.aut.js.1)

end UpperTheory.Lit.Car
end
