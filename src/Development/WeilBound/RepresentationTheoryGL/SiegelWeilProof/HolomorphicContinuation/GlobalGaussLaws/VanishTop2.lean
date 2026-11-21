import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.VanishTop
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GenCoreTop
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.NullIff
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.LcOf
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilThetaConvergence.WeilThetaConvergenceOfSiegelSet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.StrongEisensteinBounds.Strong
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaAutomorphicOfConvergenceStatement

section
namespace PositivityTheory.Rg.Sw.Glob

theorem wtc : GlobalTheory.Published.WeilThetaConvergence := GlobalTheory.CompanionTheory.WTC.weilThetaConvergence_of_core GlobalTheory.CompanionTheory.SiegelRed.siegelCore

end PositivityTheory.Rg.Sw.Glob
end

section
namespace PositivityTheory.Rg.Sw.Glob

theorem absThm : AbsThm := AbsSt.absThm_of lv (cyc_of fft) (lc_of fft) nullIff

theorem top2 (hLF : LocFact) (hAA : AwayAct) (hLi : LocInst) (hTA : PositivityTheory.PfSWUS.ThetaAuto) (hLC : LieComm)
    (hDO : DerivOne) (hId : GIdil) (hC : PositivityTheory.PfSWUS.CoefND) :
    ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n → 1 ≤ n →
      ∀ g, GlobalTheory.Cont.HolValueAt (PositivityTheory.PfSWUS.eis ω H Φ g) (GlobalTheory.StdUnn.s0 V n) (GlobalTheory.StdUnn.thetaInt ω ν Φ g) :=
  top absThm hLF hAA hLi hTA hLC hDO hId PositivityTheory.Rg.SwEis.Hd.eisStrong hC wtc

theorem top3 (hLF : LocFact) (hAA : AwayAct) (hLi : LocInst) (hLC : LieComm) (hDO : DerivOne) (hId : GIdil)
    (hC : PositivityTheory.PfSWUS.CoefND) :
    ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n → 1 ≤ n →
      ∀ g, GlobalTheory.Cont.HolValueAt (PositivityTheory.PfSWUS.eis ω H Φ g) (GlobalTheory.StdUnn.s0 V n) (GlobalTheory.StdUnn.thetaInt ω ν Φ g) :=
  top2 hLF hAA hLi (GlobalTheory.T.theta_automorphic_of_convergence wtc) hLC hDO hId hC

end PositivityTheory.Rg.Sw.Glob
end
