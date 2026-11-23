module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubquotSmIndCongr
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivOfSameSatakeParameters
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasSatakeOfIsSatVecGL
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.UnramB
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SatSplitAt

theorem satSplit : PositivityTheory.Rg.BcB.F.RS.SatSplit := by
  rintro E _ _ _ n π D w B ⟨σ, hc, hs⟩ ⟨b, hb, rfl⟩
  obtain ⟨P, hsub, -, hsat⟩ := GlobalTheory.PfBCI.unram_component D.h w (D.σ · w) b hb
  obtain ⟨α, hα, hσ⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ _).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hs⟩)
  obtain ⟨y, hy⟩ := hsat.exists_vec
  have hP : GlobalTheory.SmGL.HasSatake P.ρ α :=
    GlobalTheory.CompanionTheory.SatComp.hasSatake_of_isSatVecGL ⟨P.smooth, P.irred⟩ α (hα ▸ hy)
  obtain ⟨e⟩ := GlobalTheory.SmGL.SphUniq.equiv_of_parInd _ _ hP.1 hσ.1 hP.2.2 hσ.2.2 hP.2.1 hσ.2.1
  exact ⟨σ, (GlobalTheory.SmGL.IsSubquotient.of_surjective e.toIntertwiningMap e.toLinearEquiv.surjective).trans hsub, hc⟩

end GlobalTheory.CompanionTheory.SatSplitAt

end
