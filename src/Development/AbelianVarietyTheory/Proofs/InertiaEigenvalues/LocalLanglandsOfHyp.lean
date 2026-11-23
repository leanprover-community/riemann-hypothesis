module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsTransportStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecOfRecLiteralStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglandsBridge

theorem localLanglandsGL_of_depthZero_zelevinsky_bernstein : LocalLanglandsExists → LocalConverseGL → DepthZeroCuspidalLL → DepthZeroInduction →
    BrauerDegreeZero → ChevalleyUnits → GlobalArtinReciprocity → LanglandsExhaustionGL → LanglandsMultisegments →
    StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → LocalLanglandsGL := by
  intro hEx hConv hDep hInd hBr hChev hArt hExh hMult hCos hZel hGeo hBZ
  have hRec := GlobalTheory.T.rec_of_rec_literal hDep hInd hExh hMult hCos hZel hGeo hBZ
  have hComp := GlobalTheory.T.local_langlands_transport hArt hChev hBr hEx hConv hExh hBZ
  refine ⟨?_, ?_⟩
  · intro E Ω _ _ _ _ _ A w h
    obtain ⟨rc, hrc⟩ := hEx E Ω A w h
    refine ⟨rc, hRec E Ω A w h rc hrc, ?_⟩
    intro rc' hrc'
    funext x
    obtain ⟨n, c⟩ := x
    have hC := hComp E Ω A w h E Ω A w h rc' rc hrc'.toLit hrc
      (RingEquiv.refl Ω) (RingHom.id E) (RingEquiv.refl _) (fun _ => Iff.rfl) (fun _ => rfl) continuous_id
      (fun _ => rfl) n c.rep c.rep (LinearEquiv.refl ℂ _) (fun g v => by
        have hg : GeneralLinearGroup.map (RingEquiv.refl (w.adicCompletion E)).toRingHom g = g :=
          Units.ext (Matrix.ext fun _ _ => rfl)
        rw [hg]; rfl)
    obtain ⟨b, b', hb, hb', hN, hρ⟩ := hC
    have hbb : WD.mk b = WD.mk b' := WD.sound ⟨LinearEquiv.refl ℂ _, fun σ v => by
      simp only [LinearEquiv.refl_apply]; rw [hρ σ σ (fun _ => rfl)], fun v => by
      simp only [LinearEquiv.refl_apply]; rw [hN]⟩
    have hx : (⟨n, c⟩ : IrrGL (k := w.adicCompletion E)) = cls c.rep := congrArg (Sigma.mk _) c.cl_rep.symm
    rw [hx, ← hb, ← hb', hbb]
  · intro E Ω _ _ _ _ _ A w h E' Ω' _ _ _ _ _ A' w' h' rc rc' hrc hrc'
    exact hComp E Ω A w h E' Ω' A' w' h' rc rc' hrc.toLit hrc'.toLit

end GlobalTheory.LocLanglandsBridge
