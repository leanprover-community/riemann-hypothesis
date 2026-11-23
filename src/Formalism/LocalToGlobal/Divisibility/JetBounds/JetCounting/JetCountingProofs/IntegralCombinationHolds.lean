module

public import Formalism.LocalToGlobal.Divisibility.JetBounds.JetCounting.PlaceSeriesJetsOneLetterOrbits
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CmAll
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SingleLetterBiextensionRelation
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.FinalFree
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OneLetterGaussSharpTranslateHolds
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OneLetterGaussTranslateOfCmCase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open scoped BigOperators

noncomputable section

namespace Formalism.L2.DIV.C

open Formalism.L2.DIV Formalism.DworkPowerSeriesWeights
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension cm4)
open Formalism.L2.Th1.Top (kappa_integral ltNormExists uniformGaussModels_fact_variant frameExistsH)

theorem integralFree_holds : HostIntFree := by
  intro a₀ b₀ c₀ dK ha hdK hOK l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨hsq, hmod, hcm⟩ := Formalism.L2.Th1.Top.HAux.data ha hdK hOK
  obtain ⟨s2, hs2, ⟨c, hc, e2, e3, es⟩, hN⟩ := Formalism.L2.Th1.D.nrcmOfCM4 cm4 dK (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK)
    hsq hmod hcm l h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨lam, hlam, hLT⟩ := ltNormExists l _ ι g2 g3 s2 ε c hc hε e2 e3 es
  refine ⟨s2, lam, hlam, hs2, hLT, fun σ F hσ hF => ⟨h5, hg.2.2.1, hg.2.2.2.1, hε, hth, hσ, hF, hN σ hσ, hg.2.2.2.2.1⟩, ?_⟩
  intro n _ _ h Λ g₀ hLat
  obtain ⟨κ, k1, k2, k3, hθ⟩ := uniformGaussModels_fact_variant a₀ b₀ c₀ dK ha hdK lam hlam hOK n h Λ g₀ hLat
  refine ⟨κ, k1, k2, k3, fun θ hθm hten => ?_⟩
  obtain ⟨g₁, i1, i2, hK1⟩ := hθ θ hθm hten l h5 ι
  refine ⟨g₁, i1, i2, fun σ hσ => frameExistsH a₀ b₀ c₀ dK ha hdK lam hlam hOK l h5 hd hin ι σ hσ n h Λ g₀ g₁
    hLat i1 i2, ?_⟩
  intro t N hN0 hlN ht σ hσ hFe γ B' hFr
  obtain ⟨F, hF⟩ := hFe
  exact kappa_integral l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) n _ γ hFr.1
    (hK1 g2 g3 ε s2 hLT hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1 hε hth t N hN0 hlN ht σ γ B' hFr)

end Formalism.L2.DIV.C
