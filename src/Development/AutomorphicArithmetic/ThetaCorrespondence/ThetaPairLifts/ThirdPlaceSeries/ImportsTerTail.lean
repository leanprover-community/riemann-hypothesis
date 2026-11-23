module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DaAutRepSphAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfOfNodupAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalIntegrality
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SphRead
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.SphLoc
section Alg
variable {G V X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
end Alg
section Val
open ValuativeRel Filter Topology
variable {K K' : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']
end Val
section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
end
end GlobalTheory.SphLoc
end
section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem GlobalTheory.SphLoc.main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E) x,
    GlobalTheory.AutQuot.LocAt π s.w x → π.SphericalAtPlace s.v → (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 s.w) x).unr := by
  intro hL D π s x hx hs
  obtain ⟨s', σ, h, hσ, e⟩ := hx
  have hv : s'.v = s.v := HeightOneSpectrum.ext (by rw [← s'.w_under, ← s.w_under, h])
  have hsph := _root_.UpperTheory.One.M.Sph.isSph π s' σ hσ (hv ▸ hs)
  have hu := (_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_unramified_iff_spherical (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 s'.w)) σ).2 hsph
  have key : ∀ (u u' : HeightOneSpectrum (𝓞 D.host.E)) (_ : u = u') (a : GlobalTheory.LocGL.IrrGL (k := u.adicCompletion D.host.E))
      (b : GlobalTheory.LocGL.IrrGL (k := u'.adicCompletion D.host.E)), HEq a b →
      (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 u) a).unr → (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 u') b).unr := by
    intro u u' hu a b hab
    subst hu
    cases eq_of_heq hab
    exact id
  exact key _ _ h _ _ e hu
end
end
