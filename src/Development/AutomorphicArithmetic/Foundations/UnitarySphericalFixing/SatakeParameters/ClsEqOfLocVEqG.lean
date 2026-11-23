module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import GroundTheory.LocalFields.PadicLogSeries
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.BernsteinZelevinsky.TopAdm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientPreservesSubquotient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassCuspidal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLaws
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf GlobalTheory.PRep GlobalTheory.LocGL GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.One.M

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem good_contra {n : ℕ} (π π' : IrrRep (GL (Fin n) k)) (e : Nonempty (π'.ρ.Equiv (contra π.ρ))) (hg : Good (cls π)) :
    Good (cls π') := by
  obtain ⟨s, h1, h2⟩ := hg
  obtain ⟨φ⟩ := e
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have h3 : HasSupport π.ρ s := h1.of_equiv (equivRep π).symm
  have hdual : HasSupport (contra π.ρ) (s.map Zc.dualCl) := by
    have hsm := h3.isSmooth
    obtain ⟨m, x, hs, hirr, hcusp, P, hsub⟩ := h3
    have hcs : IsCuspSupport (contra π.ρ) (fun a => (x a).1) (fun a => contra (x a).rep) := by
      refine ⟨GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis k n)
        (hA k n π.V π.ρ hsm hirr) hirr, fun a => ?_, P, ?_⟩
      · have hc := (GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp hA (x a)
          ⟨(hcusp a).1, (hcusp a).2.2⟩).1
        rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA, IrrGL.isCusp_of] at hc
        exact ⟨(hcusp a).1, GlobalTheory.CompanionTheory.ContraProd.contra_rep_isIrreducible hA (x a), hc.2⟩
      · have hsub' := GlobalTheory.CompanionTheory.ContraSub.main k n _ _ π.ρ
          (parInd P (piTensor fun a => (x a).rep)) hsm (isSmooth_parInd P _) hsub
        obtain ⟨E⟩ := GlobalTheory.CompanionTheory.ContraProd.parInd_equiv_contra
          (σ := piTensor fun a => contra (x a).rep) (ρ := piTensor fun a => (x a).rep) P
          (isSmooth_piTensor fun a => (x a).2.rep.smooth)
          (GlobalTheory.CompanionTheory.ContraProd.contra_piTensor_rep hA x)
        exact hsub'.trans (IsSubquotient.of_surjective E.toIntertwiningMap E.toLinearEquiv.surjective)
    rw [← hs, Multiset.map_map]
    simpa only [Function.comp_apply, GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA] using
      hasSupport_of_isCuspSupport hcs
  refine ⟨s.map Zc.dualCl, (hdual.of_equiv φ.symm).of_equiv (equivRep π'), fun y hy => ?_⟩
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
  have hc := h2 z hz
  rcases hc with h | ⟨⟨p, hp, i, hi⟩, _⟩
  · apply Or.inl
    rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA z]
    exact h
  · let : CharZero k := charZero_of_injective_ringHom (f := i.toRingHom) i.injective
    have hd : DualCl z (Zc.dualCl z) :=
      ⟨z.1, z.2.rep, ⟨_, contra z.rep, isSmooth_contra z.rep,
        GlobalTheory.CompanionTheory.ZcDual.isIrreducible_contra hA _ z.2.rep.smooth z.2.rep.irr⟩,
        congrArg (Sigma.mk z.1) z.2.cl_rep.symm,
        GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA z, ⟨.refl _⟩⟩
    exact ((clBasic k z).2.2.2.2.2.2 _ hd).2.2.2.1.mpr (h2 z hz)

end

end UpperTheory.One.M
