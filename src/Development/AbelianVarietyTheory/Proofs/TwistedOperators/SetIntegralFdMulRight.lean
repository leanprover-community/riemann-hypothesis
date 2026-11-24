module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

namespace GlobalTheory.RowReal

theorem setIntegral_fd_mul_right : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {X : Node} (M : Vol G)
    {K : Subgroup (GL (Fin (G.V X).rank) (Formalism.IndefR.Lev.EAf D))}, M.IsAt X K → ∀ (k : GA D (G.V X)),
    MeasurePreserving (fun g : GA D (G.V X) => g * k) (M.ν X) (M.ν X) → Measurable (fun g : GA D (G.V X) => g * k⁻¹) →
    ∀ φ : GA D (G.V X) → ℂ, (∀ γ ∈ GQ (G.V X), ∀ g, φ (γ * g) = φ g) →
    ∫ g in M.fd X, φ (g * k) ∂M.ν X = ∫ g in M.fd X, φ g ∂M.ν X := by
  intro D T L sc G X M K hM k hk hk' φ hφ
  obtain ⟨hH, hF⟩ := hM.haar_fund
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig (G.V X).gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig (G.V X).gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig (G.V X).gram
  haveI : Countable (GQ (G.V X)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (G.V X).gram
  haveI := hH
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ (G.V X))
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ (G.V X)) (M.ν X)

  let e : GA D (G.V X) ≃ᵐ GA D (G.V X) :=
    { toFun := fun g => g * k, invFun := fun g => g * k⁻¹,
      left_inv := fun g => by simp, right_inv := fun g => by simp,
      measurable_toFun := hk.measurable, measurable_invFun := hk' }

  have hF' : IsFundamentalDomain (GQ (G.V X)) ((fun g : GA D (G.V X) => g * k) ⁻¹' M.fd X) (M.ν X) :=
    hF.preimage_of_equiv hk.quasiMeasurePreserving (e := id) Function.bijective_id
      (fun γ x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc])
  rw [hF.setIntegral_eq hF' (f := fun g => φ (g * k)) (fun γ x => by
      simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc]; exact hφ γ γ.2 _)]
  exact hk.setIntegral_preimage_emb e.measurableEmbedding φ (M.fd X)

end GlobalTheory.RowReal
